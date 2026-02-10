# Proof Graph Automation: Technical Design (v2)

*Design document for extracting **semantic** proof dependencies from Lean 4.*

**Issue:** #142
**Status:** Revised design - addressing semantic vs syntactic gap
**Revision:** v2 (2026-02-10)

---

## Problem Statement

### Original Problem

The current `src/viz/interactive/export_data.py` script requires manual curation of the dependency graph:

```python
DEPENDENCIES = {
    "expectation_x_measured_z_is_zero": [
        "expectation_orthogonal_is_zero",
        "spinXState_is_pure",
        "spinZObservable_is_pure",
        "x_z_orthogonal",
    ],
    # ... more manual entries
}
```

This manual process:
- Is error-prone (easy to miss dependencies)
- Doesn't scale with more experiments
- Can drift from actual Lean proof structure

### Critical Gap in v1 Design (Why It Was Rejected)

The original v1 design proposed using `Lean.Expr.getUsedConstants` to extract dependencies. This approach is **syntactically correct but semantically misleading**.

**The Problem:** `getUsedConstants` captures *symbol occurrence*, not *logical dependency*.

Consider our actual proofs:

```lean
-- Basic.lean (line 24)
theorem spin_x_is_pure : isPureQuaternion SPIN_X := rfl

-- Basic.lean (lines 58-60)
theorem expectation_orthogonal_is_zero (ψ O : Q)
    (_hψ : isPureQuaternion ψ) (_hO : isPureQuaternion O)
    (h_ortho : vecDot ψ O = 0) : expectationValue ψ O = 0 := by
  simp [expectationValue, vecPart]
  exact h_ortho
```

**What `getUsedConstants` would report:**
- `spin_x_is_pure`: `[isPureQuaternion, SPIN_X, Eq.refl]` (syntactic)
- `expectation_orthogonal_is_zero`: `[expectationValue, vecPart, simp, ...]` (what symbols appear)

**What we actually want:**
- `spin_x_is_pure`: What mathematical principle makes this true? (definitional equality)
- `expectation_orthogonal_is_zero`: What lemmas did `simp` actually use to simplify?

**Why this matters for James's understanding:**
The visualization must show *why* a proof works, not *what symbols it mentions*. If `simp` applies 5 Mathlib lemmas to reduce a goal, the user needs to see those 5 lemmas as dependencies, not just "simp was called."

---

## The Semantic vs Syntactic Gap

### Three Levels of Dependency

| Level | What it captures | Example |
|-------|------------------|---------|
| **Syntactic** | Symbol occurrence in source | `simp [expectationValue]` mentions `expectationValue` |
| **Proof Term** | Constants in compiled proof | `getUsedConstants` on elaborated term |
| **Semantic** | Logical principles actually used | Which simp lemmas fired? What did `rfl` unfold? |

The v1 design operated at the Proof Term level, which is better than Syntactic but still insufficient.

### Case Study: `rfl` Proofs

```lean
theorem spin_x_is_pure : isPureQuaternion SPIN_X := rfl
```

At the **proof term level**, this just shows `Eq.refl`. But the *semantic* truth is:
1. `SPIN_X` unfolds to `⟨0, 1, 0, 0⟩`
2. `isPureQuaternion` unfolds to `.re = 0`
3. `(⟨0, 1, 0, 0⟩ : Q).re` reduces to `0` by definitional equality
4. `0 = 0` is reflexivity

A semantically accurate graph would show this depends on the *definitions* of `SPIN_X` and `isPureQuaternion`, not just that `rfl` was used.

### Case Study: `simp` Tactics

```lean
theorem x_z_orthogonal : vecDot spinXState spinZObservable = 0 := by
  simp [vecDot, spinXState, spinZObservable, SPIN_X, SPIN_Z]
```

**Syntactic view:** Uses `vecDot`, `spinXState`, etc.
**Semantic view:** After unfolding those definitions, `simp` applies arithmetic lemmas from Mathlib to reduce `1*0 + 0*0 + 0*1` to `0`.

---

## Proposed Solution: Hybrid Extraction

Given the complexity of semantic extraction, we propose a **three-tier hybrid approach**:

### Tier 1: Automated Proof Term Analysis (Enhanced)

Use `getUsedConstants` but with **semantic augmentation**:

```lean
/-- Enhanced dependency extraction that distinguishes dependency types -/
structure DepInfo where
  name : Name
  kind : DepKind  -- direct_call | definition_unfold | type_constraint
  deriving Repr, BEq

inductive DepKind
  | direct_call      -- Explicitly invoked (e.g., `exact foo`)
  | definition_unfold -- Definition expanded during elaboration
  | type_constraint   -- Required by type signature
```

### Tier 2: Simp Lemma Tracing (Automated)

Lean 4 provides `Simp.UsedSimps` which tracks exactly which lemmas `simp` applied.

**Key API:** `Lean.Meta.Simp.State.usedTheorems`

```lean
import Lean.Meta.Tactic.Simp.Types

/-- Extract simp lemmas actually used during simplification -/
def getSimpDeps (state : Simp.State) : List Name :=
  state.usedTheorems.toList.map fun (origin, _count) =>
    match origin with
    | .decl name _ _ => name
    | .fvar fvarId => fvarId.name  -- local hypothesis
    | _ => `anonymous
```

**Implementation Strategy:**

Instead of post-hoc analysis, we create a **tracing tactic wrapper**:

```lean
/-- Wrapper that runs simp and records used lemmas -/
elab "traced_simp" args:Lean.Parser.Tactic.simpArgs : tactic => do
  -- Run simp normally
  let (result, state) ← Lean.Elab.Tactic.evalSimpCore ...
  -- Record used theorems to environment extension
  for (origin, _) in state.usedTheorems.toList do
    recordSimpDep (← getMainTarget).mvarId origin
  -- Apply result
  ...
```

**Challenge:** This requires modifying proof source to use `traced_simp` instead of `simp`.

**Alternative:** Use `simp?` during development, which outputs `simp only [...]` with the exact lemmas used, then commit that explicit form.

### Tier 3: Manual Semantic Annotation (Human-in-the-loop)

For cases where automated extraction fails or is misleading, maintain a curated override file:

```json
// proofs/QBP/Meta/semantic_overrides.json
{
  "spin_x_is_pure": {
    "semantic_deps": ["isPureQuaternion_def", "SPIN_X_def"],
    "note": "rfl proof - depends on definitional equality of these"
  },
  "x_z_orthogonal": {
    "semantic_deps": ["vecDot_def", "mul_zero", "add_zero", "zero_add"],
    "note": "simp reduces arithmetic to zero"
  }
}
```

---

## Technical Design (Revised)

### Architecture

```
proofs/QBP/
├── Basic.lean
├── Experiments/
│   └── SternGerlach.lean
└── Meta/
    ├── ExportGraph.lean       ← Proof term extraction
    ├── SimpTrace.lean         ← Simp lemma tracing infrastructure
    └── semantic_overrides.json ← Manual semantic annotations
```

### Lean 4 APIs for Semantic Extraction

```lean
-- Core proof term analysis (from v1, still useful as baseline)
Lean.Environment.constants
Lean.ConstantInfo.type
Lean.ConstantInfo.value?
Lean.Expr.getUsedConstants

-- NEW: Simp lemma tracking
Lean.Meta.Simp.State              -- Contains usedTheorems field
Lean.Meta.Simp.UsedSimps          -- Map from origin to usage count
Lean.Meta.Simp.Origin             -- .decl, .fvar, .stx, .other

-- NEW: InfoTree for elaboration details
Lean.Elab.InfoTree                -- Tree of elaboration info
Lean.Elab.Info.TermInfo           -- Contains expr, lctx, expectedType?
Lean.Elab.Info.TacticInfo         -- Contains goalsBefore/After, mctx

-- NEW: Trace options for debugging
set_option trace.Meta.Tactic.simp true
set_option trace.Meta.Tactic.simp.rewrite true
```

### Implementation Outline (Revised)

```lean
-- proofs/QBP/Meta/ExportGraph.lean (v2)

import Lean
import QBP.Basic
import QBP.Experiments.SternGerlach

open Lean Elab Command Meta

/-- Dependency with semantic classification -/
structure SemanticDep where
  name : Name
  kind : String  -- "explicit" | "unfolded" | "simp_lemma" | "type_dep"
  source : String -- Where this was detected
  deriving ToJson, FromJson

/-- Extract proof-term level dependencies (baseline) -/
def getProofTermDeps (env : Environment) (name : Name) : List Name := do
  let some info := env.find? name | return []
  let mut deps := #[]
  if let some val := info.value? then
    deps := deps ++ val.getUsedConstants.toList
  deps.filter fun n => `QBP.isPrefixOf n

/-- Classify a dependency as definition-unfold vs direct-call -/
def classifyDep (env : Environment) (caller callee : Name) : String :=
  -- If callee appears in caller's proof term but not in source syntax,
  -- it was likely unfolded
  -- This is a heuristic; manual override can correct it
  let info := env.find? callee
  match info with
  | some (.defnInfo _) => "unfolded"
  | some (.thmInfo _) => "explicit"
  | _ => "type_dep"

/-- Load manual semantic overrides -/
def loadOverrides : IO (Std.HashMap Name (List SemanticDep)) := do
  let path := "proofs/QBP/Meta/semantic_overrides.json"
  if ← System.FilePath.pathExists path then
    let content ← IO.FS.readFile path
    -- Parse JSON and convert to HashMap
    ...
  else
    return {}

/-- Generate semantic dependency graph -/
def exportSemanticGraph (namespace : Name) : CommandElabM Json := do
  let env ← getEnv
  let overrides ← loadOverrides

  let qbpConstants := env.constants.fold (init := []) fun acc name _ =>
    if namespace.isPrefixOf name then name :: acc else acc

  let nodes ← qbpConstants.mapM fun name => do
    -- Start with proof-term level deps
    let baseDeps := getProofTermDeps env name

    -- Check for manual override
    let semanticDeps := match overrides.find? name with
      | some override => override
      | none => baseDeps.map fun dep => {
          name := dep
          kind := classifyDep env name dep
          source := "proof_term"
        }

    return Json.mkObj [
      ("id", Json.str name.toString),
      ("dependencies", toJson semanticDeps),
      ("extraction_method", Json.str $
        if overrides.contains name then "manual_override" else "proof_term")
    ]

  return Json.mkObj [
    ("namespace", Json.str namespace.toString),
    ("schema_version", Json.str "2.0"),
    ("nodes", Json.arr nodes.toArray)
  ]
```

### Simp Tracing Infrastructure

```lean
-- proofs/QBP/Meta/SimpTrace.lean

import Lean

open Lean Meta Elab Tactic

/-- Environment extension to store simp trace data -/
initialize simpTraceExt : SimplePersistentEnvExtension (Name × List Name) (Std.HashMap Name (List Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => {}
    addEntryFn := fun map (thm, lemmas) => map.insert thm lemmas
  }

/-- Record simp lemmas used for a theorem -/
def recordSimpUsage (thmName : Name) (usedSimps : Simp.UsedSimps) : CoreM Unit := do
  let lemmas := usedSimps.toList.filterMap fun (origin, _) =>
    match origin with
    | .decl name _ _ => some name
    | _ => none
  modifyEnv fun env => simpTraceExt.addEntry env (thmName, lemmas)

/-- Retrieve recorded simp usage for export -/
def getSimpUsage (env : Environment) (thmName : Name) : List Name :=
  match (simpTraceExt.getState env).find? thmName with
  | some lemmas => lemmas
  | none => []
```

### Recommended Proof Style for Traceability

To maximize automated semantic extraction, proofs should follow this style:

```lean
-- PREFERRED: Explicit simp arguments (simp? output)
theorem x_z_orthogonal : vecDot spinXState spinZObservable = 0 := by
  simp only [vecDot, spinXState, spinZObservable, SPIN_X, SPIN_Z,
             mul_zero, mul_one, zero_add, add_zero]

-- AVOID: Bare simp (hides dependencies)
theorem x_z_orthogonal' : vecDot spinXState spinZObservable = 0 := by
  simp [vecDot, spinXState, spinZObservable, SPIN_X, SPIN_Z]

-- PREFERRED: Explicit function application
theorem expectation_x_measured_z_is_zero :
    expectationValue spinXState spinZObservable = 0 :=
  expectation_orthogonal_is_zero spinXState spinZObservable
    spinXState_is_pure spinZObservable_is_pure x_z_orthogonal

-- AVOID: term-mode tricks that hide structure
theorem expectation_x_measured_z_is_zero' :
    expectationValue spinXState spinZObservable = 0 := by
  apply expectation_orthogonal_is_zero <;> first | rfl | assumption
```

---

## Implementation Phases (Revised)

### Phase 1: Enhanced Proof Term Extraction + Manual Layer

1. Create `proofs/QBP/Meta/ExportGraph.lean` with v2 design
2. Implement `getProofTermDeps` with dependency classification
3. Create `semantic_overrides.json` with manual annotations for `rfl`/`simp` cases
4. Merge automated + manual for complete graph

**Deliverable:** Semantically accurate JSON with hybrid extraction

### Phase 2: Simp Tracing Infrastructure

1. Create `proofs/QBP/Meta/SimpTrace.lean`
2. Implement environment extension for simp usage tracking
3. Refactor existing proofs to use `simp only [...]` where possible
4. Update export to incorporate simp trace data

**Deliverable:** Automated simp lemma extraction

### Phase 3: Proof Style Guide + Linting

1. Document recommended proof style for traceability
2. Create linter to warn about opaque `simp` calls
3. Gradually refactor existing proofs

**Deliverable:** Sustainable process for maintaining semantic accuracy

### Phase 4: Visualization Enhancement

1. Update graph visualization to show dependency kinds
2. Color-code: explicit (solid), unfolded (dashed), simp_lemma (dotted)
3. Add "expand" feature to show Mathlib lemmas when relevant

**Deliverable:** Richer visualization reflecting semantic structure

---

## What Can Be Automated vs What Must Remain Manual

### Fully Automated

| Case | Method |
|------|--------|
| Explicit theorem application | `getUsedConstants` on proof term |
| Definition references in types | `getUsedConstants` on type |
| `simp only [...]` lemmas | Direct syntax extraction |
| `exact foo` applications | Proof term analysis |

### Semi-Automated (with tracing)

| Case | Method |
|------|--------|
| Bare `simp` calls | `Simp.UsedSimps` via tracing tactic |
| `omega`/`linarith` | Custom tracing (complex) |
| `decide` | Definitional, hard to trace |

### Manual Annotation Required

| Case | Why |
|------|-----|
| `rfl` proofs | Definitional equality hides computation |
| `native_decide` | Opaque kernel computation |
| Physical meaning | Not encoded in Lean |
| Pedagogical ordering | Logical deps != learning order |

---

## Migration Path (Revised)

1. **Current state:** Manual `DEPENDENCIES` dict in Python
2. **Phase 1:** Hybrid extraction (proof term + manual overrides)
3. **Phase 2:** Simp tracing reduces manual overrides needed
4. **Phase 3:** Style guide prevents new opaque proofs
5. **End state:** 80%+ automated, 20% curated overrides

---

## Known Challenges (Updated)

### Challenge 1: `rfl` Opacity

`rfl` proofs hide all computational content.

**Solution:** Manual annotation in `semantic_overrides.json`, documenting which definitions are unfolded.

### Challenge 2: Simp Tactic Variations

`simp`, `simp only`, `simp_all`, `dsimp` have different tracing needs.

**Solution:** Phase 2 tracing infrastructure handles all variants via `Simp.UsedSimps`.

### Challenge 3: Mathlib Lemma Explosion

`simp` often uses dozens of Mathlib lemmas that would clutter the graph.

**Solution:** Filter to "interesting" lemmas (non-trivial arithmetic, algebraic properties). Configurable depth.

### Challenge 4: Breaking Changes During Refactor

Converting `simp` to `simp only` may break proofs if Mathlib updates.

**Solution:** Pin Mathlib version; update simp arguments when upgrading.

### Challenge 5: Definition vs Theorem Distinction

Some dependencies are definitions being unfolded, others are theorems being applied.

**Solution:** Classify using `ConstantInfo` kind; show differently in visualization.

---

## References (Updated)

- [Lean 4 Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Lean.Environment API](https://leanprover-community.github.io/mathlib4_docs/Lean/Environment.html)
- [Lean.Elab.InfoTree.Types](https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/InfoTree/Types.html) - TermInfo, TacticInfo structures
- [Lean.Meta.Tactic.Simp.Types](https://florisvandoorn.com/LeanCourse24/docs/Lean/Meta/Tactic/Simp/Types.html) - Simp.State, UsedSimps
- [Simp Tactic Documentation](https://leanprover-community.github.io/extras/simp.html) - `simp?` and tracing options
- [lean4/src/Lean/Elab/Tactic/Simp.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Simp.lean) - Implementation reference
- Current export script: `src/viz/interactive/export_data.py`
- Proof graph JSON schema: `src/viz/interactive/data/proof_graph_01.json`

---

## Appendix: Concrete Example

### Current Proof (Basic.lean)

```lean
theorem expectation_orthogonal_is_zero (ψ O : Q)
    (_hψ : isPureQuaternion ψ) (_hO : isPureQuaternion O)
    (h_ortho : vecDot ψ O = 0) : expectationValue ψ O = 0 := by
  simp [expectationValue, vecPart]
  exact h_ortho
```

### Syntactic Dependencies (v1 would produce)

```json
{
  "name": "expectation_orthogonal_is_zero",
  "dependencies": ["expectationValue", "vecPart", "vecDot", "isPureQuaternion"]
}
```

### Semantic Dependencies (v2 produces)

```json
{
  "name": "expectation_orthogonal_is_zero",
  "dependencies": [
    {"name": "expectationValue", "kind": "unfolded", "source": "simp_arg"},
    {"name": "vecPart", "kind": "unfolded", "source": "simp_arg"},
    {"name": "h_ortho", "kind": "explicit", "source": "exact"},
    {"name": "vecDot", "kind": "type_dep", "source": "hypothesis_type"}
  ],
  "extraction_method": "proof_term_classified"
}
```

### Why This Matters

The v2 graph tells James:
- `expectationValue` and `vecPart` are **definitions that get unfolded** (dashed lines in viz)
- `h_ortho` is the **key logical step** (solid line - this is what matters)
- `vecDot` is a **type constraint** (appears in hypothesis, not directly used)

This accurate representation helps James understand that the *essence* of this theorem is: "given orthogonality (h_ortho), the expectation is zero" - not "we need these four symbols."
