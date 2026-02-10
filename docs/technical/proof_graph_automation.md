# Proof Graph Automation: Technical Design

*Design document for automating proof dependency extraction from Lean 4.*

**Issue:** #142
**Status:** Design complete, implementation pending

---

## Problem Statement

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

---

## Proposed Solution: Lean Metaprogramming

**Recommendation:** Use Lean 4's metaprogramming capabilities to extract the actual dependency graph from the compiled proof environment.

### Why Metaprogramming?

| Approach | Accuracy | Complexity | Maintenance |
|----------|----------|------------|-------------|
| Regex parsing (current) | Low | Low | High |
| LSP queries | Medium | High | Medium |
| **Metaprogramming** | **High** | Medium | **Low** |

Metaprogramming wins because:
1. Uses Lean's actual type system (no parsing errors)
2. Lake integration for automation
3. Single source of truth

---

## Technical Design

### Architecture

```
proofs/QBP/
├── Basic.lean
├── Experiments/
│   └── SternGerlach.lean
└── Meta/
    └── ExportGraph.lean    ← NEW: Metaprogramming script
```

### Key Lean 4 APIs

```lean
-- Get all constants (theorems, defs) in environment
Lean.Environment.constants

-- Get the type/value expression of a constant
Lean.ConstantInfo.type
Lean.ConstantInfo.value?

-- Extract all referenced constants from an expression
Lean.Expr.getUsedConstants

-- Filter to QBP namespace
Name.isPrefixOf `QBP
```

### Implementation Outline

```lean
-- proofs/QBP/Meta/ExportGraph.lean

import Lean
import QBP.Basic
import QBP.Experiments.SternGerlach

open Lean Elab Command Meta

/-- Extract dependency graph for a constant -/
def getDependencies (env : Environment) (name : Name) : List Name := do
  let some info := env.find? name | return []
  let mut deps := #[]
  -- Get dependencies from type
  deps := deps ++ info.type.getUsedConstants.toList
  -- Get dependencies from value (if definition/theorem)
  if let some val := info.value? then
    deps := deps ++ val.getUsedConstants.toList
  -- Filter to QBP namespace only
  deps.filter (·.isPrefixOf `QBP)

/-- Generate JSON export -/
def exportGraph (namespace : Name) : CommandElabM Json := do
  let env ← getEnv
  let qbpConstants := env.constants.fold (init := []) fun acc name _ =>
    if namespace.isPrefixOf name then name :: acc else acc

  let nodes := qbpConstants.map fun name =>
    let deps := getDependencies env name
    Json.mkObj [
      ("id", Json.str name.toString),
      ("dependencies", Json.arr (deps.map (Json.str ·.toString)).toArray)
    ]

  return Json.mkObj [
    ("namespace", Json.str namespace.toString),
    ("nodes", Json.arr nodes.toArray)
  ]

-- Lake task to run export
#eval do
  let graph ← exportGraph `QBP.Experiments.SternGerlach
  IO.FS.writeFile "data/proof_graph.json" graph.pretty
```

### Lake Integration

```lean
-- lakefile.lean addition

@[default_target]
lean_lib QBP

-- New: Export graph task
script export_graph do
  -- Import the export script and run
  -- Writes to data/proof_graph_XX.json
  return 0
```

### CI Integration

```yaml
# .github/workflows/ci.yml addition

- name: Export proof graph
  run: lake run export_graph

- name: Validate graph matches schema
  run: python scripts/validate_proof_graph.py
```

---

## Implementation Phases

### Phase 1: Metaprogramming Script (Priority)

1. Create `proofs/QBP/Meta/ExportGraph.lean`
2. Implement basic constant enumeration
3. Implement dependency extraction via `getUsedConstants`
4. Export to JSON

**Deliverable:** Automated JSON generation

### Phase 2: Lake Integration

1. Add Lake script for graph export
2. Integrate with build process
3. Add CI step to validate graph freshness

**Deliverable:** `lake run export_graph`

### Phase 3: Physical Meaning Augmentation

1. Keep `PHYSICAL_MEANINGS` dict in Python
2. Merge automated deps with human meanings
3. Validate consistency

**Deliverable:** Complete export pipeline

### Phase 4: Multi-Experiment Support

1. Parameterize by experiment namespace
2. Generate separate JSON per experiment
3. Update visualization to load appropriate file

**Deliverable:** Scalable to all experiments

---

## Known Challenges

### Challenge 1: Transitive Dependencies

`getUsedConstants` returns immediate references, not transitive closure.

**Solution:** Build dependency graph, then compute transitive closure if needed for visualization.

### Challenge 2: Mathlib Dependencies

Many QBP proofs depend on Mathlib. We want QBP dependencies only.

**Solution:** Filter by `Name.isPrefixOf `QBP`.

### Challenge 3: Human-Readable Names

Lean names like `QBP.Experiments.SternGerlach.prob_up_x_measured_z_is_half` are verbose.

**Solution:** Strip namespace prefix for display, keep full name for linking.

### Challenge 4: Physical Meanings

Automated extraction gives structure, not semantics.

**Solution:** Maintain separate `physical_meanings.json` curated by humans, merge at export time.

---

## Migration Path

1. **Current state:** Manual `DEPENDENCIES` dict in Python
2. **After Phase 1:** Automated JSON, Python merges meanings
3. **After Phase 3:** Single export command generates complete data
4. **After Phase 4:** Works for all experiments automatically

---

## Open Questions

1. Should the exported JSON include proof terms (expressions) or just names?
2. How to handle private/internal definitions?
3. Should we version the JSON schema?

---

## References

- [Lean 4 Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Lean.Environment API](https://leanprover-community.github.io/mathlib4_docs/Lean/Environment.html)
- Current export script: `src/viz/interactive/export_data.py`
- Proof graph JSON schema: `src/viz/interactive/data/proof_graph_01.json`
