# Lean 4 Library Strategy

*A strategy for building cumulative, reusable Lean 4 proof libraries across QBP experiments.*

---

## Overview

As QBP progresses through multiple experiments, we risk re-proving the same foundational lemmas. This document defines a strategy for building a cumulative library of Lean 4 theorems that:
- Reduces rework across experiments
- Ensures consistency in the logical foundation
- Maintains the axiom-first principle
- Enables rigorous connections between experiments

---

## Current Structure

```
proofs/
├── QBP.lean                    # Root import file
├── QBP/
│   ├── Basic.lean              # Foundational definitions and theorems
│   └── Experiments/
│       └── SternGerlach.lean   # Experiment 01 proofs
├── lakefile.lean
├── lean-toolchain
└── README.md
```

---

## Library Hierarchy

### Tier 1: Core (QBP.Basic)

**Scope:** Fundamental definitions and theorems that apply to ALL experiments.

**Contents:**
- Quaternion type definition (`Q := Quaternion ℝ`)
- Unit quaternion predicate (`isUnitQuaternion`)
- Pure quaternion predicate (`isPureQuaternion`)
- Standard spin observables (`SPIN_X`, `SPIN_Y`, `SPIN_Z`)
- Vector part extraction (`vecPart`)
- Dot product (`vecDot`)
- Expectation value (`expectationValue`)
- Probability functions (`probUp`, `probDown`)
- Fundamental theorems (normalization, orthogonality)

**Criteria for inclusion:**
- Derived directly from QBP axioms
- Used by 2+ experiments
- No experiment-specific assumptions

### Tier 2: Domain Libraries (QBP.Rotation, QBP.Measurement, etc.)

**Scope:** Specialized domains that may be used by multiple experiments.

**Proposed structure:**
```
QBP/
├── Basic.lean           # Tier 1: Core
├── Rotation.lean        # Tier 2: Quaternion rotation formalism
├── Measurement.lean     # Tier 2: Measurement theory extensions
├── Entanglement.lean    # Tier 2: Multi-particle systems (future)
└── Experiments/         # Tier 3: Per-experiment proofs
```

**Criteria for promotion to Tier 2:**
- Used by 2+ experiments
- Represents a coherent domain concept
- Has clear API boundaries

### Tier 3: Experiment Proofs (QBP.Experiments.*)

**Scope:** Proofs specific to individual experiments.

**Contents:**
- Theorems that reference specific experimental setups
- Simulation-correspondence proofs
- Result validation theorems

**Rule:** If a theorem in Tier 3 is reused by another experiment, consider promoting it to Tier 1 or Tier 2.

---

## Identifying Theorem Location

Use this decision tree when adding a new theorem:

```
Is this theorem derived purely from QBP axioms?
├── No → Tier 3 (Experiment-specific)
└── Yes
    └── Is it likely to be used by multiple experiments?
        ├── No → Tier 3 (but document potential for promotion)
        └── Yes
            └── Does it fit an existing Tier 2 domain?
                ├── Yes → Add to that domain library
                └── No
                    └── Does it warrant a new domain?
                        ├── Yes → Create new Tier 2 library
                        └── No → Tier 1 (Basic.lean)
```

---

## Axiom-First Principle

The axiom-first principle guards against "simulation-steered proving" — formulating axioms to match observed numerical results rather than deriving predictions from first principles.

### Safeguards for Library Development

1. **Axiom immutability:** Core axioms (Axioms 1-4 in Basic.lean) must NOT be modified to make new proofs work.

2. **Derivation direction:** All library theorems must flow FROM axioms, never reverse-engineered from experiment results.

3. **Cross-experiment consistency:** If Experiment N's proof requires modifying a library theorem, verify that Experiments 1..N-1 still compile and pass.

4. **Review gate:** All additions to Tier 1 or Tier 2 libraries require Tier 3 review (Red Team + Gemini).

### Process for Library Modifications

When a new experiment suggests modifications to shared libraries:

1. **Document the motivation** — Why does the current library not support this proof?
2. **Trace to axioms** — Can the needed capability be derived from existing axioms?
3. **Impact analysis** — What existing proofs would be affected?
4. **Review escalation** — Tier 1/2 changes always require Tier 3 review

---

## Inter-Experiment Connections

The library enables formal connections between experiments:

### Logical Dependencies

```
Experiment 01b (Angle-Dependent) builds on Experiment 01 (Stern-Gerlach):
- Imports: QBP.Basic (shared definitions)
- Extends: probUp theorem to arbitrary angles
- Validates: cos²(θ/2) formula for all θ
```

### Dependency Graph

Each experiment's proof file should declare its dependencies:

```lean
-- SternGerlach.lean
import QBP.Basic           -- Core library
-- Note: No experiment dependencies (foundational)

-- AngleDependent.lean
import QBP.Basic           -- Core library
import QBP.Rotation        -- Rotation formalism
-- Note: Builds on concepts proven in SternGerlach
```

### Backward Compatibility

When adding new experiments:
1. Run `lake build` to verify all existing proofs compile
2. Run the Phase 4a test suite
3. Document any new dependencies in the experiment's proof file header

---

## General-Purpose Libraries (/libs/)

Some capabilities developed during QBP proofs may be useful to the broader Lean community. These should be extracted to `/libs/` as standalone packages.

### Extraction Criteria

| Criterion | Question |
|-----------|----------|
| Generality | Would non-QBP Lean users benefit? |
| Independence | Can it function without QBP-specific definitions? |
| Quality | Does it meet Library Quality Standards? |

### Extraction Process

1. Identify candidate theorems/definitions in `proofs/QBP/`
2. Create standalone package in `/libs/<name>/`
3. Migrate code (NO imports from `proofs/QBP/`)
4. Update `proofs/QBP/` to import from `/libs/` via local require
5. Verify all proofs still compile
6. Publish to Reservoir when ready

See [Library Quality Standards](../CONTRIBUTING.md#library-quality-standards) for publication requirements.

---

## Implementation Phases

### Phase A: Current State (Experiments 01, 01b)

- `Basic.lean`: Core definitions
- `Experiments/SternGerlach.lean`: Experiment 01 proofs
- No Tier 2 libraries yet

### Phase B: Rotation Extension (Experiment 01b → 02)

When implementing Experiment 01b:
- Consider extracting rotation formalism to `QBP/Rotation.lean`
- Document rotation quaternion derivation
- Prepare for reuse in future experiments

### Phase C: Multi-Experiment Expansion (Experiments 02-05)

As more experiments are added:
- Evaluate which theorems should move to Tier 2
- Create domain libraries as patterns emerge
- Build inter-experiment dependency graph

### Phase D: Library Extraction (Ongoing)

Throughout development:
- Identify general-purpose candidates
- Extract to `/libs/` when mature
- Publish to Reservoir for community use

---

## Integration with Phase 4 Workflow

This strategy integrates with the existing Phase 4 workflow:

### Phase 4a: Formal Proof

1. Check existing library for reusable theorems
2. Write experiment-specific proofs in `Experiments/`
3. Identify candidates for library promotion
4. Document theorem dependencies

### Phase 4b: Proof Review

1. Review new theorems against axiom-first principle
2. Evaluate library placement decisions
3. Check for breaking changes to existing proofs
4. Flag promotion candidates for discussion

### Phase 4c: Interactive Visualization

1. Library structure influences proof graph visualization
2. Show dependency chains clearly
3. Distinguish Tier 1/2/3 theorems visually

---

## Governance

### Who decides on library structure?

- **Tier 1 (Basic.lean):** James approval required for any changes
- **Tier 2 (Domain libraries):** Red Team + Gemini review, James approval
- **Tier 3 (Experiments):** Standard Tier 2 review process

### Versioning

Until the project matures:
- No semantic versioning within `proofs/QBP/`
- All changes validated by full `lake build`
- Breaking changes documented in commit messages

Future consideration:
- Lean Package versioning for `QBP` package
- Reservoir publication for mature components

---

## References

- [Axiom-First Principle](../CONTRIBUTING.md) — Preventing simulation-steered proving
- [Library Quality Standards](../CONTRIBUTING.md#library-quality-standards) — Standards for `/libs/`
- [Phase 4 Workflow](../CONTRIBUTING.md#phase-4-formal-verification) — Formal verification process
- [proofs/README.md](../../proofs/README.md) — Current proof structure documentation
