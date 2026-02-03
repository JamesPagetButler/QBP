# Phase 4 Formal Verification Guide for Gemini

This guide enables Gemini to resolve Phase 4 (Formal Proof) issues using the Lean 4 infrastructure.

## Overview

Phase 4 issues require formal mathematical proofs that verify the QBP predictions match experimental ground truth. Each experiment (Issues #55-#63) needs its own Lean proof file.

## Prerequisites

1. Lean 4 installed via elan (see [lean4_setup.md](lean4_setup.md))
2. Project builds successfully: `cd proofs && lake build`
3. Familiarity with the QBP axioms in `proofs/QBP/Basic.lean`

## Project Structure

```
proofs/
├── QBP.lean              # Root module (imports all submodules)
├── QBP/
│   ├── Basic.lean        # Core definitions (Axioms 1 & 2)
│   ├── Measurement.lean  # Measurement postulate (create as needed)
│   └── Experiments/
│       ├── SternGerlach.lean   # Issue #55
│       ├── DoubleSlit.lean     # Issue #56
│       ├── LambShift.lean      # Issue #57
│       ├── AnomalousMagnetic.lean # Issue #58
│       ├── Bell.lean           # Issue #59
│       ├── Statistics.lean     # Issue #60
│       ├── Positronium.lean    # Issue #61
│       ├── Hydrogen.lean       # Issue #62
│       └── Gravity.lean        # Issue #63
├── lakefile.lean
└── lean-toolchain
```

## Phase 4 Workflow

For each experiment's Phase 4 issue:

### Step 1: Read Ground Truth (Phase 1 output)

- Location: `research/NN_experiment_expected_results.md`
- Extract mathematical claims that need formal proof
- Identify numerical predictions and their derivations

### Step 2: Review Implementation (Phase 2 output)

- Core functions: `src/qphysics.py`
- Experiment code: `experiments/NN_experiment/simulate.py`
- Map Python functions to Lean definitions

### Step 3: Write Lean Proofs

Create `proofs/QBP/Experiments/ExperimentName.lean`:

```lean
import QBP.Basic

namespace QBP.Experiments.ExperimentName

-- State theorems matching ground truth claims
-- Prove each theorem without `sorry`

end QBP.Experiments.ExperimentName
```

### Step 4: Update Root Module

Add import to `proofs/QBP.lean`:

```lean
import QBP.Basic
import QBP.Experiments.ExperimentName
```

### Step 5: Build and Verify

```bash
cd proofs && lake build
```

- All proofs must compile
- No `sorry` allowed

## Available Mathlib4 Resources

### Quaternion Operations

```lean
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion

-- Type: Quaternion ℝ
-- Components: q.re, q.imI, q.imJ, q.imK
-- Norm squared: q.normSq
-- Conjugate: star q
-- Multiplication: q₁ * q₂
```

### Core QBP Definitions (from Basic.lean)

```lean
namespace QBP

-- Quaternion type alias
abbrev Q := Quaternion ℝ

-- Axiom 1: Unit quaternion state
def isUnitQuaternion (q : Q) : Prop := q.normSq = 1

-- Axiom 2: Pure quaternion observable
def isPureQuaternion (q : Q) : Prop := q.re = 0

-- Standard spin observables
def SPIN_X : Q := ⟨0, 1, 0, 0⟩
def SPIN_Y : Q := ⟨0, 0, 1, 0⟩
def SPIN_Z : Q := ⟨0, 0, 0, 1⟩

end QBP
```

## Key Theorems by Experiment

| Issue | Experiment | Key Theorems |
|-------|------------|--------------|
| #55 | Stern-Gerlach | Binary outcomes (±1), 50/50 split for perpendicular |
| #56 | Double-Slit | Interference pattern formula |
| #57 | Lamb Shift | Energy shift expression |
| #58 | g-2 | Anomalous magnetic moment formula |
| #59 | Bell's Theorem | CHSH bound: \|S\| ≤ 2√2 |
| #60 | Particle Statistics | Boson/fermion symmetry properties |
| #61 | Positronium | Decay rate formula |
| #62 | Hydrogen Spectrum | Energy level formula |
| #63 | Gravity Tests | Equivalence principle |

## Example: Stern-Gerlach Proof Structure (Issue #55)

```lean
-- proofs/QBP/Experiments/SternGerlach.lean
import QBP.Basic

namespace QBP.Experiments.SternGerlach

/-- Measurement outcomes are binary: +1 or -1 -/
theorem binary_outcomes (outcome : ℤ) (h : is_measurement_outcome outcome) :
    outcome = 1 ∨ outcome = -1 := by
  -- proof here

/-- For perpendicular state and observable, P(up) = 1/2 -/
theorem perpendicular_fifty_fifty (ψ O : Q)
    (hψ : isUnitQuaternion ψ) (hO : isPureQuaternion O)
    (h_perp : ψ.imI * O.imI + ψ.imJ * O.imJ + ψ.imK * O.imK = 0) :
    prob_up ψ O = 1/2 := by
  -- proof here

end QBP.Experiments.SternGerlach
```

## Definition of Done for Phase 4

- [ ] All theorems stated match ground truth claims from Phase 1
- [ ] All proofs compile (`lake build` succeeds)
- [ ] No `sorry` in any proof
- [ ] Proof file added to `proofs/QBP.lean` imports
- [ ] Red Team review passed
- [ ] Gemini review passed

## Tips for Writing Proofs

### Start Simple

Begin with definitional equalities (provable by `rfl`) before tackling complex theorems.

### Use Mathlib Tactics

Common tactics:
- `rfl` - reflexivity (definitional equality)
- `simp` - simplification
- `ring` - ring arithmetic
- `norm_num` - numerical computation
- `field_simp` - clear denominators
- `linarith` - linear arithmetic

### Check Mathlib Documentation

Mathlib4 docs: https://leanprover-community.github.io/mathlib4_docs/

Search for quaternion lemmas:
- `Quaternion.normSq_*`
- `Quaternion.star_*`
- `Quaternion.mul_*`

### Build Incrementally

After adding each theorem, run `lake build` to catch errors early.

## Common Patterns

### Proving a quantity equals zero

```lean
theorem foo_eq_zero : foo = 0 := by
  simp [foo]  -- unfold definition and simplify
```

### Proving equality of quaternions

```lean
theorem q1_eq_q2 : q1 = q2 := by
  ext  -- reduce to component-wise equality
  · simp [q1, q2]  -- prove re components equal
  · simp [q1, q2]  -- prove imI components equal
  · simp [q1, q2]  -- prove imJ components equal
  · simp [q1, q2]  -- prove imK components equal
```

### Using hypotheses

```lean
theorem bar (h : isPureQuaternion q) : q.re = 0 := by
  exact h  -- or just `h`
```

## Phase 4 Issue Links

| Issue | Title |
|-------|-------|
| [#55](../../issues/55) | Experiment 1 (Stern-Gerlach) - Formal Proof |
| [#56](../../issues/56) | Experiment 2 (Double-Slit) - Formal Proof |
| [#57](../../issues/57) | Experiment 3 (Lamb Shift) - Formal Proof |
| [#58](../../issues/58) | Experiment 4 (g-2) - Formal Proof |
| [#59](../../issues/59) | Experiment 5 (Bell's Theorem) - Formal Proof |
| [#60](../../issues/60) | Experiment 6 (Particle Statistics) - Formal Proof |
| [#61](../../issues/61) | Experiment 7 (Positronium) - Formal Proof |
| [#62](../../issues/62) | Experiment 8 (Hydrogen Spectrum) - Formal Proof |
| [#63](../../issues/63) | Experiment 9 (Gravity Tests) - Formal Proof |
