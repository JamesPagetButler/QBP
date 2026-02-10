# Proof Review: Angle-Dependent Measurement (Experiment 01b)

*Phase 4b Review Document — Sprint 2*

**Reviewer:** Claude (Red Team perspective)
**Date:** 2026-02-10
**Decision:** PASS

---

## 1. Overview

This document records the formal review of the Lean 4 proofs for Experiment 01b (Angle-Dependent Measurement). The review applies the axiom-first principle: every axiom must be justified on first principles alone, not reverse-engineered from simulation results.

**Files Reviewed:**
- `proofs/QBP/Basic.lean` — Core axioms
- `proofs/QBP/Experiments/AngleDependent.lean` — Experiment-specific proofs

**Ground Truth Reference:**
- `research/01b_angle_dependent_expected_results.md`

---

## 2. Compilation Status

| Check | Status |
|-------|--------|
| `lake build` succeeds | PASS (2390 jobs) |
| No `sorry` in proof files | PASS |
| `QBP.Experiments.AngleDependent` compiles | PASS |

---

## 3. Axiom Analysis (First Principles)

### Axiom 1: State is Unit Quaternion

```lean
def isUnitQuaternion (q : Q) : Prop := q.normSq = 1
```

**First-principles justification:** Normalization is fundamental to probability interpretation in QM (⟨ψ|ψ⟩ = 1). This is independent of any simulation — it follows from the requirement that total probability equals 1.

**Verdict:** JUSTIFIED

### Axiom 2: Observable is Pure Quaternion

```lean
def isPureQuaternion (q : Q) : Prop := q.re = 0
```

**First-principles justification:** Pure quaternions correspond to vectors in ℝ³ (Hamilton's original insight, 1843). A measurement direction is a point on S², which is exactly the space of pure unit quaternions. This geometric correspondence is independent of any physical measurement.

**Verdict:** JUSTIFIED

### Expectation Value Formula

```lean
def expectationValue (ψ O : Q) : ℝ := vecDot (vecPart ψ) (vecPart O)
```

**Concern:** The code comment notes "The factor of 2 was removed based on findings from Experiment 01b (PR #116)". This appears to suggest the axiom was fitted to simulation results.

**Analysis:** The ground truth document (§4.4) provides the mathematical argument:

1. Original formula: ⟨O⟩ = 2 × vecDot(ψ, O) produces values in [-2, +2]
2. Born rule P(+) = (1 + ⟨O⟩)/2 requires ⟨O⟩ ∈ [-1, +1] for valid probabilities
3. Cauchy-Schwarz inequality guarantees |vecDot(unit, unit)| ≤ 1

**Critical question:** Would we have chosen vecDot (without factor 2) if we had never run the simulation?

**Answer:** YES. The constraint ⟨O⟩ ∈ [-1, +1] is mathematically forced by probability bounds (0 ≤ P ≤ 1). The factor of 2 violates this constraint for any non-orthogonal configuration. The simulation revealed the bug, but the correct axiom is derivable from first principles alone.

**Verdict:** JUSTIFIED — correction is mathematically forced, not empirically fitted

### Born Rule

```lean
noncomputable def probUp (ψ O : Q) : ℝ := (1 + expectationValue ψ O) / 2
```

**First-principles justification:** This is the unique linear map from [-1, +1] to [0, 1] satisfying the boundary conditions:

- ⟨O⟩ = +1 (aligned) → P(+) = 1
- ⟨O⟩ = -1 (anti-aligned) → P(+) = 0
- ⟨O⟩ = 0 (orthogonal) → P(+) = 0.5

**Verdict:** JUSTIFIED

---

## 4. Theorem Correspondence

The following table maps ground truth predictions (§10 of expected results) to proved theorems:

| Ground Truth Prediction | Lean Theorem | Status |
|------------------------|--------------|--------|
| P(+) = (1 + cos θ)/2 | `prob_up_angle` | PASS |
| P(+) = cos²(θ/2) | `prob_up_angle_cos_sq` | PASS |
| P(-) = (1 - cos θ)/2 | `prob_down_angle` | PASS |
| P(-) = sin²(θ/2) | `prob_down_angle_sin_sq` | PASS |
| θ=0° → P(+)=1 | `prob_up_theta_zero` | PASS |
| θ=90° → P(+)=0.5 | `prob_up_theta_pi_div_two` | PASS |
| θ=180° → P(+)=0 | `prob_up_theta_pi` | PASS |
| θ=90° recovers Stern-Gerlach | `angle_consistent_with_stern_gerlach` | PASS |

All ground truth predictions have corresponding proved theorems.

---

## 5. Mathematical Rigor Assessment

### State Construction

```lean
noncomputable def psiAngle (θ : ℝ) : Q := ⟨0, Real.sin θ, 0, Real.cos θ⟩
```

This represents a spin state at angle θ from the z-axis in the xz-plane:
- At θ=0: ψ = k (spin-z up)
- At θ=π/2: ψ = i (spin-x)
- At θ=π: ψ = -k (spin-z down)

**Verified properties:**
- Pure quaternion: `psiAngle_is_pure` proves re = 0
- Unit quaternion: `psiAngle_is_unit` uses sin²θ + cos²θ = 1

### Proof Techniques

All proofs use standard Lean/Mathlib tactics:
- `unfold`, `simp`, `ring_nf`, `rw`

Key mathematical identities from Mathlib:
- Pythagorean: `Real.sin_sq_add_cos_sq`
- Half-angle: `Real.cos_sq`, `Real.cos_two_mul`
- Standard values: `Real.cos_zero`, `Real.cos_pi`, `Real.cos_pi_div_two`

No custom axioms or `sorry` escape hatches were used.

---

## 6. Axiom-First Principle Summary

> "Would this axiom be chosen if we had never run the simulation?"

| Axiom | First-Principles Basis | Verdict |
|-------|----------------------|---------|
| State normalization | Probability conservation (∑P = 1) | JUSTIFIED |
| Observable as pure quaternion | Geometric necessity (S² ↔ Im(ℍ) ∩ S³) | JUSTIFIED |
| Expectation = vecDot | Probability bounds + Cauchy-Schwarz | JUSTIFIED |
| Born rule (1 + ⟨O⟩)/2 | Unique linear map with correct boundaries | JUSTIFIED |

**Overall assessment:** All axioms are derivable from first principles. The factor-of-2 correction discovered in PR #116 was a bug fix (the original violated probability bounds), not a fit to empirical data.

---

## 7. Decision Gate

| Criterion | Status |
|-----------|--------|
| All axioms justified on first principles | PASS |
| Proof-to-ground-truth correspondence verified | PASS |
| Clean compilation (no errors) | PASS |
| No incomplete proofs (`sorry`) | PASS |

## DECISION: PASS

The proofs are mathematically rigorous and correctly implement the QBP axioms. Ready for Phase 4c (Interactive Proof Visualization).

---

## 8. Notes for Phase 4c

The proof dependency graph is:

```
mathlib: sin_sq_add_cos_sq
              ↓
        psiAngle_is_unit
              ↓
        expectation_angle
         ↙         ↘
prob_up_angle    prob_down_angle
      ↓                ↓
prob_up_angle_cos_sq   prob_down_angle_sin_sq
      ↓
edge case theorems (θ=0, π/2, π)
      ↓
angle_consistent_with_stern_gerlach
```

**Visualization opportunities:**
1. Animate the state vector psiAngle(θ) rotating in the Bloch sphere
2. Show how the half-angle identity transforms (1 + cos θ)/2 to cos²(θ/2)
3. Highlight consistency with Stern-Gerlach at θ = π/2

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2026-02-10 | Initial review (Phase 4b) |
