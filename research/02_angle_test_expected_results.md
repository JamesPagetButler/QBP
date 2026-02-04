# Expected Results for Angle-Dependent Measurement (Ground Truth)

*This document was produced through the Collaborative Theory Workflow, synthesizing independent work from Claude and Gemini, evaluated by Bell.*

---

## 1. Overview

This document derives the QBP prediction for measurement probability as a function of the angle θ between preparation and measurement axes. We demonstrate that quaternion algebra necessarily produces the quantum mechanical result P(+) = (1 + cos θ)/2, and we explain *why* this is so—not merely that it is.

**Key Finding:** During this derivation, we identified a critical issue with the stated QBP axioms. The expectation value formula ⟨O⟩ = 2 × vecDot(ψ, O) produces invalid probabilities for non-orthogonal cases. This document proposes a correction and validates it against known physics.

---

## 2. The Physical Situation

Imagine a Stern-Gerlach apparatus where we can rotate the magnet to any angle. We prepare a particle with spin along direction **n̂₁**, then measure along direction **n̂₂**, where the angle between them is θ.

**The question:** What is the probability of measuring spin-up (+1) along **n̂₂**?

**Standard QM answer:** P(+) = cos²(θ/2) = (1 + cos θ)/2

**Our task:** Derive this from QBP axioms alone, without importing the standard QM result.

---

## 3. The QBP Axioms

1. **Axiom 1 (State):** A spin state is a pure unit quaternion ψ (real part = 0, |ψ| = 1)
2. **Axiom 2 (Observable):** A measurement direction is a pure unit quaternion O
3. **Axiom 3 (Expectation Value):** ⟨O⟩ = 2 × vecDot(ψ, O) ← *Under review*
4. **Axiom 4 (Born Rule):** P(+) = (1 + ⟨O⟩)/2, P(-) = (1 - ⟨O⟩)/2

---

## 4. The Core Derivation

### 4.1 Representing Directions as Quaternions

A pure unit quaternion has the form:

```
q = ai + bj + ck,  where a² + b² + c² = 1
```

This is isomorphic to a unit vector in ℝ³: **v** = (a, b, c). The space of pure unit quaternions *is* the 2-sphere S²—every point corresponds to a direction in 3D space, and hence to a possible spin orientation.

### 4.2 Setup for Angle-Dependent Measurement

Following the convention from our simulation code:

- **Observable (O):** Measurement along the z-axis → `O = k = ⟨0, 0, 0, 1⟩`
- **State (ψ):** Prepared at angle θ from z-axis in the x-z plane → `ψ(θ) = sin(θ)·i + cos(θ)·k`

This gives vec(ψ) = (sin θ, 0, cos θ) and vec(O) = (0, 0, 1).

### 4.3 Computing the Vector Dot Product

```
vecDot(ψ, O) = (sin θ × 0) + (0 × 0) + (cos θ × 1) = cos θ
```

**Key insight:** The quaternion dot product of pure unit quaternions equals the cosine of the angle between them. This is not something we put in—it's a geometric property that Hamilton's algebra automatically provides.

### 4.4 The Factor-of-2 Problem

Applying Axiom 3 as stated:

```
⟨O⟩ = 2 × vecDot(ψ, O) = 2 × cos θ
```

This gives ⟨O⟩ ranging from -2 to +2. But for a ±1 observable, expectation values must lie in [-1, +1].

**Testing the limiting cases:**

| θ | cos θ | ⟨O⟩ = 2 cos θ | P(+) = (1 + ⟨O⟩)/2 | Valid? |
|---|-------|---------------|---------------------|--------|
| 0° | 1 | 2 | 1.5 | ❌ Invalid |
| 90° | 0 | 0 | 0.5 | ✓ Valid |
| 180° | -1 | -2 | -0.5 | ❌ Invalid |

**Conclusion:** The factor of 2 in Axiom 3 produces unphysical results. This error was not detected in Experiment 01 because vecDot(i, k) = 0, making the factor of 2 irrelevant (2 × 0 = 0).

### 4.5 Proposed Axiom Correction

The expectation value formula should be:

```
⟨O⟩ = vecDot(ψ, O)  [CORRECTED]
```

This gives:

| θ | cos θ | ⟨O⟩ = cos θ | P(+) = (1 + cos θ)/2 | Valid? |
|---|-------|-------------|----------------------|--------|
| 0° | 1 | 1 | 1.0 | ✓ |
| 90° | 0 | 0 | 0.5 | ✓ |
| 180° | -1 | -1 | 0.0 | ✓ |

### 4.6 Final Derivation

With the corrected axiom:

```
⟨O⟩ = vecDot(ψ, O) = cos θ

P(+) = (1 + ⟨O⟩)/2 = (1 + cos θ)/2
```

### 4.7 Verification Against Standard QM

Standard quantum mechanics gives: P(+) = cos²(θ/2)

Using the half-angle identity:
```
cos²(θ/2) = (1 + cos θ)/2
```

**The QBP prediction matches standard QM exactly.** ✓

---

## 5. Why Does This Work?

It is not enough to show *that* quaternions give the right answer. We must understand *why*.

### 5.1 The Geometry of Spin States

In standard QM, spin-1/2 states live in a 2D complex Hilbert space (ℂ²). The space of pure states is the Bloch sphere—a 2-sphere S².

In QBP, spin states are pure unit quaternions. The space of pure unit quaternions is *also* S² (embedded in 3D imaginary quaternion space).

**These are the same space.** The quaternion formulation is not an approximation—it is an alternative parameterization of the same geometric object.

### 5.2 Why Cos θ Appears

The dot product of unit vectors gives cos θ—this is the projection of one direction onto another. For spin-1/2, measuring a state prepared along **n̂₁** using an apparatus aligned with **n̂₂** asks: "How much does this state 'point' in the measurement direction?"

The quaternion formulation makes this geometric interpretation manifest. The answer is cos θ because that is literally what "projection" means in Euclidean geometry.

### 5.3 Why (1 + cos θ)/2?

The raw projection cos θ ranges from -1 to +1, but probabilities must be non-negative. The Born rule P(+) = (1 + ⟨O⟩)/2 is the unique linear map that:

- Maps ⟨O⟩ = +1 (fully aligned) → P(+) = 1
- Maps ⟨O⟩ = -1 (anti-aligned) → P(+) = 0
- Maps ⟨O⟩ = 0 (orthogonal) → P(+) = 0.5

### 5.4 The Deep Connection

Hamilton quaternions encode SO(3) rotations. Spin-1/2 transforms under SU(2), which is the double cover of SO(3). The mathematics is connected at a fundamental level.

**The QBP framework works because quaternions and spin-1/2 quantum mechanics describe the same underlying geometric structure.**

---

## 6. Edge Cases and Physical Interpretation

### 6.1 θ = 0° (Aligned)

- vecDot(ψ, O) = cos(0°) = 1
- ⟨O⟩ = 1
- P(+) = 1.0

**Physical meaning:** Measuring spin along the preparation axis always gives the prepared value. Complete certainty.

### 6.2 θ = 90° (Orthogonal)

- vecDot(ψ, O) = cos(90°) = 0
- ⟨O⟩ = 0
- P(+) = 0.5

**Physical meaning:** The state has no "preference" for either outcome along the perpendicular axis. Maximum uncertainty. (This is Experiment 01.)

### 6.3 θ = 180° (Anti-aligned)

- vecDot(ψ, O) = cos(180°) = -1
- ⟨O⟩ = -1
- P(+) = 0.0

**Physical meaning:** Measuring along the opposite direction always gives the opposite result. Complete certainty of spin-down.

### 6.4 θ = 60°

- vecDot(ψ, O) = cos(60°) = 0.5
- ⟨O⟩ = 0.5
- P(+) = 0.75

**Physical meaning:** The state "partially points" in the measurement direction, giving a 3:1 bias toward spin-up.

---

## 7. Quantitative Predictions & Acceptance Criteria

### 7.1 Test Angles

| θ (degrees) | θ (radians) | cos θ | Expected P(+) | Rationale |
|-------------|-------------|-------|---------------|-----------|
| 0° | 0 | 1.000 | 1.000 | Perfect alignment (deterministic) |
| 30° | π/6 | 0.866 | 0.933 | Tests smooth variation |
| 45° | π/4 | 0.707 | 0.854 | Common angle, irrational cos |
| 60° | π/3 | 0.500 | 0.750 | Clean fractional value |
| 90° | π/2 | 0.000 | 0.500 | Maximum uncertainty (Exp 01) |
| 120° | 2π/3 | -0.500 | 0.250 | Tests negative expectation |
| 135° | 3π/4 | -0.707 | 0.146 | Symmetry with 45° |
| 150° | 5π/6 | -0.866 | 0.067 | Near anti-alignment |
| 180° | π | -1.000 | 0.000 | Perfect anti-alignment (deterministic) |

### 7.2 Statistical Parameters

For N = 1,000,000 trials per angle:

- **Expected count:** μ = N × P(+)
- **Standard deviation:** σ = √(N × P(+) × (1 - P(+)))
- **Acceptance criterion:** |Measured count - μ| ≤ 3σ

**Note:** σ varies with angle. At θ = 90°, σ = 500. At θ = 0° or 180°, σ = 0 (deterministic).

### 7.3 Detailed Acceptance Table

| θ | P(+) | μ | σ | 3σ Range |
|---|------|---|---|----------|
| 0° | 1.000 | 1,000,000 | 0.0 | Exactly 1,000,000 |
| 30° | 0.933 | 933,013 | 250.0 | [932,263, 933,763] |
| 45° | 0.854 | 853,553 | 353.6 | [852,493, 854,614] |
| 60° | 0.750 | 750,000 | 433.0 | [748,701, 751,299] |
| 90° | 0.500 | 500,000 | 500.0 | [498,500, 501,500] |
| 120° | 0.250 | 250,000 | 433.0 | [248,701, 251,299] |
| 135° | 0.146 | 146,447 | 353.6 | [145,386, 147,507] |
| 150° | 0.067 | 66,987 | 250.0 | [66,237, 67,737] |
| 180° | 0.000 | 0 | 0.0 | Exactly 0 |

### 7.4 Special Handling for Deterministic Cases

At θ = 0° and θ = 180°, σ = 0. The acceptance criterion becomes exact:
- θ = 0°: All 1,000,000 measurements must be +1
- θ = 180°: All 1,000,000 measurements must be -1

Any deviation indicates a bug, not statistical fluctuation.

---

## 8. Potential Difficulties and Concerns

### 8.1 Axiom Correction (CRITICAL)

**Action Required:** The expectation value axiom must be corrected:

| Current | Proposed |
|---------|----------|
| ⟨O⟩ = 2 × vecDot(ψ, O) | ⟨O⟩ = vecDot(ψ, O) |

This change must propagate to:
- `src/qphysics.py`
- `proofs/QBP/Basic.lean`
- `paper/quaternion_physics.md`

### 8.2 Floating-Point Precision

For angles near 0° or 180°:
- cos θ approaches ±1
- P(+) approaches 0 or 1
- Use radians for trigonometric calculations
- Handle P = 0 and P = 1 as deterministic cases

### 8.3 Quaternion Construction

Experiment 01 used axis-aligned quaternions (i, j, k). For arbitrary angles:
```
ψ(θ) = sin(θ)·i + cos(θ)·k
```
The implementation must correctly construct and normalize these quaternions.

### 8.4 Numerical Verification

Before running statistical tests, verify analytically:
- Compute vecDot(ψ, O) for known quaternions
- Confirm it equals cos θ
- Catch implementation errors before statistical noise obscures them

### 8.5 Off-Axis States

This test is confined to the x-z plane. A more comprehensive test could include states with j components, verifying full 3D angular dependence.

---

## 9. Connection to Future Experiments

### 9.1 Bell's Theorem (Experiment 05)

This experiment validates single-particle angle dependence. Experiment 05 will test correlations between two entangled particles measured at different angles:

```
E(a, b) = -cos(θ_ab)
```

Getting angle dependence right here is essential groundwork.

### 9.2 General Angular Formula

The formula P(+) = (1 + cos θ)/2 is the foundation for all spin-1/2 measurements in QBP. Every subsequent experiment involving spin will depend on this result.

---

## 10. Summary

### What We Derived

From QBP axioms (with corrected expectation value formula):

**P(+) = (1 + cos θ)/2**

This matches the standard QM result P(+) = cos²(θ/2) exactly.

### What We Discovered

The factor of 2 in the original expectation value axiom produces invalid probabilities. This experiment serves as validation for the axiom correction.

### Why It Works

Quaternion algebra naturally encodes the geometry of spin-1/2 states. Pure unit quaternions parameterize S², the same space as the Bloch sphere. The dot product gives cos θ, directly measuring how much a state "points" in the measurement direction.

### What We Will Test

Nine angles from 0° to 180°, each with 1,000,000 trials, with angle-specific acceptance criteria based on binomial statistics.

---

## 11. References

1. Hamilton, W.R. (1844). "On Quaternions". *Proceedings of the Royal Irish Academy*.
2. Sakurai, J.J. (1994). *Modern Quantum Mechanics*. Addison-Wesley.
3. Altmann, S.L. (1986). *Rotations, Quaternions, and Double Groups*. Oxford University Press.
4. Bell, J.S. (1964). "On the Einstein Podolsky Rosen Paradox". *Physics Physique Физика*. 1(3): 195–200.
5. Griffiths, D.J.; Schroeter, D.F. (2018). *Introduction to Quantum Mechanics*. Cambridge University Press.

---

*Document produced through the Collaborative Theory Workflow*
*Synthesis by Claude from independent work by Claude and Gemini, evaluated by Bell*
