# Expected Results for Angle-Dependent Measurement (Ground Truth)

## Overview

This document derives the QBP prediction for measurement probability as a function of the angle between preparation and measurement axes. We will show that quaternion algebra *necessarily* produces the quantum mechanical result P(+) = (1 + cos θ)/2, and we will explain *why* this is so—not merely demonstrate that it is.

---

## 1. The Physical Situation

Imagine a Stern-Gerlach apparatus where we can rotate the magnet to any angle. We prepare a particle with spin along direction **n̂₁**, then measure along direction **n̂₂**, where the angle between them is θ.

**The question:** What is the probability of measuring spin-up (+1) along **n̂₂**?

**Standard QM answer:** P(+) = cos²(θ/2)

**Our task:** Derive this from QBP axioms alone, without importing the standard QM result.

---

## 2. The QBP Axioms (Restated)

1. **State:** A spin state is a pure unit quaternion ψ (real part = 0, |ψ| = 1)
2. **Observable:** A measurement direction is a pure unit quaternion O
3. **Expectation Value:** ⟨O⟩ = 2 × vecDot(ψ, O)
4. **Born Rule:** P(+) = (1 + ⟨O⟩)/2

---

## 3. The Core Derivation

### 3.1 Representing Directions as Quaternions

A pure unit quaternion has the form:

```
q = ai + bj + ck,  where a² + b² + c² = 1
```

This is isomorphic to a unit vector in ℝ³: **v** = (a, b, c). This is not a coincidence—Hamilton discovered quaternions precisely because they encode 3D rotations.

**Key insight:** The space of pure unit quaternions *is* the 2-sphere S². Every point on S² corresponds to a direction in 3D space, and hence to a possible spin orientation.

### 3.2 The Dot Product of Pure Quaternions

For two pure unit quaternions:
- ψ = ψᵢi + ψⱼj + ψₖk  (the prepared state, pointing along **n̂₁**)
- O = Oᵢi + Oⱼj + Oₖk  (the measurement axis, pointing along **n̂₂**)

The vector dot product is:

```
vecDot(ψ, O) = ψᵢOᵢ + ψⱼOⱼ + ψₖOₖ
```

But this is simply the Euclidean dot product of the corresponding 3D vectors:

```
vecDot(ψ, O) = n̂₁ · n̂₂ = |n̂₁||n̂₂|cos θ = cos θ
```

**This is the critical step.** The quaternion dot product of pure unit quaternions equals the cosine of the angle between them. This is not something we put in—it's a geometric property of quaternions that Hamilton's algebra automatically provides.

### 3.3 Deriving the Probability

Now we apply the QBP axioms:

**Step 1:** Expectation value
```
⟨O⟩ = 2 × vecDot(ψ, O) = 2 cos θ
```

**Wait.** This gives ⟨O⟩ = 2 cos θ, which ranges from -2 to +2. But expectation values for a ±1 observable should range from -1 to +1.

**This reveals something important about the axioms.** Let me re-examine.

### 3.4 Re-examining the Expectation Value Formula

Looking back at Experiment 01, the expectation value formula was stated as:
```
⟨O⟩ = 2 × vecDot(ψ, O)
```

For orthogonal quaternions (θ = 90°), vecDot = 0, so ⟨O⟩ = 0. ✓

But for aligned quaternions (θ = 0°), vecDot = 1, so ⟨O⟩ = 2. This would give P(+) = (1 + 2)/2 = 1.5, which is nonsense.

**There are two possibilities:**

**Possibility A:** The formula should be ⟨O⟩ = vecDot(ψ, O) without the factor of 2.

Let's check: For θ = 90°, ⟨O⟩ = 0, P(+) = 0.5. ✓
For θ = 0°, ⟨O⟩ = 1, P(+) = 1.0. ✓
For θ = 180°, ⟨O⟩ = -1, P(+) = 0.0. ✓

This works! But it contradicts what was stated in Experiment 01.

**Possibility B:** The "2" in the original formula compensates for a different normalization convention.

Looking at the Experiment 01 ground truth document more carefully:
```
⟨O_z⟩ = 2 * vecDot(ψ, O_z) = 2 * 0 = 0
```

The factor of 2 didn't matter because vecDot was 0. We never tested a case where it would matter!

**This is a significant finding.** The axiom as stated appears to have an error, or there's a normalization convention I'm missing. Let me investigate further.

### 3.5 Resolving the Factor of 2

After reflection, I believe the issue is this: the formula ⟨O⟩ = 2 × vecDot(ψ, O) assumes that ψ and O are *not* unit quaternions, but rather have magnitude 1/√2 or some other normalization.

However, if we require ψ and O to be **unit** pure quaternions (|ψ| = |O| = 1), then the correct formula must be:

```
⟨O⟩ = vecDot(ψ, O) = cos θ
```

**I will proceed with this corrected formula**, noting that this is either:
- A correction to the axioms, or
- An implicit normalization that wasn't made explicit

This is exactly the kind of issue that careful theory work should uncover.

### 3.6 The Final Derivation

With the corrected understanding:

```
⟨O⟩ = vecDot(ψ, O) = cos θ

P(+) = (1 + ⟨O⟩)/2 = (1 + cos θ)/2
```

### 3.7 Verification Against Standard QM

Standard quantum mechanics gives: P(+) = cos²(θ/2)

Using the half-angle identity:
```
cos²(θ/2) = (1 + cos θ)/2
```

**The QBP prediction matches standard QM exactly.** ✓

---

## 4. Why Does This Work? (The Deeper Question)

It's not enough to show *that* quaternions give the right answer. We should understand *why*.

### 4.1 The Geometry of Spin States

In standard QM, spin-1/2 states live in a 2D complex Hilbert space (C²). The space of pure states is the Bloch sphere—a 2-sphere S².

In QBP, spin states are pure unit quaternions. The space of pure unit quaternions is *also* a 2-sphere S² (embedded in 3D imaginary quaternion space).

**These are the same space.** The quaternion formulation isn't an approximation or analogy—it's an alternative parameterization of the same geometric object.

### 4.2 Why Cos θ Appears

The dot product of unit vectors gives cos θ. This is the projection of one direction onto another—how much of **n̂₁** points along **n̂₂**.

For spin-1/2, when you measure a state prepared along **n̂₁** using an apparatus aligned with **n̂₂**, you're asking: "How much does this state 'point' in the measurement direction?"

The quaternion formulation makes this geometric interpretation manifest. The answer is cos θ because that's literally what "projection" means in Euclidean geometry.

### 4.3 Why (1 + cos θ)/2 and Not Just cos θ?

The raw projection cos θ ranges from -1 to +1. But probabilities must be non-negative.

The Born rule P(+) = (1 + ⟨O⟩)/2 is the unique linear map that:
- Maps ⟨O⟩ = +1 (fully aligned) to P(+) = 1
- Maps ⟨O⟩ = -1 (anti-aligned) to P(+) = 0
- Maps ⟨O⟩ = 0 (orthogonal) to P(+) = 1/2

This is the only sensible probability assignment given that ⟨O⟩ represents "how much the state points in the measurement direction."

### 4.4 The Remarkable Coincidence (Or Is It?)

It might seem remarkable that:
1. Pure unit quaternions parameterize S²
2. The Bloch sphere for spin-1/2 is also S²
3. The quaternion dot product gives cos θ
4. The QM probability formula involves cos θ

But this is not coincidence. Hamilton quaternions encode SO(3) rotations, and spin-1/2 transforms under SU(2), which is the double cover of SO(3). The mathematics is connected at a deep level.

**The QBP framework works because quaternions and spin-1/2 quantum mechanics are describing the same underlying geometric structure.**

---

## 5. Edge Cases and Limiting Behavior

### 5.1 θ = 0° (Aligned)

- State: ψ points along **n̂**
- Measurement: O points along **n̂** (same direction)
- vecDot(ψ, O) = cos(0°) = 1
- ⟨O⟩ = 1
- P(+) = (1 + 1)/2 = 1.0

**Physical meaning:** Measuring spin along the same axis it was prepared always gives the prepared value. 100% certainty.

### 5.2 θ = 90° (Orthogonal)

- vecDot(ψ, O) = cos(90°) = 0
- ⟨O⟩ = 0
- P(+) = (1 + 0)/2 = 0.5

**Physical meaning:** The state has no "preference" for either outcome along the perpendicular axis. Maximum uncertainty. (This is Experiment 01.)

### 5.3 θ = 180° (Anti-aligned)

- vecDot(ψ, O) = cos(180°) = -1
- ⟨O⟩ = -1
- P(+) = (1 + (-1))/2 = 0.0

**Physical meaning:** Measuring along the opposite direction always gives the opposite result. 100% certainty of spin-down.

### 5.4 θ = 60° (A Non-trivial Case)

- vecDot(ψ, O) = cos(60°) = 0.5
- ⟨O⟩ = 0.5
- P(+) = (1 + 0.5)/2 = 0.75

**Physical meaning:** The state "partially points" in the measurement direction, giving a 3:1 bias toward spin-up.

### 5.5 θ = 120°

- vecDot(ψ, O) = cos(120°) = -0.5
- ⟨O⟩ = -0.5
- P(+) = (1 + (-0.5))/2 = 0.25

**Physical meaning:** The state "partially points away" from the measurement direction, giving a 1:3 bias toward spin-down.

---

## 6. Test Angles and Acceptance Criteria

### 6.1 Selected Test Angles

| θ (degrees) | θ (radians) | cos θ | Expected P(+) | Why Test This Angle |
|-------------|-------------|-------|---------------|---------------------|
| 0° | 0 | 1.000 | 1.000 | Perfect alignment |
| 30° | π/6 | 0.866 | 0.933 | Tests smooth variation |
| 45° | π/4 | 0.707 | 0.854 | Common angle, irrational cos |
| 60° | π/3 | 0.500 | 0.750 | Clean fractional value |
| 90° | π/2 | 0.000 | 0.500 | Maximum uncertainty (Exp 01) |
| 120° | 2π/3 | -0.500 | 0.250 | Tests negative expectation |
| 135° | 3π/4 | -0.707 | 0.146 | Symmetry with 45° |
| 150° | 5π/6 | -0.866 | 0.067 | Near anti-alignment |
| 180° | π | -1.000 | 0.000 | Perfect anti-alignment |

### 6.2 Acceptance Criteria

For each angle, we run N = 1,000,000 trials and count spin-up outcomes.

**Expected count:** μ = N × P(+)

**Standard deviation:** σ = √(N × P(+) × P(-)) = √(N × P(+) × (1 - P(+)))

**Note:** σ varies with angle! At θ = 90°, σ = 500. At θ = 0° or 180°, σ → 0.

**Acceptance criterion:** |Measured count - μ| ≤ 3σ

### 6.3 Detailed Acceptance Table

| θ | P(+) | P(-) | μ | σ | 3σ Range |
|---|------|------|---|---|----------|
| 0° | 1.000 | 0.000 | 1,000,000 | 0.0 | Exactly 1,000,000 |
| 30° | 0.933 | 0.067 | 933,013 | 250.0 | [932,263, 933,763] |
| 45° | 0.854 | 0.146 | 853,553 | 353.6 | [852,493, 854,614] |
| 60° | 0.750 | 0.250 | 750,000 | 433.0 | [748,701, 751,299] |
| 90° | 0.500 | 0.500 | 500,000 | 500.0 | [498,500, 501,500] |
| 120° | 0.250 | 0.750 | 250,000 | 433.0 | [248,701, 251,299] |
| 135° | 0.146 | 0.854 | 146,447 | 353.6 | [145,386, 147,507] |
| 150° | 0.067 | 0.933 | 66,987 | 250.0 | [66,237, 67,737] |
| 180° | 0.000 | 1.000 | 0 | 0.0 | Exactly 0 |

### 6.4 Special Handling for θ = 0° and θ = 180°

At these angles, P(+) = 1 or P(+) = 0, so σ = 0. The acceptance criterion becomes exact:
- θ = 0°: All 1,000,000 measurements must be +1
- θ = 180°: All 1,000,000 measurements must be -1

Any deviation indicates a bug, not statistical fluctuation.

---

## 7. Potential Difficulties and Concerns

### 7.1 The Factor of 2 Issue (CRITICAL)

As noted in Section 3.5, the axiom ⟨O⟩ = 2 × vecDot(ψ, O) appears inconsistent with the requirement that ⟨O⟩ ∈ [-1, +1]. This needs resolution before implementation.

**Recommended action:** Review the axioms in `proofs/QBP/Basic.lean` and clarify the normalization convention. Either:
- Remove the factor of 2, or
- Specify that states/observables are normalized differently

### 7.2 Floating-Point Precision

For angles near 0° or 180°, cos θ approaches ±1, and P(+) approaches 0 or 1. The simulation must handle:
- Accurate trigonometric computation (use radians, not degrees)
- Probability values very close to 0 or 1
- The RNG must correctly handle P = 0 and P = 1 as deterministic cases

### 7.3 Quaternion Construction for Arbitrary Angles

Experiment 01 used axis-aligned quaternions (i, j, k). For arbitrary angles, we need to construct quaternions pointing in arbitrary directions.

**Approach:** If **n̂** = (sin φ cos λ, sin φ sin λ, cos φ) in spherical coordinates, then:
```
ψ = sin(φ)cos(λ)·i + sin(φ)sin(λ)·j + cos(φ)·k
```

The implementation must correctly construct these quaternions.

### 7.4 Numerical Test of the Formula

Before running the full statistical test, verify the formula analytically:
- Compute vecDot(ψ, O) for two known quaternions at a known angle
- Confirm it equals cos θ
- This catches implementation errors before the statistical noise obscures them

### 7.5 What If the Test Fails?

If the simulation results deviate by more than 3σ consistently, possible causes:
1. **Bug in quaternion construction** - Verify unit magnitude
2. **Bug in vecDot implementation** - Test against known values
3. **RNG issues** - Test with different seeds
4. **Axiom error** - The normalization factor issue mentioned above

A systematic pattern of failure (e.g., all angles off by a constant factor) would indicate an axiom problem.

---

## 8. Connection to Bell's Theorem (Looking Ahead)

This experiment validates single-particle angle dependence. Experiment 05 (Bell's Theorem) will test whether the QBP framework correctly handles *correlations* between two particles measured at different angles.

The key formula there will involve:
```
E(a, b) = -cos(θ_ab)
```

where θ_ab is the angle between measurement directions **a** and **b** for an entangled pair.

Getting Experiment 02 right is essential groundwork—if single-particle angle dependence is wrong, Bell correlations will certainly be wrong.

---

## 9. Summary

### What We Derived
From QBP axioms, we derived: **P(+) = (1 + cos θ)/2**

This matches the standard QM result P(+) = cos²(θ/2) exactly.

### Why It Works
Quaternion algebra naturally encodes the geometry of spin-1/2 states. The dot product of pure unit quaternions gives cos θ, which directly measures how much a state "points" in the measurement direction.

### What We Discovered
The factor of 2 in the expectation value formula needs clarification. For unit pure quaternions, it appears the formula should be ⟨O⟩ = vecDot(ψ, O), not ⟨O⟩ = 2 × vecDot(ψ, O).

### What We Will Test
Nine angles from 0° to 180°, each with 1,000,000 trials, with angle-specific acceptance criteria based on the binomial standard deviation.

---

## 10. References

1. Hamilton, W.R. (1844). "On Quaternions". Proceedings of the Royal Irish Academy.
2. Sakurai, J.J. (1994). *Modern Quantum Mechanics*. Addison-Wesley. Chapter 1 (Stern-Gerlach).
3. Altmann, S.L. (1986). *Rotations, Quaternions, and Double Groups*. Oxford University Press.
4. Bell, J.S. (1964). "On the Einstein Podolsky Rosen Paradox". Physics Physique Физика. 1 (3): 195–200.

---

*Document prepared by Claude for the QBP Project*
*This is a ground truth document for Phase 1 of Experiment 02: Angle-Dependent Measurement*
