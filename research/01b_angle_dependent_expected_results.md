# Expected Results for Angle-Dependent Measurement (Ground Truth)

*Experiment 01b Ground Truth — Sprint 2*

*Originally produced through the Collaborative Theory Workflow (PR #116). Revised for Sprint 2 Phase 1 to incorporate lessons from Sprint 1 (Stern-Gerlach).*

---

## 1. Overview

This document derives the QBP prediction for measurement probability as a function of the angle θ between preparation and measurement axes. We demonstrate that quaternion algebra necessarily produces the quantum mechanical result P(+) = (1 + cos θ)/2, and we explain *why* this is so—not merely that it is.

**Key Result:** The corrected Measurement Postulate (see `paper/DESIGN_RATIONALE.md` §5.2) gives ⟨O⟩ = vecDot(ψ, O), which produces valid probabilities for all angles and matches standard quantum mechanics exactly.

**Cross-references:**
- Theory: `paper/DESIGN_RATIONALE.md` §6.4 (Sprint 2 theoretical extensions)
- Axioms: `paper/quaternion_physics.md` §2 (Axiomatic Framework)
- Implementation: `src/qphysics.py` (corrected in PR #117)

---

## 2. The Physical Situation

Imagine a Stern-Gerlach apparatus where we can rotate the magnet to any angle. We prepare a particle with spin along direction **n̂₁**, then measure along direction **n̂₂**, where the angle between them is θ.

**The question:** What is the probability of measuring spin-up (+1) along **n̂₂**?

**Standard QM answer:** P(+) = cos²(θ/2) = (1 + cos θ)/2

**Our task:** Derive this from QBP axioms alone, without importing the standard QM result.

---

## 3. Empirical Anchor

**Data type:** Formula-confirmed

### Key Measured Values

| Quantity | Measured Value | Uncertainty | Source | Year | DOI / Identifier |
|----------|---------------|-------------|--------|------|------------------|
| P(+) = cos²(θ/2) for spin-1/2 | Functional form confirmed across all angles | Exact agreement within statistical bounds | Sakurai, J.J. (textbook, citing extensive experimental literature) | 1994 | ISBN 0-201-53929-2 |
| Discrete binary outcomes at all angles | Only ±1 observed, never intermediate | Exact (qualitative) | Gerlach & Stern; all subsequent SG experiments | 1922– | Z. Phys. 9, 349–352 |

### Experimental Confidence

| Factor | Assessment |
|--------|------------|
| Replication status | The cos²(θ/2) angular dependence has been confirmed in countless experiments across electron, neutron, and atom systems. It is one of the most thoroughly verified predictions in quantum mechanics. |
| Measurement precision | For individual angle measurements: statistical precision scales as 1/√N. The functional form cos²(θ/2) is confirmed to high precision by fitting across many angles simultaneously. |
| Relevance to QBP test | Direct — QBP must derive the cos²(θ/2) formula from its axioms, not import it. The formula's status as experimentally confirmed means any QBP derivation is tested against reality, not just against standard QM theory. |

### What "Matching Reality" Means

The cos²(θ/2) formula is a **formula-confirmed** result: the functional form itself has been verified by extensive experiments. "Matching reality" means QBP must derive this exact functional form — P(+) = (1 + cos θ)/2 = cos²(θ/2) — from its axioms alone. The identity between these two expressions follows from the half-angle identity and is mathematically exact, not approximate.

At the implementation level, "matching" means: for each test angle θ, the simulation's measured frequency of spin-up outcomes must fall within 3σ of the predicted P(+) = cos²(θ/2) over N trials. The deterministic cases (θ = 0° gives P(+) = 1, θ = 180° gives P(+) = 0) must be exact — any deviation indicates a bug, not a statistical fluctuation.

### Null Results and Constraints

No known null results specific to this phenomenon. The cos²(θ/2) dependence has been universally confirmed for spin-1/2 systems. No experiment has reported a deviation from this formula for single-particle spin measurements.

---

## 4. The QBP Axioms (Corrected)

The following axioms govern the QBP measurement framework. Note that Axiom 3 was corrected after Experiment 01 (see `paper/DESIGN_RATIONALE.md` §5.2 for the correction history).

1. **Axiom 1 (State):** A spin state is a pure unit quaternion ψ (real part = 0, |ψ| = 1)
2. **Axiom 2 (Observable):** A measurement direction is a pure unit quaternion O
3. **Axiom 3 (Expectation Value):** ⟨O⟩ = vecDot(ψ, O) — *Corrected from 2 × vecDot*
4. **Axiom 4 (Born Rule):** P(+) = (1 + ⟨O⟩)/2, P(-) = (1 - ⟨O⟩)/2

**Why the correction was needed:** The original formula ⟨O⟩ = 2 × vecDot(ψ, O) produces expectation values in [-2, +2], which yields invalid probabilities (>1 or <0) for non-orthogonal configurations. The corrected formula produces expectation values in [-1, +1], guaranteed by the Cauchy-Schwarz inequality for unit vectors.

---

## 5. The Core Derivation

### 5.1 Representing Directions as Quaternions

A pure unit quaternion has the form:

```
q = ai + bj + ck,  where a² + b² + c² = 1
```

This is isomorphic to a unit vector in ℝ³: **v** = (a, b, c). The space of pure unit quaternions *is* the 2-sphere S²—every point corresponds to a direction in 3D space, and hence to a possible spin orientation.

### 5.2 Setup for Angle-Dependent Measurement

Following the convention from our simulation code:

- **Observable (O):** Measurement along the z-axis → `O = k = ⟨0, 0, 0, 1⟩`
- **State (ψ):** Prepared at angle θ from z-axis in the x-z plane → `ψ(θ) = sin(θ)·i + cos(θ)·k`

This gives vec(ψ) = (sin θ, 0, cos θ) and vec(O) = (0, 0, 1).

### 5.3 Computing the Vector Dot Product

```
vecDot(ψ, O) = (sin θ × 0) + (0 × 0) + (cos θ × 1) = cos θ
```

**Key insight:** The quaternion dot product of pure unit quaternions equals the cosine of the angle between them. This is not something we put in—it's a geometric property that Hamilton's algebra automatically provides.

### 5.4 Historical Note: The Factor-of-2 Correction

*This section documents how the axiom error was discovered. The correction has been applied — see `paper/DESIGN_RATIONALE.md` §5.2.*

The original Axiom 3 stated ⟨O⟩ = 2 × vecDot(ψ, O). This produced invalid probabilities:

| θ | cos θ | ⟨O⟩ = 2 cos θ | P(+) = (1 + ⟨O⟩)/2 | Valid? |
|---|-------|---------------|---------------------|--------|
| 0° | 1 | 2 | 1.5 | ❌ Invalid |
| 90° | 0 | 0 | 0.5 | ✓ Valid |
| 180° | -1 | -2 | -0.5 | ❌ Invalid |

**Why Experiment 01 didn't catch it:** For orthogonal states, vecDot(i, k) = 0, so 2 × 0 = 0 — the factor was invisible.

**Lesson learned:** Edge cases (aligned, anti-aligned) are essential test coverage.

### 5.5 The Corrected Formula

With the corrected Axiom 3 (⟨O⟩ = vecDot(ψ, O)):

| θ | cos θ | ⟨O⟩ = cos θ | P(+) = (1 + cos θ)/2 | Valid? |
|---|-------|-------------|----------------------|--------|
| 0° | 1 | 1 | 1.0 | ✓ |
| 90° | 0 | 0 | 0.5 | ✓ |
| 180° | -1 | -1 | 0.0 | ✓ |

### 5.6 Final Derivation

With the corrected axiom:

```
⟨O⟩ = vecDot(ψ, O) = cos θ

P(+) = (1 + ⟨O⟩)/2 = (1 + cos θ)/2
```

### 5.7 Verification Against Standard QM

Standard quantum mechanics gives: P(+) = cos²(θ/2)

Using the half-angle identity:
```
cos²(θ/2) = (1 + cos θ)/2
```

**The QBP prediction matches standard QM exactly.** ✓

### 5.8 The Rotation Formalism

For more complex scenarios, we can also express angle-dependent measurement using quaternion rotation operators. This is the approach documented in `paper/DESIGN_RATIONALE.md` §6.4.

**Rotation quaternion:** A rotation by angle θ about unit axis n̂ = (nx, ny, nz) is:
```
q = cos(θ/2) + sin(θ/2)(nx·i + ny·j + nz·k)
```

**Rotated observable:** O' = q·O·q⁻¹

**Example:** To rotate the z-axis observable by θ in the xz-plane:
- Rotation axis: y-axis, so q = cos(θ/2) + sin(θ/2)·j
- O_θ = q·k·q⁻¹ = cos(θ)·k + sin(θ)·i

This produces the same expectation value as the direct state construction in §5.2.

**Physical interpretation:** The rotation quaternion q has a non-zero real part — it's an *operator*, not a state. The half-angle θ/2 reflects the SU(2) double-cover of SO(3): rotating a spin state by 360° returns it to −ψ, not +ψ.

### 5.9 Simplified Code Example

For readers who want to understand the core calculation (following the pattern from Experiment 01):

```python
import numpy as np

def angle_measurement_probability(theta_degrees):
    """
    Calculate P(+) for measuring a state at angle θ from the z-axis.

    Physical setup: Particle prepared with spin tilted θ from z-axis,
    then measured along z-axis.
    """
    theta = np.radians(theta_degrees)

    # State quaternion: ψ(θ) = sin(θ)·i + cos(θ)·k
    # Physical meaning: spin direction tilted θ from z toward x
    psi = np.array([0, np.sin(theta), 0, np.cos(theta)])  # [real, i, j, k]

    # Observable: measurement along z-axis
    O_z = np.array([0, 0, 0, 1])  # Pure quaternion k

    # Expectation value = dot product of imaginary parts
    vec_psi = psi[1:4]  # [sin θ, 0, cos θ]
    vec_O = O_z[1:4]    # [0, 0, 1]
    expectation = np.dot(vec_psi, vec_O)  # = cos θ

    # Born rule
    P_up = (1 + expectation) / 2  # = (1 + cos θ)/2 = cos²(θ/2)

    return P_up

# Verify key angles
print(f"θ=0°:   P(+) = {angle_measurement_probability(0):.3f}")   # → 1.000
print(f"θ=60°:  P(+) = {angle_measurement_probability(60):.3f}")  # → 0.750
print(f"θ=90°:  P(+) = {angle_measurement_probability(90):.3f}")  # → 0.500
print(f"θ=180°: P(+) = {angle_measurement_probability(180):.3f}") # → 0.000
```

---

## 6. Why Does This Work?

It is not enough to show *that* quaternions give the right answer. We must understand *why*.

### 6.1 The Geometry of Spin States

In standard QM, spin-1/2 states live in a 2D complex Hilbert space (ℂ²). The space of pure states is the Bloch sphere—a 2-sphere S².

In QBP, spin states are pure unit quaternions. The space of pure unit quaternions is *also* S² (embedded in 3D imaginary quaternion space).

**These are the same space.** The quaternion formulation is not an approximation—it is an alternative parameterization of the same geometric object.

### 6.2 Why Cos θ Appears

The dot product of unit vectors gives cos θ—this is the projection of one direction onto another. For spin-1/2, measuring a state prepared along **n̂₁** using an apparatus aligned with **n̂₂** asks: "How much does this state 'point' in the measurement direction?"

The quaternion formulation makes this geometric interpretation manifest. The answer is cos θ because that is literally what "projection" means in Euclidean geometry.

### 6.3 Why (1 + cos θ)/2?

The raw projection cos θ ranges from -1 to +1, but probabilities must be non-negative. The Born rule P(+) = (1 + ⟨O⟩)/2 is the unique linear map that:

- Maps ⟨O⟩ = +1 (fully aligned) → P(+) = 1
- Maps ⟨O⟩ = -1 (anti-aligned) → P(+) = 0
- Maps ⟨O⟩ = 0 (orthogonal) → P(+) = 0.5

### 6.4 The Deep Connection

Hamilton quaternions encode SO(3) rotations. Spin-1/2 transforms under SU(2), which is the double cover of SO(3). The mathematics is connected at a fundamental level.

**The QBP framework works because quaternions and spin-1/2 quantum mechanics describe the same underlying geometric structure.**

---

## 7. Edge Cases and Physical Interpretation

### 7.1 θ = 0° (Aligned)

- vecDot(ψ, O) = cos(0°) = 1
- ⟨O⟩ = 1
- P(+) = 1.0

**Physical meaning:** Measuring spin along the preparation axis always gives the prepared value. Complete certainty.

### 7.2 θ = 90° (Orthogonal)

- vecDot(ψ, O) = cos(90°) = 0
- ⟨O⟩ = 0
- P(+) = 0.5

**Physical meaning:** The state has no "preference" for either outcome along the perpendicular axis. Maximum uncertainty. (This is Experiment 01.)

### 7.3 θ = 180° (Anti-aligned)

- vecDot(ψ, O) = cos(180°) = -1
- ⟨O⟩ = -1
- P(+) = 0.0

**Physical meaning:** Measuring along the opposite direction always gives the opposite result. Complete certainty of spin-down.

### 7.4 θ = 60°

- vecDot(ψ, O) = cos(60°) = 0.5
- ⟨O⟩ = 0.5
- P(+) = 0.75

**Physical meaning:** The state "partially points" in the measurement direction, giving a 3:1 bias toward spin-up.

---

## 8. Quantitative Predictions & Acceptance Criteria

### 8.1 Test Angles

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

### 8.2 Statistical Parameters

For N = 1,000,000 trials per angle:

- **Expected count:** μ = N × P(+)
- **Standard deviation:** σ = √(N × P(+) × (1 - P(+)))
- **Acceptance criterion:** |Measured count - μ| ≤ 3σ

**Note:** σ varies with angle. At θ = 90°, σ = 500. At θ = 0° or 180°, σ = 0 (deterministic).

### 8.3 Detailed Acceptance Table

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

### 8.4 Special Handling for Deterministic Cases

At θ = 0° and θ = 180°, σ = 0. The acceptance criterion becomes exact:
- θ = 0°: All 1,000,000 measurements must be +1
- θ = 180°: All 1,000,000 measurements must be -1

Any deviation indicates a bug, not statistical fluctuation.

---

## 9. Potential Difficulties and Concerns

### 9.1 Axiom Correction (COMPLETED)

**Status:** ✅ Corrected in Sprint 1 post-analysis.

The expectation value axiom was corrected from ⟨O⟩ = 2 × vecDot(ψ, O) to ⟨O⟩ = vecDot(ψ, O).

**Propagation verified:**
- ✅ `src/qphysics.py` — PR #117
- ✅ `proofs/QBP/Basic.lean` — PR #118
- ✅ `paper/quaternion_physics.md` — PR #155

See `paper/DESIGN_RATIONALE.md` §5.2 for full correction history.

### 9.2 Floating-Point Precision

For angles near 0° or 180°:
- cos θ approaches ±1
- P(+) approaches 0 or 1
- Use radians for trigonometric calculations
- Handle P = 0 and P = 1 as deterministic cases

### 9.3 Quaternion Construction

Experiment 01 used axis-aligned quaternions (i, j, k). For arbitrary angles:
```
ψ(θ) = sin(θ)·i + cos(θ)·k
```
The implementation must correctly construct and normalize these quaternions.

### 9.4 Numerical Verification

Before running statistical tests, verify analytically:
- Compute vecDot(ψ, O) for known quaternions
- Confirm it equals cos θ
- Catch implementation errors before statistical noise obscures them

### 9.5 Off-Axis States

This test is confined to the x-z plane. A more comprehensive test could include states with j components, verifying full 3D angular dependence.

---

## 10. Connection to Future Experiments

### 10.1 Bell's Theorem (Experiment 05)

This experiment validates single-particle angle dependence. Experiment 05 will test correlations between two entangled particles measured at different angles:

```
E(a, b) = -cos(θ_ab)
```

Getting angle dependence right here is essential groundwork.

### 10.2 General Angular Formula

The formula P(+) = (1 + cos θ)/2 is the foundation for all spin-1/2 measurements in QBP. Every subsequent experiment involving spin will depend on this result.

---

## 11. Summary

### What We Derived

From QBP axioms (with corrected expectation value formula):

**P(+) = (1 + cos θ)/2 = cos²(θ/2)**

This matches the standard QM result exactly.

### Key Insights

1. **Geometric foundation:** Quaternion dot product = cos θ because pure unit quaternions parameterize S², the same space as the Bloch sphere.

2. **Axiom validation:** The factor-of-2 correction (discovered here, applied in Sprint 1) is essential for valid probabilities at all angles.

3. **Rotation formalism:** The q·O·q⁻¹ rotation with half-angle reflects SU(2) structure.

### What Phase 2 Will Test

Nine angles from 0° to 180°, each with 1,000,000 trials:
- Edge cases: 0° (aligned), 90° (orthogonal), 180° (anti-aligned)
- Intermediate angles: 30°, 45°, 60°, 120°, 135°, 150°

All must pass the 3σ acceptance criterion (see §8.3).

---

## 12. Prediction Classification

| Prediction | Type | Standard QM | Notes |
|------------|------|-------------|-------|
| P(+) = cos²(θ/2) = (1 + cos θ)/2 | Validation | cos²(θ/2) | Identical to QM |
| P(-) = sin²(θ/2) = (1 - cos θ)/2 | Validation | sin²(θ/2) | Identical to QM |
| Deterministic at θ=0°, 180° | Validation | Same | Aligned/anti-aligned cases |

### Classification Summary

**Validation:** This experiment confirms QBP reproduces standard quantum mechanics for angle-dependent spin measurement. The formula P(+) = cos²(θ/2) is identical to the standard QM result derived from spinor theory.

**Novel predictions:** None for this experiment. The angle-dependent probability formula is a textbook QM result that QBP must reproduce to be viable.

### Implications

Experiment 01b extends Experiment 01's validation to arbitrary angles. Together, they establish that QBP correctly handles all single-particle spin-1/2 measurements. This is *mathematically necessary* because quaternions (ℍ) are isomorphic to the Pauli algebra underlying SU(2).

For QBP to make novel predictions, we must look beyond single-particle systems — possibly to entanglement (Experiment 05: Bell's Theorem), multi-particle statistics, or regimes where octonion structure becomes relevant. See #167 for ongoing research.

---

## 13. Phase 2 Acceptance Criteria

The following criteria must be met for Phase 2 (Implementation) to pass:

- [ ] **AC:** Rotation function implemented in `src/qphysics.py`
- [ ] **AC:** All 9 test angles pass within 3σ of predicted P(+)
- [ ] **AC:** Deterministic cases (θ=0°, θ=180°) pass exactly
- [ ] **AC:** Results saved to CSV in `results/01b_angle_dependent/`
- [ ] **AC:** Physics validation tests pass in CI

---

## 14. References

1. Hamilton, W.R. (1844). "On Quaternions". *Proceedings of the Royal Irish Academy*.
2. Sakurai, J.J. (1994). *Modern Quantum Mechanics*. Addison-Wesley.
3. Altmann, S.L. (1986). *Rotations, Quaternions, and Double Groups*. Oxford University Press.
4. Bell, J.S. (1964). "On the Einstein Podolsky Rosen Paradox". *Physics Physique Физика*. 1(3): 195–200.
5. Griffiths, D.J.; Schroeter, D.F. (2018). *Introduction to Quantum Mechanics*. Cambridge University Press.

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2026-02-04 | Original via Collaborative Theory Workflow (PR #116) |
| 2.0 | 2026-02-06 | Sprint 2 Phase 1 rework: updated axioms to corrected version, added rotation formalism, code example, Phase 2 acceptance criteria, cross-references |

*Original synthesis by Claude from independent work by Claude and Gemini, evaluated by Bell*
*Sprint 2 revision by Claude with Herschel coordination*
