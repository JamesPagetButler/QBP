# QBP Axiom Justifications

This document consolidates the first-principles justifications for each QBP axiom. Every axiom must be derivable from mathematical or physical necessity alone — not reverse-engineered from simulation results.

**Sources:**
- `paper/DESIGN_RATIONALE.md` (Sections 4, 5.2, 6.3, 8.3)
- `research/01b_angle_dependent_proof_review.md`
- `proofs/QBP/Basic.lean`

---

## Axiom 1: States as Pure Unit Quaternions

```lean
-- proofs/QBP/Basic.lean:10
def isUnitQuaternion (q : Q) : Prop := q.normSq = 1

-- proofs/QBP/Basic.lean:13
def isPureQuaternion (q : Q) : Prop := q.re = 0
```

A valid spin state `ψ` must satisfy both conditions: `isPureQuaternion ψ` AND `isUnitQuaternion ψ`.

### Derivation

**Unit norm (|ψ|² = 1):** Normalization is fundamental to probability interpretation. The Born rule produces probabilities from inner products of states, which requires `⟨ψ|ψ⟩ = 1` so that total probability sums to 1. This constraint is shared with standard QM and is not specific to quaternions.

**Pure quaternion (Re(ψ) = 0):** Pure quaternions have the form `ψ = ai + bj + ck` with zero real part. This restricts states to a 2-sphere S² embedded in the imaginary part of ℍ, which is exactly the Bloch sphere of spin-1/2 states.

The constraint `Re(ψ) = 0` distinguishes states from rotation operators:
- **States** are pure unit quaternions: points on S² (the Bloch sphere)
- **Rotation operators** are general unit quaternions: `q = cos(θ/2) + sin(θ/2)n̂` with `Re(q) ≠ 0` in general

This separation is physically meaningful: states transform under SU(2), while rotations act as SU(2) group elements.

### Intuition

A pure unit quaternion is a unit vector in ℝ³ (the imaginary subspace of ℍ). In QBP, this vector represents the spin direction. The quaternion basis elements `i`, `j`, `k` correspond to spin eigenstates along the x, y, and z axes respectively.

---

## Axiom 2: Observables as Pure Quaternions

```lean
-- proofs/QBP/Basic.lean:19-21
def SPIN_X : Q := ⟨0, 1, 0, 0⟩
def SPIN_Y : Q := ⟨0, 0, 1, 0⟩
def SPIN_Z : Q := ⟨0, 0, 0, 1⟩
```

### Derivation

An observable `O = ai + bj + ck` (pure quaternion) corresponds to a measurement direction in 3D space. This follows Hamilton's original insight (1843): pure quaternions are isomorphic to vectors in ℝ³.

The Pauli correspondence makes this precise:

| QBP Observable | Pauli Matrix |
|----------------|-------------|
| `i` | `-iσₓ` |
| `j` | `-iσᵧ` |
| `k` | `-iσ_z` |

where `i` on the left is the quaternion basis element and `i` on the right is the complex unit. A general pure quaternion `O = ai + bj + ck` corresponds to the Hermitian operator `aσₓ + bσᵧ + cσ_z`.

More precisely, this is a **Lie algebra isomorphism**: the imaginary quaternions Im(ℍ) with the commutator bracket form a Lie algebra isomorphic to su(2), and the Pauli matrices provide a representation of this algebra. The commutation relations are preserved: `[i, j] = 2k` corresponds to `[σₓ, σᵧ] = 2iσ_z`. QBP observables *are* Pauli operators in a different parameterization. A measurement direction is a point on S², which is the space of pure unit quaternions. The requirement `Re(O) = 0` ensures the observable represents a spatial direction, not a rotation.

### Intuition

Asking "what is the spin along direction n̂?" is asking for the component of the state vector along `n̂`. Pure quaternions are exactly the vectors available in quaternion space.

---

## Axiom 3: Measurement via vecDot (Expectation Value)

```lean
-- proofs/QBP/Basic.lean:44-47
def expectationValue (ψ O : Q) : ℝ :=
  let ψ_vec := vecPart ψ
  let O_vec := vecPart O
  vecDot ψ_vec O_vec
```

### Derivation

The expectation value `⟨O⟩ = vecDot(ψ, O)` gives the dot product of the vector parts of the state and observable. For pure unit quaternions, this equals `cos(θ)` where θ is the angle between ψ and O in ℝ³.

**Why vecDot (without the factor of 2):**

The original formula `⟨O⟩ = 2 × vecDot(ψ, O)` was proposed early in the project but violates probability bounds. Here is the mathematical argument:

1. The Born rule requires `P(+) = (1 + ⟨O⟩)/2 ∈ [0, 1]`
2. This requires `⟨O⟩ ∈ [-1, +1]`
3. With the factor of 2: `⟨O⟩ = 2 × vecDot(ψ, O)`, which can reach ±2 for aligned states
4. Without the factor: `⟨O⟩ = vecDot(ψ, O)`, bounded by Cauchy-Schwarz

**Cauchy-Schwarz guarantee:** For pure unit quaternions ψ and O, their vector parts are unit vectors in ℝ³. The dot product of unit vectors satisfies `|vecDot(ψ, O)| ≤ ||ψ_im|| · ||O_im|| = 1 · 1 = 1`. This ensures valid probabilities for all configurations.

**The correction is mathematically forced, not empirically fitted.** The simulation revealed the bug (PR #116 produced probabilities > 1 for non-orthogonal cases), but the correct axiom `⟨O⟩ = vecDot(ψ, O)` is derivable from the probability bound alone.

### Worked Example: Factor-of-2 Correction

Consider spin-z state `ψ = k` measured at 60° from z-axis:

**With factor of 2 (incorrect):**
```
O_60° has vecDot(k, O_60°) = cos(60°) = 0.5
⟨O⟩ = 2 × 0.5 = 1.0
P(+) = (1 + 1.0)/2 = 1.0  ← Barely valid at this angle
```

At 30° it would give:
```
⟨O⟩ = 2 × cos(30°) = 2 × 0.866 = 1.732
P(+) = (1 + 1.732)/2 = 1.366  ← INVALID (> 1)
```

**Without factor of 2 (correct):**
```
⟨O⟩ = vecDot(k, O_30°) = cos(30°) = 0.866
P(+) = (1 + 0.866)/2 = 0.933  ← Valid probability ✓
```

### Intuition

The expectation value answers: "how aligned is the spin with the measurement axis?" When perfectly aligned (θ = 0), the dot product is 1 → certain spin-up. When perpendicular (θ = 90°), the dot product is 0 → 50/50. When anti-aligned (θ = 180°), the dot product is -1 → certain spin-down.

---

## Born Rule: P(+) = (1 + ⟨O⟩) / 2

```lean
-- proofs/QBP/Basic.lean:50-53
noncomputable def probUp (ψ O : Q) : ℝ := (1 + expectationValue ψ O) / 2
noncomputable def probDown (ψ O : Q) : ℝ := (1 - expectationValue ψ O) / 2
```

### Derivation

The Born rule `P(+) = (1 + ⟨O⟩)/2` is the **unique** linear map from `[-1, +1]` to `[0, 1]` satisfying the boundary conditions `f(+1) = 1` (aligned → certain spin-up) and `f(-1) = 0` (anti-aligned → certain spin-down):

| Condition | ⟨O⟩ | P(+) | Physical meaning |
|-----------|------|------|-----------------|
| Aligned | +1 | 1 | Certain spin-up |
| Anti-aligned | -1 | 0 | Certain spin-down |
| Orthogonal | 0 | 0.5 | Maximally uncertain (consequence) |

**Uniqueness proof:** Any linear function `f(x) = ax + b` with `f(+1) = 1` and `f(-1) = 0` gives `a + b = 1` and `-a + b = 0`, so `a = b = 1/2`, yielding `f(x) = (1 + x)/2`. The orthogonal case `f(0) = 0.5` follows as a consequence, not an independent constraint.

**Why linearity?** While non-linear maps from `[-1, +1]` to `[0, 1]` satisfying the same boundary conditions are possible (e.g., `f(x) = (1 + x)²/4`), the linear form is the simplest and most natural choice. It is also the only form consistent with the standard QM expectation value formula, where probabilities depend linearly on the expectation value.

The complementary probability `P(-) = (1 - ⟨O⟩)/2` ensures `P(+) + P(-) = 1`.

### Connection to Standard QM

In standard QM, the probability of measuring eigenvalue +1 for observable `σ̂` in state `|ψ⟩` is:

```
P(+) = ⟨ψ|(1 + σ̂)/2|ψ⟩ = (1 + ⟨ψ|σ̂|ψ⟩)/2
```

The QBP Born rule is algebraically identical, with `vecDot(ψ, O)` replacing `⟨ψ|σ̂|ψ⟩`.

---

## Summary: Axiom-First Principle

> "Would this axiom be chosen if we had never run the simulation?"

| Axiom | First-Principles Basis | Answer |
|-------|----------------------|--------|
| State normalization | Probability conservation (∑P = 1) | YES |
| Observable as pure quaternion | Geometric necessity (S² ↔ Im(ℍ) ∩ S³) | YES |
| Expectation = vecDot | Probability bounds + Cauchy-Schwarz | YES* |
| Born rule (1 + ⟨O⟩)/2 | Unique linear map with correct boundaries | YES |

*\*Axiom 3 note: The simulation revealed that the original factor-of-2 formula produced invalid probabilities (PR #116). However, the correct formula `⟨O⟩ = vecDot(ψ, O)` is derivable from first principles alone — the probability bound `P ∈ [0, 1]` combined with Cauchy-Schwarz forces this form. The simulation discovered the bug; mathematics provides the fix.*

All axioms are derivable from first principles. The factor-of-2 correction discovered during Experiment 01b development was a bug fix — the original violated probability bounds for non-orthogonal configurations.

---

## Scope: Single-Particle Systems

**Important caveat:** These axioms apply to single-particle spin-1/2 systems only. For this scope, QBP predictions necessarily match standard quantum mechanics because the quaternion algebra is isomorphic to the Pauli algebra underlying SU(2). This is expected, not a novel validation. The real test of QBP's predictive power comes with multi-particle systems (e.g., Experiment 05: Bell's Theorem) where the algebraic structure may yield different predictions. See `paper/DESIGN_RATIONALE.md` §8.5 for analysis of potential divergence regimes.

---

## Cross-References

- **Lean proofs:** `proofs/QBP/Basic.lean` (core axioms), `proofs/QBP/Experiments/SternGerlach.lean` (orthogonal case), `proofs/QBP/Experiments/AngleDependent.lean` (angle-dependent case)
- **Design rationale:** `paper/DESIGN_RATIONALE.md` §4 (measurement postulate), §5.2 (factor-of-2 correction), §6.3 (expectation value bounds), §8.3 (observable formalism)
- **Proof review:** `research/01b_angle_dependent_proof_review.md` (axiom-first verification)
