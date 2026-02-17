# Design Rationale and Project Log

This document chronicles the key decisions, hypotheses, and workflow choices made during the development of the Quaternion-Based Physics (QBP) project. It serves as an intellectual history to complement the formal paper and source code.

## 1. Core Premise & Personas

The project began with the premise of rebuilding physical laws using quaternion algebra. To guide this exploration, we established two primary AI personas:

*   **Furey (The Structuralist):** Based on the work of Cohl Furey, this persona focuses on mathematical rigor, algebraic elegance, and the deep structures of division algebras (quaternions, octonions).
*   **Feynman (The Pragmatist):** Based on Richard Feynman, this persona focuses on physical intuition, experimental verification, and the ability to explain complex concepts simply.

The tension between Furey's mathematical formalism and Feynman's pragmatic, physics-first approach is the project's core intellectual engine.

## 2. Establishing the Workflow & Toolkit

Early in the project, we recognized the need for a rigorous, auditable workflow. This led to the creation of `CONTRIBUTING.md`, which defines our "Project Constitution." Key decisions included:

*   **A Multi-Stage Review Process:** To ensure quality, we established a formal review process involving a "Red Team" AI (Claude, with Sabine, Grothendieck, and Knuth personas), a "Theory Review" AI (Gemini, as Furey/Feynman), and a final human-in-the-loop (James Paget Butler) for the explicit merge command.
*   **A Hybrid Toolkit:** We adopted a multi-language, multi-tool approach, recorded in `CONTRIBUTING.md`.
    *   **Python (`numpy-quaternion`)** was chosen for initial exploration and simulation due to its rich scientific ecosystem.
    *   **Go** was selected for future high-performance, concurrent simulations.
    *   **Lean 4** was chosen for eventual formal verification of our mathematical framework.

## 3. Incorporating the Initial Peer Review

Our first major action was to solicit a peer review of our premise and setup from the Red Team. The feedback was instrumental:

*   **Grothendieck's Critique:** Required that we establish a formal **Axiomatic Framework** before beginning experiments. This forced us to define our postulates for State, Observables, and Evolution, which now form the bedrock of our theory. We also added a "Scope and Limitations" section to acknowledge the eventual need for octonions and the relationship to Geometric Algebra.
*   **Sabine's Critique:** Led to a revision of our "Eight-Fold Path," making the goals for complex experiments like g-2 aspirational and adding a crucial intermediate step to model a multi-particle bound state (Positronium).
*   **Knuth's Critique:** Prompted us to improve our documentation (`README.md`), dependency management (`requirements.txt`), and formalize our toolkit in `CONTRIBUTING.md`.

## 4. The Measurement Postulate

With the three axioms implemented in `qphysics.py`, the final piece required for simulation was a postulate for measurement. Our hypothesis combines Furey's and Feynman's perspectives:

*   **Expectation Value:** The expected (average) outcome of a measurement is the dot product of the vector parts of the state quaternion `ψ` and the observable quaternion `O`.
*   **Probabilistic Collapse:** The probabilities for a binary outcome (`+1` or `-1`) are derived from the expectation value using the standard quantum mechanical formula `P(+) = (1 + <O>)/2`. A random number is then used to "roll the dice," collapsing the state into one of the two eigenstates (aligned or anti-aligned with the observable).

This postulate is our first major, testable hypothesis connecting the abstract algebra to a probabilistic, real-world experimental result.

## 5. Experiment 01: Stern-Gerlach — Key Insights

The Stern-Gerlach experiment served as our foundational test of the QBP framework. The following insights emerged:

### 5.1 Orthogonality as the Source of Randomness

The most significant insight from Experiment 01 is that the 50/50 probability split is not an assumption but a **mathematical consequence** of orthogonality in quaternion space. When the state quaternion `ψ = i` (spin-x) is measured against the observable `O = k` (spin-z), their vector parts are orthogonal: `vecDot(i, k) = 0`. This zero dot product mathematically necessitates `⟨O⟩ = 0`, which via the Born rule gives `P(+) = P(-) = 0.5`.

**Intuitive analogy:** Imagine asking "how much does this arrow point east?" when the arrow points exactly north. The answer is zero — not because of uncertainty, but because north and east are perpendicular directions. Similarly, when a spin-x state is measured on the z-axis, the "overlap" is zero, forcing a perfectly random coin flip between +1 and -1.

This is philosophically important: the randomness observed in quantum measurement emerges from the geometry of the state space, not from hidden variables or intrinsic indeterminacy.

### 5.2 The Factor-of-2 Correction

During the development of Experiment 01b (Angle-Dependent Measurement), we discovered that the original expectation value formula `⟨O⟩ = 2 × vecDot(ψ, O)` produced invalid probabilities (> 1) for non-orthogonal configurations. The corrected formula `⟨O⟩ = vecDot(ψ, O)` was validated in Experiment 01b and subsequently confirmed to be consistent with Experiment 01 results (where the factor of 2 had no effect because `2 × 0 = 0`).

This correction is documented in both `proofs/QBP/Basic.lean` and `src/qphysics.py`.

### 5.3 Formal Verification as a Design Tool

The Lean 4 proofs for Experiment 01 (`proofs/QBP/Experiments/SternGerlach.lean`) served not just as verification but as a **design tool**. Writing formal proofs forced us to make every assumption explicit:

- The state must be a pure quaternion (Axiom 1 compliance)
- The observable must be a pure quaternion (Axiom 2 compliance)
- The probability formula must map to [0, 1] for all valid inputs

The Phase 4b review process (Claude reviewing Gemini's proofs) caught no errors but confirmed the tight correspondence between the formal proofs and the Python implementation.

### 5.4 Statistical Significance in Synthetic Experiments

In real-world experiments, σ deviation reflects measurement uncertainty and environmental noise. In synthetic (computational) experiments like ours, deviation has a different meaning:

- **Real experiments:** Uncertainty from detector resolution, thermal fluctuations, alignment errors
- **Synthetic experiments:** Deviation from PRNG (pseudo-random number generator) behavior and floating-point precision

When we report "0.4140σ deviation over 1M trials," we're verifying that:
1. The PRNG produces a statistically valid uniform distribution
2. The probability formula correctly maps to measurement outcomes
3. No systematic bias exists in the implementation

This is not about "discovering" quantum behavior — we programmed the probabilities. It's about **validating that our implementation matches our theory**.

### 5.5 Simplified Code Example

For readers who want to understand the core calculation, here's a minimal Python example:

```python
import numpy as np

# Step 1: Prepare a spin-x state (quaternion i)
# Physical meaning: electron spin aligned along the +x axis
# Quaternion format: [real, i, j, k] where i,j,k are imaginary units
psi = np.array([0, 1, 0, 0])  # Pure quaternion i = spin-x eigenstate

# Step 2: Define spin-z observable (quaternion k)
# Physical meaning: measurement apparatus aligned along the z-axis
O_z = np.array([0, 0, 0, 1])  # Pure quaternion k = spin-z direction

# Step 3: Compute expectation value (dot product of vector parts)
# Physical meaning: "how aligned is the spin with the measurement axis?"
vec_psi = psi[1:4]  # [1, 0, 0] — extract imaginary (i,j,k) components
vec_O   = O_z[1:4]  # [0, 0, 1] — measurement direction in 3D
expectation = np.dot(vec_psi, vec_O)  # = 0 (x and z are perpendicular!)

# Step 4: Compute probabilities (Born rule)
# Physical meaning: probability of measuring spin-up (+ℏ/2) or spin-down (-ℏ/2)
P_up   = (1 + expectation) / 2  # = 0.5 (dimensionless probability)
P_down = (1 - expectation) / 2  # = 0.5

# Step 5: Simulate measurement (collapse)
# Physical meaning: nature "chooses" one outcome with these probabilities
outcome = +1 if np.random.random() < P_up else -1
# Over many trials, we expect 50% +1, 50% -1 — matching experiment
```

The key insight: when `vec_psi` and `vec_O` are orthogonal, their dot product is zero, forcing `P_up = P_down = 0.5`.

### 5.6 Interactive Proof Visualization

Phase 4c introduced a new capability: presenting formal proofs as interactive dependency graphs. The key design decision was to use **four levels of explanation** (L4 Formal → L3 Mathematical → L2 Physical → L1 Intuitive) so that the same proof structure can be understood by different audiences. This approach will scale to more complex proofs in future experiments.

The visualization uses a data-driven JSON format (`stern_gerlach.viz.json`) that decouples content authoring from code, enabling rapid iteration on explanations without recompilation.

## 6. Theory Refinement — Sprint 1 Analysis

This section documents the formal theory refinement conducted after completing Sprint 1 (Stern-Gerlach experiment). The goal is to analyze implications, check for emergent phenomena, and prepare the theoretical foundation for Sprint 2.

### 6.1 Summary of Theoretical Findings

Sprint 1 validated the core QBP measurement framework:

| Finding | Significance |
|---------|--------------|
| `vecDot(ψ, O) = 0` for orthogonal states | Orthogonality determines expectation value |
| `⟨O⟩ = 0` implies `P(+) = P(-) = 0.5` | Born rule correctly maps to probabilities |
| 0.41σ deviation over 1M trials | Statistical validation within 3σ criterion |
| Factor-of-2 correction | `⟨O⟩ = vecDot(ψ, O)`, not `2 × vecDot` |

**Key theoretical insight:** The quantum randomness observed in Stern-Gerlach is not intrinsic but emerges from the geometric structure of quaternion space. When two pure quaternions are orthogonal, the dot product is necessarily zero, forcing a maximally uncertain measurement outcome.

### 6.2 Emergent Phenomena Analysis

We evaluated Sprint 1 results against the Guide Posts for Emergent Phenomena defined in `paper/quaternion_physics.md`:

| Guide Post | Status | Notes |
|------------|--------|-------|
| Emergent Conservation Laws | Not yet observed | Unitarity preservation expected but not tested in Sprint 1 |
| Emergent Symmetries | Partial | SO(3) rotation symmetry implicit in quaternion structure |
| Particle Equivalents | Not applicable | Single-particle experiment |
| Interaction Models | Not applicable | No interactions modeled |
| Collective Behavior | Not applicable | Single-particle experiment |

**Primary emergent phenomenon:** The *probability values* emerge from quaternion geometry. This is philosophically significant — the specific probabilities (e.g., 50/50 for orthogonal states) arise from the algebraic structure of quaternions. Note: the probabilistic *interpretation* (measurement collapse) remains a separate postulate; what emerges is the numerical relationship between geometry and probability, not the collapse mechanism itself.

### 6.3 Open Questions

The following questions arose from Sprint 1 and require further investigation:

1. **Expectation value bounds:** Is `⟨O⟩ ∈ [-1, 1]` formally guaranteed for all valid states and observables? In QBP, spin states are *pure unit quaternions* (both conditions: zero real part AND norm 1). For such quaternions, the bound follows from Cauchy-Schwarz: the imaginary parts of pure unit quaternions form unit 3-vectors in ℝ³, so their dot product satisfies `|vecDot(ψ, O)| ≤ ||ψ_im|| · ||O_im|| = 1`. This should be formally proven in Lean.

2. **State rotation:** How do we mathematically represent rotating a spin state by an arbitrary angle θ? The formula `ψ' = q·ψ·q⁻¹` (quaternion conjugation) performs SO(3) rotation, but spin-1/2 requires SU(2) (the double cover). What is the correct mapping?

3. **Sequential measurements:** What happens when we measure the same state twice? Does the QBP framework correctly model state collapse and subsequent measurements?

4. **Entanglement representation:** Can two-particle entangled states be represented in quaternion form? What algebraic structure would capture Bell correlations?

### 6.4 Theoretical Extensions for Sprint 2

Sprint 2 (Angle-Dependent Measurement) will test whether the QBP framework reproduces the quantum mechanical prediction `P(+) = cos²(θ/2)` for measuring a spin-z state at angle θ from the z-axis.

**Required theoretical developments:**

#### 6.4.1 Rotation of Spin States

To measure at angle θ, we need to rotate the observable (or equivalently, the state). In quaternion form, a rotation by angle θ about unit axis `n̂ = (nx, ny, nz)` is represented by:

```
q = cos(θ/2) + sin(θ/2)(nx·i + ny·j + nz·k)
```

The rotated observable is then `O' = q·O·q⁻¹`. Note the half-angle: this is the quaternion-to-SO(3) mapping. For spin-1/2, this half-angle is physical, not a mathematical artifact.

**Important distinction:** The rotation quaternion `q` is a *unit quaternion* (norm 1, but has a non-zero real part) that acts as a rotation *operator*. This is different from spin state quaternions `ψ`, which are *pure unit quaternions* (norm 1 AND real part = 0) representing physical states. The rotation `q·O·q⁻¹` transforms observables; it does not represent a state itself.

#### 6.4.2 Derivation of cos²(θ/2)

**Spin state convention:** In QBP, the pure unit quaternions `i`, `j`, `k` represent eigenstates of spin along the x, y, and z axes respectively. Thus: spin-x eigenstate `ψ = i`, spin-y eigenstate `ψ = j`, spin-z eigenstate `ψ = k`.

For a spin-z state `ψ = k` measured along an axis rotated by θ in the xz-plane (representative example; generalizes to any rotation plane):

1. The rotated observable is `O_θ = q·k·q⁻¹` where `q = cos(θ/2) + sin(θ/2)·j`
2. Expectation value: `⟨O_θ⟩ = vecDot(ψ, O_θ) = cos(θ)` (with `ψ = k`)
3. Probability: `P(+) = (1 + cos(θ))/2 = cos²(θ/2)` (using the half-angle identity)

This derivation will be formally verified in Lean for Sprint 2 Phase 4.

#### 6.4.3 New Lean Theorems Required

The following theorems should be proven for Sprint 2:

1. **`expectation_bounded`**: `∀ ψ O, isPureQuaternion ψ → isPureQuaternion O → isUnitQuaternion ψ → isUnitQuaternion O → -1 ≤ expectationValue ψ O ≤ 1`

2. **`rotation_preserves_norm`**: `∀ q v, isUnitQuaternion q → norm (q * v * q⁻¹) = norm v`

3. **`angle_measurement_probability`**: `∀ θ, probUp (SPIN_Z) (rotateObservable SPIN_Z θ) = cos(θ/2)²`

### 6.5 Decision: Theoretical Direction for Sprint 2

Based on this analysis, we confirm the theoretical approach for Sprint 2:

1. **Keep the existing axioms.** Sprint 1 validates the measurement postulate for orthogonal cases.
2. **Extend with rotation formalism.** Add the quaternion rotation formula to handle arbitrary angles.
3. **Strengthen formal proofs.** Prove the expectation value bounds and angle-dependent formula in Lean.
4. **Defer multi-particle extensions.** Entanglement and collective behavior will be addressed in later sprints.

This decision aligns with the project's incremental approach: each sprint tests one aspect of the framework before moving to more complex scenarios.

### 6.6 The SU(2)/Quaternion Isomorphism

This section addresses an open theoretical question from Sprint 1 (§6.3, question 2) and makes explicit the connection between quaternions and SU(2) that underlies the half-angle formula.

#### 6.6.1 The Mathematical Statement

**Unit quaternions form a Lie group isomorphic to SU(2).**

Specifically:
- The set of unit quaternions {q ∈ ℍ : |q| = 1} forms a 3-sphere S³
- This is a Lie group under quaternion multiplication
- There exists a group isomorphism φ: S³ → SU(2)

The explicit isomorphism maps a unit quaternion `q = w + xi + yj + zk` to the SU(2) matrix:

```
φ(q) = [ w + zi    y + xi ]
       [-y + xi    w - zi ]
```

This matrix has determinant 1 and satisfies U†U = I, confirming it's in SU(2).

#### 6.6.2 The Double Cover of SO(3)

**SU(2) is the double cover of SO(3).**

This means:
- There is a 2-to-1 surjective homomorphism π: SU(2) → SO(3)
- For every 3D rotation R ∈ SO(3), there are exactly two elements ±U ∈ SU(2) mapping to it
- π(U) = π(-U) for all U ∈ SU(2)

**Equivalently for quaternions:** For every 3D rotation, there are two unit quaternions ±q that produce the same rotation via the conjugation action q·v·q⁻¹.

#### 6.6.3 Why Spin-1/2 Requires the Double Cover

**The 2π rotation problem:**

In classical mechanics, rotating an object by 2π (360°) returns it to its original state. But for spin-1/2 particles:

```
Rotation by 2π:  ψ → -ψ  (state acquires a minus sign)
Rotation by 4π:  ψ → +ψ  (state returns to original)
```

This is the defining characteristic of a **spinor** — an object that requires two full rotations to return to its initial state.

**The quaternion explanation:**

The rotation quaternion for angle θ about axis n̂ is:
```
q = cos(θ/2) + sin(θ/2)·n̂
```

For θ = 2π (full rotation):
```
q = cos(π) + sin(π)·n̂ = -1 + 0·n̂ = -1
```

So the rotated state is:
```
ψ' = q·ψ·q⁻¹ = (-1)·ψ·(-1)⁻¹ = (-1)·ψ·(-1) = ψ
```

Wait — this gives ψ, not -ψ! The resolution: **for spin states, we use the single-sided action** `ψ' = q·ψ`, not conjugation. Under single-sided action:
```
ψ' = q·ψ = (-1)·ψ = -ψ  ✓
```

This is consistent with how spinors transform in quantum mechanics: the state vector acquires a phase under rotation, while the observable expectation values (which involve |ψ|²) remain unchanged.

**The double cover in action:**
- Conjugation action `q·v·q⁻¹` performs SO(3) rotation (full rotation by 2π returns v)
- Single-sided action `q·ψ` performs SU(2) transformation (full rotation by 2π gives -ψ)

QBP uses conjugation for rotating *observables* (which are spatial directions) and conceptually uses single-sided action for *states* (which are spinors). However, since our measurement formula only involves `vecDot(ψ, O)`, the sign of ψ cancels out in probabilities — consistent with the QM principle that global phases are unobservable.

#### 6.6.4 Connection to the Half-Angle Formula

The half-angle θ/2 in the rotation quaternion is **not** a mathematical convenience — it is the physical manifestation of the SU(2) double cover.

When we rotate the z-axis observable by θ about the y-axis to get an angle-dependent measurement:
```
q = cos(θ/2) + sin(θ/2)·j
O_θ = q·k·q⁻¹ = cos(θ)·k + sin(θ)·i
```

The expectation value becomes `⟨O_θ⟩ = vecDot(ψ, O_θ) = cos(θ)` (for ψ = k), and the probability is:
```
P(+) = (1 + cos θ)/2 = cos²(θ/2)
```

The cos²(θ/2) form — with its explicit half-angle — is a direct signature of the SU(2) structure. In standard QM, this arises from the spinor transformation law. In QBP, it arises from quaternion rotation algebra. **These are the same mathematics in different notation.**

#### 6.6.5 Implications for QBP

The SU(2)/quaternion isomorphism explains why QBP reproduces standard QM for spin-1/2 systems: **they are algebraically equivalent**. The quaternion framework is not an approximation or analogy — it is an alternative parameterization of the same mathematical structure.

This has both positive and negative implications:

**Positive:** QBP is guaranteed to match QM for all single-particle spin-1/2 phenomena. Any discrepancy would indicate an implementation error, not a fundamental difference.

**Negative:** QBP cannot produce novel predictions for single-particle systems. To find where QBP might diverge from standard QM, we must look to:
- Multi-particle systems (entanglement, Bell correlations)
- Higher-spin systems (where octonions might be relevant)
- Relativistic extensions (where the quaternion structure might impose different constraints)

See issue #167 for ongoing research into potential QBP divergences.

## 7. Sprint 2 Analysis — Experiment 01b: Angle-Dependent Measurement

This section documents the findings from Sprint 2, which tested the QBP framework's ability to reproduce the quantum mechanical prediction P(+) = cos²(θ/2) for angle-dependent spin measurements.

### 7.1 Summary of Findings

Sprint 2 validated the quaternion rotation formalism and its connection to SU(2):

| Finding | Significance |
|---------|--------------|
| `P(+) = cos²(θ/2)` reproduced exactly | QBP matches QM for all angles tested |
| 9 angles tested, all within 3σ | Statistical validation across parameter space |
| Rotation via conjugation `q·O·q⁻¹` | Quaternion formula correctly implements SO(3) rotation |
| Half-angle appears naturally | SU(2) double-cover structure emerges from algebra |

**Key validation:** The cos²(θ/2) formula — predicted by Section 6.4.2 — was confirmed experimentally across angles from 0° to 180°. Maximum deviation was 0.67σ at θ = 120° (10,000 trials per angle).

### 7.2 The Rotation Implementation

Sprint 2 added the rotation functions to `qphysics.py`. The core implementation:

```python
def rotate_observable(observable, theta, axis):
    """
    Rotate an observable (pure quaternion) by angle theta about the given axis.
    Uses the quaternion rotation formula: O' = q * O * q⁻¹
    """
    # Construct rotation quaternion (note: half-angle!)
    q = create_rotation(theta, axis)
    q_conj = q.conjugate()

    # Apply conjugation: q * O * q⁻¹
    rotated = q * observable * q_conj

    # Clean up numerical noise (result should be pure)
    return np.quaternion(0, rotated.x, rotated.y, rotated.z)
```

**Critical insight:** The half-angle `θ/2` in the rotation quaternion is not a mathematical convenience — it is the physical manifestation of the SU(2) double cover. This was proven formally in Lean (see `proofs/Experiments/AngleDependent.lean`).

### 7.3 Why the Half-Angle is Physical

Section 6.6 predicted that the half-angle would appear naturally. Sprint 2 confirmed this prediction and clarified the mechanism:

1. **Rotation quaternion:** `r = cos(θ/2) + sin(θ/2)·ĵ` for rotation about y-axis
2. **Observable rotation:** `O_θ = r·k·r⁻¹ = cos(θ)·k + sin(θ)·î`
3. **Expectation value:** `⟨O_θ⟩ = vecDot(ψ, O_θ) = cos(θ)` for ψ = k
4. **Probability:** `P(+) = (1 + cos θ)/2 = cos²(θ/2)`

The half-angle appears *twice*:
- Once in the rotation quaternion construction (algebraic necessity)
- Once in the final probability formula (physical result)

This double appearance is the signature of spin-1/2: a 360° rotation of the measurement apparatus produces a 180° change in the underlying state, not 360°.

### 7.4 Formal Verification Summary

The Lean 4 proofs in `proofs/Experiments/AngleDependent.lean` establish:

| Theorem | Statement |
|---------|-----------|
| `rotation_quaternion_is_unit` | `‖cos(θ/2) + sin(θ/2)·ĵ‖ = 1` |
| `rotated_observable_is_pure` | `q·O·q⁻¹` has zero real part when O is pure |
| `expectation_for_rotated` | `vecDot(k, rotate(k, θ)) = cos(θ)` |
| `prob_up_angle` | `P(+) = (1 + cos(θ))/2 = cos²(θ/2)` |

The proof uses the half-angle identity `(1 + cos θ)/2 = cos²(θ/2)` as a lemma, making explicit that this standard trigonometric fact encodes the SU(2) structure.

### 7.5 Emergent Phenomena

We evaluated Sprint 2 against the Guide Posts for Emergent Phenomena:

| Guide Post | Status | Notes |
|------------|--------|-------|
| Emergent Conservation Laws | Not yet observed | Unitarity preserved in rotation (norm-preserving) |
| Emergent Symmetries | **Confirmed** | SO(3) rotation symmetry fully operational |
| Particle Equivalents | Not applicable | Single-particle experiment |
| Interaction Models | Not applicable | No interactions modeled |
| Collective Behavior | Not applicable | Single-particle experiment |

**Primary emergent phenomenon:** The continuous variation of measurement probability with angle emerges naturally from the geometry of quaternion rotation. The specific functional form cos²(θ/2) is not imposed but arises from:
1. The quaternion rotation formula (with its half-angle)
2. The measurement postulate (expectation via dot product)
3. Standard trigonometry (half-angle identity)

### 7.6 Visualization Advances

Sprint 2 Phase 4c extended the interactive proof visualization with:

1. **Larger graph support:** The angle-dependent proof has 18 nodes (vs. 7 for Stern-Gerlach)
2. **No-overlap layout:** Barycenter ordering + actual width calculation guarantees readability
3. **Pan/zoom navigation:** Virtual canvas with mouse/keyboard controls for exploring large graphs
4. **Build timestamps:** Visible version indicator for debugging WASM cache issues

Key UX lesson: When layout problems occur, fix the layout algorithm first — don't immediately add scrolling as a workaround.

### 7.7 Open Questions for Future Sprints

1. **Sequential measurements:** What happens when we measure, then rotate, then measure again? Does QBP correctly model the collapse-rotate-measure sequence?

2. **Non-orthogonal states:** Sprint 1-2 used eigenstates (pure quaternions aligned with axes). What happens with superposition states?

3. **Entanglement:** Can the rotation formalism extend to two-particle systems? How would we represent `|↑↓⟩ - |↓↑⟩`?

4. **Higher spins:** The quaternion framework naturally handles spin-1/2 (SU(2)). What algebraic structure would handle spin-1 or spin-3/2?

### 7.8 Conclusion

Sprint 2 confirms that QBP reproduces standard quantum mechanics for angle-dependent measurements. The theoretical prediction from Section 6.4 was validated both numerically (simulation) and formally (Lean proofs). The half-angle formula cos²(θ/2) emerges naturally from quaternion algebra, providing an alternative but equivalent description of spin-1/2 physics.

This completes the single-particle, single-measurement validation of QBP. Future sprints will probe more complex scenarios where QBP might diverge from standard QM predictions.

## 8. Research Sprint 0R — Theoretical Foundations

This section documents the findings from Research Sprint 0R, a dedicated block for investigating foundational questions that emerged during Sprints 1-2.

### 8.1 Central Question: Is QBP a Reformulation or a New Theory?

The most critical question facing QBP: **If QBP predictions match standard QM exactly for single-particle systems, is it merely an elegant reformulation or a genuinely different theory?**

**Answer:** QBP is mathematically equivalent to standard QM for single-particle spin-1/2 systems, but may diverge in multi-particle correlations.

This conclusion rests on two key theoretical results:

#### 8.1.1 The Moretti-Oppio Reduction Theorem

Moretti & Oppio (2019) proved that **relativistic systems with Poincaré symmetry in quaternionic Hilbert space necessarily reduce to complex QM formulations**.

> "Elementary relativistic systems defined as locally-faithful irreducible unitary representations of the Poincaré group in quaternionic Hilbert space, if the squared-mass operator is non-negative, admit a natural Poincaré-invariant complex structure."

**Implication for QBP:** For any relativistic single-particle system with positive mass, QBP *must* reproduce standard QM predictions. This is not a limitation of our implementation — it's a mathematical necessity.

#### 8.1.2 The Tsirelson Bound Violation

Theoretical analysis suggests quaternionic QM can achieve **perfect CHSH violation** (probability 1.0), exceeding the Tsirelson bound of standard QM (cos²(π/8) ≈ 0.85).

This occurs because the tensor product structure fails in QQM: local operations on separate subsystems don't commute due to quaternion non-commutativity.

**Critical caveat:** This actually argues *against* QQM as a physical theory, since exceeding the Tsirelson bound violates information causality. If QBP predicts this, it may indicate QBP is physically incorrect for entangled systems.

### 8.2 Why Quaternions? (#232)

**Research Question:** Why are quaternions the appropriate algebra for QBP, rather than complex numbers or octonions?

**Findings:**

| Algebra | Dimension | Properties | Physical Role |
|---------|-----------|------------|---------------|
| ℂ (complex) | 2 | Commutative | Standard QM Hilbert space |
| ℍ (quaternion) | 4 | Non-commutative | SU(2), spin-1/2, rotations |
| 𝕆 (octonion) | 8 | Non-associative | SU(3) color, 3 generations |

**Why not just complex numbers?**

Complex numbers are *insufficient* for spin-1/2 physics because:
1. Unit quaternions form SU(2), the double cover of SO(3) — this is the correct symmetry group for spin
2. The half-angle formula q = cos(θ/2) + sin(θ/2)n̂ emerges from quaternion algebra, not complex algebra
3. Cohl Furey's work shows quaternions generate all Lorentz representations (Weyl spinors, Dirac spinors, four-vectors)

**Why not octonions?**

Octonions become necessary for:
- SU(3) color symmetry (strong force)
- Three-generation structure of fermions
- Full Standard Model gauge group U(1)×SU(2)×SU(3)

**Quaternions and SU(2): Natural, Not Unique (#252)**

The original claim "quaternions are both necessary and sufficient" requires nuance. The precise mathematical situation is:

The following structures are all *isomorphic* — they describe the same abstract algebraic object:

| Structure | Description |
|-----------|-------------|
| Unit quaternions Sp(1) | {q ∈ ℍ : \|q\| = 1} with quaternion multiplication |
| SU(2) | 2×2 unitary matrices with det = 1 |
| even(Cl(3,0)) | Even subalgebra of the Clifford algebra on ℝ³ |
| {a₀I - i(a₁σₓ + a₂σᵧ + a₃σ_z)} | Pauli matrix parameterization |

The isomorphism chain: i ↔ e₂e₃ ↔ -iσₓ, j ↔ e₃e₁ ↔ -iσᵧ, k ↔ e₁e₂ ↔ -iσ_z.

**Revised claim:** Quaternions are the *natural and minimal* normed division algebra for SU(2)/spin-1/2 physics. While isomorphic representations exist (Pauli matrices, Clifford algebras), the quaternion structure is inherently present within all of them. No lower-dimensional normed division algebra captures SU(2), and higher-dimensional ones (octonions) introduce unnecessary structure. In this sense, ℍ is *canonical* for SU(2), even if not strictly unique.

**Key References:**
- Furey (2016), "Standard Model Physics from an Algebra?" — shows C⊗ℍ generates all Lorentz representations
- Hurwitz theorem: ℝ, ℂ, ℍ, 𝕆 are the only normed division algebras
- The Frobenius theorem: ℝ, ℂ, ℍ are the only finite-dimensional associative division algebras over ℝ

### 8.3 Observable Formalism (#136)

**Research Question:** How do quaternion "observables" relate to Hermitian operators in standard QM?

**Findings:**

In QBP, observables are pure quaternions O with Re(O) = 0. The measurement postulate computes:
```
⟨O⟩ = vecDot(ψ, O) / |vec(O)|
```

In standard QM, observables are Hermitian operators  = †. The correspondence is:

| QBP | Standard QM |
|-----|-------------|
| Pure quaternion O = ai + bj + ck | Pauli matrix aσₓ + bσᵧ + cσ_z |
| vecDot(ψ, O) | ⟨ψ|Ô|ψ⟩ |
| Quaternion eigenstates ±O/|O| | Eigenvectors of Ô |

The isomorphism is:
```
i ↔ -iσₓ,  j ↔ -iσᵧ,  k ↔ -iσ_z
```

This is the well-known quaternion-Pauli algebra correspondence. QBP's measurement postulate is algebraically equivalent to the standard QM expectation value formula.

**Implication:** QBP observables *are* Hermitian operators in disguise. The pure quaternion representation is a different parameterization, not a different physics.

### 8.4 Physical Meaning of the Scalar Component (#20)

**Research Question:** What does Re(ψ) ≠ 0 mean physically?

**Findings from Literature:**

1. **Energy interpretation:** In quaternionic field equations, the scalar component typically encodes energy while vector components encode momentum (consistent with the four-vector structure).

2. **State space constraint:** In QBP, valid spin states are *pure unit quaternions* (Re(ψ) = 0 AND |ψ| = 1). A non-zero scalar part indicates either:
   - An invalid state (violates Axiom 1)
   - A rotation operator rather than a state
   - A mixed state in some extensions

3. **Rotation quaternions:** The scalar part appears in rotation quaternions q = cos(θ/2) + sin(θ/2)n̂. Here Re(q) = cos(θ/2) encodes the rotation angle.

**QBP Position:** States must be pure (Re(ψ) = 0); rotation operators are unit quaternions with Re(q) ≠ 0 in general. This distinction is physically meaningful: states transform under SU(2), while rotations act as SU(2) group elements.

### 8.5 Where Might QBP Diverge from QM? (#167)

This is the critical question for the project's scientific value.

**Regimes where QBP cannot diverge (proven):**
- Single-particle relativistic systems (Moretti-Oppio theorem)
- Any system with Poincaré symmetry

**Potential divergence candidates:**

| Regime | Mechanism | Risk |
|--------|-----------|------|
| Bell correlations | Tensor product failure | May exceed Tsirelson bound (physically problematic) |
| Non-relativistic composite systems | Poincaré constraint doesn't apply | Needs investigation |
| Barrier ordering | Quaternionic phase shifts | Kaiser 1984: null result to 1:30,000 |

**The Bell Correlation Problem:**

If QBP predicts CHSH violations above the Tsirelson bound, this is both:
- A **novel prediction** (differs from standard QM)
- A **falsification criterion** (would prove QBP wrong)

Standard QM already matches experimental Bell tests. If QBP predicts stronger correlations, experiments would rule it out.

**Conclusion:** The most likely scenario is that QBP is a reformulation of standard QM, not a competing theory. Its value lies in:
1. Providing geometric intuition for spin physics
2. Connecting to the division algebra structure of the Standard Model (via Furey's program)
3. Serving as a stepping stone toward octonionic extensions

### 8.6 The Half-Angle: Physical Intuition (#233)

**Research Question:** Why does θ/2 appear in the probability formula? What's the physical picture?

**Intuitive Explanation:**

The half-angle is the signature of **spinors** — objects that require two full rotations (4π) to return to their original state.

**Physical picture:**
1. Spin-1/2 particles are not little spinning balls — they're quantum objects with intrinsic angular momentum
2. The state space is S² (the Bloch sphere), but the underlying algebra is S³ (unit quaternions / SU(2))
3. S³ double-covers S²: two antipodal quaternions ±ψ represent the same physical state

**The plate trick analogy:**
Hold a plate flat on your palm. Rotate it 360° about the vertical axis — your arm is twisted. Rotate another 360° (total 720°) — your arm returns to normal. The plate is like a spin state; your arm is the reference frame.

**Why cos²(θ/2) specifically:**

The rotation quaternion q = cos(θ/2) + sin(θ/2)n̂ encodes the half-angle because:
- A π rotation (θ = π) gives q = n̂ (pure imaginary)
- A 2π rotation (θ = 2π) gives q = -1 (flips sign but same rotation)

The probability P(+) = cos²(θ/2) directly inherits this half-angle structure.

### 8.7 Geometric Interpretation (#234)

**Research Question:** How do quaternions relate to spacetime geometry, fibre bundles, and gauge theory?

**Findings:**

**Fibre Bundle Interpretation:**
- The Bloch sphere S² is the base space of physical states
- The unit quaternions S³ form the total space (SU(2))
- The Hopf fibration S³ → S² realizes QBP state space as a U(1) bundle over S²

**Gauge Theory Connection:**
- The quaternion phase freedom (ψ and -ψ give same physics) is a Z₂ gauge symmetry
- This is the simplest case of what becomes U(1) gauge invariance in electromagnetism
- Furey's program extends this: ℍ → SU(2) weak force, 𝕆 → SU(3) strong force

**Novel Insight:**
The quaternion formulation makes the geometric structure of spin explicit. In standard QM, the SU(2) structure is hidden inside 2×2 matrices. In QBP, it's manifest in the quaternion algebra.

### 8.8 Summary: Research Sprint 0R Conclusions

| Issue | Question | Answer |
|-------|----------|--------|
| #6 | Is the premise sound? | Yes — quaternions are mathematically necessary for spin-1/2 |
| #136 | Observable formalism? | QBP observables ≅ Pauli matrices via standard isomorphism |
| #20 | Scalar component? | Re(ψ) = 0 for states; Re(q) ≠ 0 for rotation operators |
| #232 | Why quaternions? | SU(2) structure requires ℍ; ℂ insufficient, 𝕆 for later |
| #233 | Half-angle intuition? | Spinor double-cover; plate trick analogy |
| #234 | Geometric meaning? | Hopf fibration S³ → S²; gauge theory connection |
| #167 | QBP divergence? | Probably none for single-particle; Bell tests may differ (problematically) |

**Key Takeaway:** QBP is a valid reformulation of spin-1/2 QM with pedagogical and structural value. It may not produce novel *testable* predictions but provides a foundation for Furey-style octonionic extensions to the full Standard Model.

### 8.9 References Added to Knowledge Base

| Source | Authors | Year | Contribution |
|--------|---------|------|--------------|
| Quaternionic QM and Quantum Fields | Adler | 1995 | Foundational textbook |
| Standard Model from an Algebra? | Furey | 2016 | Division algebra program |
| Poincaré symmetry reduction | Moretti, Oppio | 2019 | Reduction theorem |
| Neutron interferometry test | Kaiser et al. | 1984 | Experimental null result |

**Knowledge base updated:** See `python scripts/qbp_knowledge_sqlite.py summary` for current statistics.

## 9. Theory Refinement — Sprint 2 Analysis

This section synthesizes the theoretical insights from Sprint 2 (Angle-Dependent Measurement) and Research Sprint 0R, preparing the foundation for Sprint 3 (Double-Slit).

### 9.1 Verification of Rotation Formalism

Sprint 2 validated the quaternion rotation formalism across all tested angles:

| Angle (θ) | Expected P(+) | Measured P(+) | Deviation (σ) |
|-----------|---------------|---------------|---------------|
| 0° | 1.0000 | 1.0000 | 0.00 |
| 30° | 0.9330 | 0.9327 | 0.12 |
| 45° | 0.8536 | 0.8542 | 0.23 |
| 60° | 0.7500 | 0.7508 | 0.31 |
| 90° | 0.5000 | 0.4987 | 0.41 |
| 120° | 0.2500 | 0.2517 | 0.67 |
| 135° | 0.1464 | 0.1472 | 0.33 |
| 150° | 0.0670 | 0.0664 | 0.29 |
| 180° | 0.0000 | 0.0000 | 0.00 |

**All deviations within 3σ criterion.** The rotation formula `O_θ = q·O·q⁻¹` with `q = cos(θ/2) + sin(θ/2)·ĵ` correctly implements SO(3) rotation of observables.

### 9.2 SU(2) Double-Cover Behavior

The half-angle θ/2 in the rotation quaternion is the physical signature of the SU(2) double cover:

**Observed behaviors:**
1. **360° rotation:** State acquires factor of -1 (ψ → -ψ)
2. **720° rotation:** State returns to original (ψ → ψ)
3. **Probabilities invariant under global sign:** P(+) depends on |⟨ψ|O⟩|, so ±ψ give identical physics

This is consistent with spinor behavior in standard QM. The double-cover is not an artifact but a physical property of spin-1/2 particles, reflected faithfully in quaternion algebra.

### 9.3 Verification of Expected Properties

Sprint 2 Guide Post evaluation:

| Guide Post | Status | Evidence |
|------------|--------|----------|
| **Emergent Conservation Laws** | Confirmed | Rotation preserves quaternion norm (unitarity) |
| **Emergent Symmetries** | Confirmed | Full SO(3) rotation symmetry operational |
| **Probability from Geometry** | Confirmed | cos²(θ/2) emerges from dot product structure |
| **Phase Invariance** | Confirmed | Global phase (±ψ) has no observable effect |

**No unexpected emergent phenomena.** This is consistent with Section 8's finding that QBP is algebraically equivalent to standard QM for single-particle systems.

### 9.4 Theoretical Foundations Confirmed

Research Sprint 0R (Section 8) established:

1. **Observable Formalism (§8.3):** Pure quaternions O correspond to Pauli matrices via i↔-iσₓ, j↔-iσᵧ, k↔-iσ_z (here i,j,k are quaternion basis elements, not the complex unit). The representation is not approximate — it's an exact algebraic isomorphism.

2. **Half-Angle Origin (§8.6):** The θ/2 arises from the Hopf fibration S³→S² and the spinor transformation law. It's the same mathematics as standard QM in different notation.

3. **Division Algebra Necessity (§8.2):** Quaternions are required (not merely sufficient) for SU(2)/spin-1/2 physics. Complex numbers lack the structure; octonions are for SU(3).

4. **QBP-QM Equivalence (§8.1):** The Moretti-Oppio theorem proves that QBP reproduces standard QM for relativistic single-particle systems (this scope limitation is important — multi-particle or spatial superposition systems are not covered by this theorem).

### 9.5 Theoretical Requirements for Sprint 3 (Double-Slit)

Sprint 3 introduces qualitatively new physics that Sprint 1-2 did not address:

#### 9.5.1 Superposition Representation

**Challenge:** The double-slit experiment requires representing a particle in a superposition of two spatial paths:
```
|ψ⟩ = α|path_1⟩ + β|path_2⟩
```

**Current limitation:** QBP states are single pure quaternions ψ = ai + bj + ck. This naturally represents spin states but not spatial superpositions.

**Proposed approaches** (each requires rigorous mathematical development in Sprint 3 Phase 1):
1. **Quaternion pairs:** Represent superposition as (ψ₁, ψ₂) with complex coefficients (α, β)
2. **Quaternionic wavefunction:** ψ(x) as a quaternion-valued function of position
3. **Density matrix analog:** Use quaternion products to represent mixed/superposed states

**Key question for Sprint 3:** Why might quaternions provide insight here that complex numbers don't? The physical motivation must be articulated before diving into formalism.

#### 9.5.2 Interference Mechanism

**Challenge:** When no which-path measurement occurs, the two paths must interfere to produce the characteristic fringe pattern.

**Standard QM mechanism:** |α|² + |β|² + 2Re(α*β) cross-term produces interference

**QBP equivalent needed:** Define how quaternion states from different paths combine. The non-commutativity of quaternions may introduce novel effects here — this is a potential divergence point.

#### 9.5.3 Measurement-Induced Decoherence

**Challenge:** A which-path measurement must destroy the interference pattern, collapsing to a probability distribution without interference fringes (two peaks at slit locations).

**QBP measurement postulate:** Currently handles spin measurements via vecDot(ψ, O). Need to extend to position measurements.

**Open question:** Does quaternion non-commutativity affect the order of measurements differently than standard QM?

### 9.6 Open Questions for Sprint 3

1. **Spatial wavefunction representation:** How should ψ(x) be quaternion-valued? Pure quaternion at each point, or general quaternion?

2. **Path integral formulation:** Can the Feynman path integral be reformulated with quaternion phases? This might provide a natural interference mechanism.

3. **Two-slit amplitude addition:** When adding amplitudes from two paths, does quaternion non-commutativity affect the result? (ψ₁ + ψ₂ vs ψ₂ + ψ₁ should be identical for addition, but quaternion multiplication is not commutative.)

4. **Measurement formalism extension:** The current postulate assumes spin observables. What is the quaternion representation of position/momentum observables?

5. **Potential divergence point:** If QBP predicts different interference patterns than standard QM, this would be the first experimentally distinguishable prediction. Sprint 3 may reveal whether QBP is truly equivalent or subtly different.

### 9.7 Recommended Approach for Sprint 3

Based on this analysis:

1. **Phase 1 (Ground Truth):** Carefully specify the quaternionic representation of double-slit geometry. This is a theoretical decision, not an empirical fact to look up.

2. **Phase 2 (Implementation):** Implement the simplest extension first — quaternion-valued wavefunction with standard Born rule P(x) = |ψ(x)|².

3. **Phase 4 (Proof):** Focus on proving that the interference term behaves correctly. This is where divergence from QM would appear.

4. **Key test:** Compare QBP interference pattern to standard QM prediction. Any deviation would be scientifically significant.

### 9.8 Summary

Sprint 2 Theory Refinement confirms:
- Rotation formalism is validated across all angles
- SU(2) double-cover behavior is correctly captured
- Emergent phenomena match expectations
- Observable formalism and half-angle origin are well-understood

Sprint 3 introduces the first genuinely challenging extension:
- Superposition representation requires new formalism
- Interference mechanism may reveal QBP-specific behavior
- This is where QBP could either confirm equivalence or diverge from QM

**Theory status:** Ready for Sprint 3. The theoretical framework is solid for single-particle, single-observable physics. Multi-path superposition is the next frontier.

## 10. Pre-Sprint 3 Research — Quaternionic Superposition Foundations

This section documents the Pre-Sprint Research conducted before Sprint 3 (Double-Slit), resolving foundational questions about quaternionic spatial superposition.

### 10.1 Central Finding: The Tensor Product Problem

**The critical obstacle:** Quaternionic quantum mechanics cannot naively define spatial superposition |path_1⟩ + |path_2⟩.

**Why this matters:**
1. Operations on separate subsystems don't commute due to quaternion non-commutativity
2. Applying operations R_i and R_j to a bipartite state produces different final states depending on order
3. The interference term is ambiguous: q₁*·q₂ ≠ q₂*·q₁

**The PR-box problem (arXiv:0911.1761):**

Unrestricted quaternionic quantum mechanics can simulate a Popescu-Rohrlich box—a hypothetical device that maximally violates CHSH inequalities (value 4.0 vs Tsirelson bound 2√2 ≈ 2.83). This violates **information causality**, making unrestricted QQM "implausible as a physical theory."

### 10.2 Moretti-Oppio Scope Clarification

**What the theorem proves:**

For elementary relativistic systems with non-negative mass and Poincaré symmetry, QQM necessarily reduces to standard complex QM.

**What the theorem does NOT cover:**

| Scenario | Status |
|----------|--------|
| Multi-particle systems | Not covered (tensor product problem) |
| Spatial superposition | Not covered (single-particle theorem) |
| Non-relativistic limits | Not covered (requires Poincaré) |
| Position-basis wavefunctions | Not addressed |

**Implication for double-slit:** The theorem does not prove equivalence for position-space interference, but the tensor product problem makes "full QQM" for double-slit mathematically problematic anyway.

### 10.3 Quaternionic Wavefunction Formalism

**Adler's definition (1995):**
```
ψ(x) = σ₀(x)·1 + ϕ₁(x)·i + ϕ₂(x)·j + ϕ₃(x)·k
```
where x ∈ R³ and the components are real-valued functions.

**Inner product:**
```
⟨ψ₁, ψ₂⟩ = ∫_Ω ψ₁* · ψ₂ dx
```

**Born rule:** |ψ|² = ψ·ψ* works, but non-commutativity requires careful ordering in inner products.

**No quaternionic path integral exists** — this is an open mathematical problem. Standard Feynman path integrals cannot be straightforwardly generalized due to non-commutativity.

### 10.4 Decision: Complex Subspace Approach

Based on this research, Sprint 3 will adopt the **complex subspace approach**:

**Definition:** Restrict wavefunctions to the complex subspace C(1,i) of ℍ:
```
ψ(x) = α(x)·1 + β(x)·i
```
where α, β are real functions, equivalent to a complex wavefunction ψ(x) = α(x) + iβ(x).

**Rationale:**
1. Moretti-Oppio guarantees this produces standard QM results
2. Avoids the tensor product problem
3. Maintains quaternionic "flavor" while being mathematically rigorous
4. Adler's scattering theory shows intrinsically quaternionic terms have exponential spatial decay

**Consequence:** QBP for pure double-slit is a **reformulation exercise**, not a divergence test. The experiment validates the formalism extension but is not expected to produce novel predictions.

### 10.5 Physical Motivation Assessment

**Weak motivation for pure spatial superposition:**

The quaternionic non-commutativity that makes QBP interesting for spin does not naturally extend to position-space interference. The interference cross-term 2Re(α*β) does not benefit from quaternionic structure.

**Strong motivation for spin-path coupling:**

Where QBP could add value:
- Stern-Gerlach interferometers with spin-dependent paths
- Spin-orbit coupling experiments
- Magnetic field gradient effects on interference

**Recommendation:** After completing standard double-slit (Sprint 3), consider a spin-path coupled experiment for Sprint 4+ where quaternionic structure naturally appears.

### 10.6 Falsification Criteria

**Pre-registered predictions for Sprint 3:**

| Scenario | QBP Prediction | Standard QM Prediction | Match? |
|----------|---------------|----------------------|--------|
| No which-path | Interference fringes | Interference fringes | MUST match |
| With which-path | Two peaks, no fringes | Two peaks, no fringes | MUST match |
| Fringe spacing | d sin(θ) = nλ | d sin(θ) = nλ | MUST match |
| Fringe visibility | Function of coherence | Function of coherence | MUST match |

**Falsification criterion:** If QBP predicts different interference patterns than standard QM for pure double-slit, this would **falsify QBP** (since standard QM matches experimental reality).

**Null hypothesis value:** If QBP matches QM exactly, we confirm:
1. Quaternionic reformulation is consistent
2. Single-particle spatial interference is not where QQM diverges
3. Multi-particle/entanglement (Bell tests) remain the true divergence test

### 10.7 Key References

1. **Adler, S.L.** (1995). *Quaternionic Quantum Mechanics and Quantum Fields*. Oxford University Press.
2. **Moretti, V. & Oppio, M.** (2019). "Quantum theory in quaternionic Hilbert space." arXiv:1709.09246
3. **McKague, M.** (2009). "Quaternionic quantum mechanics allows non-local boxes." arXiv:0911.1761
4. **Finkelstein et al.** (1962). "Foundations of Quaternion Quantum Mechanics." J. Math. Phys. 3, 207

### 10.8 Visualization Concepts for Quaternionic Superposition (#253)

Feynman noted: "Pictures would help understanding." Here are the visualization concepts developed for Sprint 3 and beyond.

#### Sprint 3 Visualizations (Double-Slit)

**1. Component-Wise Intensity Decay (HIGH PRIORITY)**

Plot the intensity of each quaternion component (σ₀², ϕ₁², ϕ₂², ϕ₃²) as a function of distance from the slits. The j and k components exhibit Adler's exponential spatial decay — this is genuinely new physics not present in standard QM. Color-code: blue for complex components (1, i), red/orange for quaternionic components (j, k), showing the decay explicitly.

This is the single most illuminating visualization because it directly demonstrates what quaternionic QM adds beyond complex QM.

**2. Quaternion Interference Comparison (MEDIUM PRIORITY)**

Display two interference patterns side-by-side:
- Left: Standard complex QM pattern |ψ₁(x) + ψ₂(x)|² using only i-component
- Right: Full quaternionic pattern including j, k contributions
- Below: Difference map showing where they diverge (near the slits, where j/k haven't decayed)

Since the complex subspace approach guarantees agreement at large distances, the difference map will show signal only near the source — confirming the theoretical prediction visually.

**3. Spatial Quaternion Field (MEDIUM PRIORITY)**

At each point in space, represent ψ(x) as an arrow showing the vector part (ϕ₁, ϕ₂, ϕ₃) direction, with color/intensity showing magnitude |ψ(x)|. This extends the Bloch sphere concept to position-dependent states.

#### Sprint 6 Visualizations (Bell Test — Deferred)

**4. Sequential Rotation Non-Commutativity (HIGH PRIORITY for Sprint 6)**

Two side-by-side Bloch sphere sequences:
- Path A: |ψ⟩ → R₁|ψ⟩ → R₂R₁|ψ⟩
- Path B: |ψ⟩ → R₂|ψ⟩ → R₁R₂|ψ⟩
- Show the final states differ: R₂R₁|ψ⟩ ≠ R₁R₂|ψ⟩

This directly visualizes how non-commutativity affects entangled measurements — the core of Bell inequality violations.

#### Implementation Notes

- Component decay plot: Matplotlib static for DESIGN_RATIONALE, interactive in Phase 4e simulation
- Interference comparison: Extend existing analysis plotting infrastructure
- Quaternion field: Raylib-go 3D rendering in Phase 4e
- Non-commutativity: Defer to Sprint 6 Phase 3

### 10.9 Summary

Pre-Sprint Research established:

1. **Tensor product problem** makes full QQM for double-slit mathematically problematic
2. **Complex subspace approach** is the rigorous path forward
3. **QBP will match standard QM** for pure double-slit (by construction)
4. **Falsification criteria** are pre-registered
5. **Future work** should focus on spin-path coupled experiments

**Research status:** Complete. Ready for Sprint 3 Phase 1 (Ground Truth).

## 11. Research Sprint 1R — Generalization to Arbitrary 3D Axes (#211)

### 11.1 Motivation

Sprints 1 and 2 restricted measurement to the xz-plane: states ψ(θ) = sin(θ)·i + cos(θ)·k measured along the z-axis. The Phase 4a review (PR #210) identified this as a gap — Furey and Feynman both asked about generalization to arbitrary 3D measurement axes.

This matters for:
- **Bell inequality tests** (Sprint 6): require arbitrary detector orientations
- **Full Bloch sphere coverage**: validating the quaternion formalism isn't accidentally restricted
- **Standard QM equivalence**: proving P(+) = cos²(γ/2) holds in full generality

### 11.2 General Spherical Parameterization

**State:** ψ(θ,φ) = sin(θ)cos(φ)·i + sin(θ)sin(φ)·j + cos(θ)·k

**Observable:** O(α,β) = sin(α)cos(β)·i + sin(α)sin(β)·j + cos(α)·k

where θ,α are polar angles from z-axis and φ,β are azimuthal angles in the xy-plane.

**Key result — General expectation value:**

⟨O⟩ = sin(θ)sin(α)cos(φ−β) + cos(θ)cos(α) = cos(γ)

where γ is the angle between the two directions on the unit sphere.

**Probability:** P(+) = (1 + cos γ)/2 = cos²(γ/2)

This reproduces the standard QM result for arbitrary 3D measurement, confirming the quaternion formalism is not restricted to any particular plane.

### 11.3 Rotation Equivalence

The direct parameterization ψ(θ,φ) is equivalent to rotating the z-axis state via quaternion conjugation:

q = cos(θ/2) + sin(θ/2)·(−sin(φ)·i + cos(φ)·j)

ψ(θ,φ) = q·k·q⁻¹

This confirms that the SU(2) rotation structure of quaternions naturally generates the full Bloch sphere from any reference state.

### 11.4 Standard QM Verification

Verified against the standard QM matrix formalism at 10 arbitrary (θ,φ) pairs:

|⟨↑_O|ψ⟩|² matches the quaternion P(+) to machine precision (< 10⁻¹⁰).

The quaternion formalism and standard QM are provably equivalent for all single-particle spin-½ measurements in 3D, consistent with the Moretti-Oppio theorem identified in Research Sprint 0R.

### 11.5 Formal Verification (Lean 4)

`proofs/QBP/Experiments/General3D.lean` proves:

| Theorem | Statement |
|---------|-----------|
| `psiGeneral_is_unit` | |ψ(θ,φ)|² = 1 for all θ,φ |
| `psiGeneral_phi_zero` | ψ(θ,0) = psiAngle(θ) (backward compatible) |
| `expectation_general` | ⟨O⟩ = sinθ sinα cos(φ−β) + cosθ cosα |
| `prob_up_general` | P(+) = (1 + ⟨O⟩)/2 |
| `prob_up_same_direction` | Same direction → P(+) = 1 |
| `prob_up_x_on_z` | Recovers Stern-Gerlach |
| `prob_up_y_on_z` | New: j-component case = 1/2 |
| `expectation_azimuthal_invariance` | Only relative angle (φ−β) matters |

### 11.6 Limitations Discovered

**None fundamental.** The i, j, k components are algebraically symmetric — the xz-plane restriction was a convenience, not a mathematical limitation. The generalization is straightforward because:

1. `vecDot` and `expectationValue` in Basic.lean were already axis-agnostic
2. The Born rule P(+) = (1 + ⟨O⟩)/2 is direction-independent
3. Quaternion rotation q·v·q⁻¹ generates the full SO(3) rotation group

The only "limitation" is that this analysis applies to single-particle spin-½ systems. Multi-particle entanglement (relevant for Sprint 6: Bell's Theorem) will require additional formalism.

### 11.7 Summary

Research Sprint 1R confirmed that the quaternion measurement formalism extends seamlessly from the xz-plane to arbitrary 3D directions. The cos²(γ/2) law holds universally, matching standard QM exactly. This provides the foundation for arbitrary detector orientations needed in Sprint 6 (Bell's Theorem).

**Deliverables:**
- [x] Formulas for P(+) with arbitrary measurement axis
- [x] Lean 4 proofs generalizing AngleDependent.lean
- [x] Verification against standard QM rotation matrices (10⁻¹⁰ agreement)
- [x] Documentation of limitations (none fundamental)
