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
def rotate_quaternion(q, axis, angle):
    """
    Rotate quaternion q by angle (radians) about axis (3-vector).
    Uses the conjugation formula: q' = r * q * r⁻¹
    where r = cos(θ/2) + sin(θ/2) * axis_quaternion
    """
    # Construct rotation quaternion (note: half-angle!)
    half = angle / 2
    r = np.array([np.cos(half),                    # real part
                  np.sin(half) * axis[0],          # i component
                  np.sin(half) * axis[1],          # j component
                  np.sin(half) * axis[2]])         # k component

    # Apply conjugation: r * q * r⁻¹
    return quat_mul(quat_mul(r, q), quat_conjugate(r))
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
