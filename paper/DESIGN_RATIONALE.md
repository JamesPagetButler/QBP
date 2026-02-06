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

During the development of Experiment 02 (Angle-Dependent Measurement), we discovered that the original expectation value formula `⟨O⟩ = 2 × vecDot(ψ, O)` produced invalid probabilities (> 1) for non-orthogonal configurations. The corrected formula `⟨O⟩ = vecDot(ψ, O)` was validated in Experiment 02 and subsequently confirmed to be consistent with Experiment 01 results (where the factor of 2 had no effect because `2 × 0 = 0`).

This correction is documented in both `proofs/QBP/Basic.lean` and `src/qphysics.py`.

### 5.3 Formal Verification as a Design Tool

The Lean 4 proofs for Experiment 01 (`proofs/QBP/Experiments/SternGerlach.lean`) served not just as verification but as a **design tool**. Writing formal proofs forced us to make every assumption explicit:

- The state must be a pure quaternion (Axiom 1 compliance)
- The observable must be a pure quaternion (Axiom 2 compliance)
- The probability formula must map to [0, 1] for all valid inputs

The Phase 4b review process (Claude reviewing Gemini's proofs) caught no errors but confirmed the tight correspondence between the formal proofs and the Python implementation.

### 5.4 Interactive Proof Visualization

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

**Primary emergent phenomenon:** The emergence of probability from geometry. This is philosophically significant — the Born rule's probabilistic nature arises from the algebraic structure of quaternions, not as a separate postulate.

### 6.3 Open Questions

The following questions arose from Sprint 1 and require further investigation:

1. **Expectation value bounds:** Is `⟨O⟩ ∈ [-1, 1]` formally guaranteed for all unit quaternion states and pure quaternion observables? This constraint is implicit in our probability formula but not yet proven in Lean.

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

#### 6.4.2 Derivation of cos²(θ/2)

For a spin-z state `ψ = k` measured along an axis rotated by θ in the xz-plane:

1. The rotated observable is `O_θ = q·k·q⁻¹` where `q = cos(θ/2) + sin(θ/2)·j`
2. Expectation value: `⟨O_θ⟩ = vecDot(k, O_θ) = cos(θ)`
3. Probability: `P(+) = (1 + cos(θ))/2 = cos²(θ/2)` (half-angle identity)

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
