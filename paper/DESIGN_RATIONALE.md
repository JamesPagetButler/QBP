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
