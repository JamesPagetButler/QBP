# QBP Project Plan & TODO

This document serves as the official project plan, tracking our high-level roadmap and the granular tasks required to achieve our goals.

---

## Project Roadmap (The Eight-Fold Path)

This is our strategic guide. We will tackle these items sequentially.

1.  **[In Progress]** The Stern-Gerlach Experiment
2.  **[Next]** The Double-Slit Experiment
3.  **[Upcoming]** The Lamb Shift
4.  **[Upcoming]** Bell's Theorem Experiments
5.  **[Upcoming]** Derivation of Particle Statistics
6.  **[Upcoming]** Modeling Positronium's Ground State
7.  **[Upcoming]** The Hydrogen Atom Spectrum
8.  **[Aspirational]** The Anomalous Magnetic Moment of the Electron (g-2)
9.  **[Aspirational]** Gravitational Lensing & Galactic Rotation Curves

---

## Current Sprint: Ground Truth Analysis

This is our highest priority. We must establish the real-world experimental results we aim to match with our synthetic tests.

-   **[In Progress] Action 0:** For each test on the Eight-Fold Path, search for real-world data and meta-analyses. Document the key expected results in a corresponding `/research` directory file. Start with Stern-Gerlach.

---

## Next Sprint: Stern-Gerlach Implementation & Refinement

These are the immediate action items derived from the review of Pull Request #13. We will work on these locally.

### Engineering & Refinement (Knuth's Feedback)
-   **[TODO] Action A:** Add an optional `seed` parameter to the `measure` function in `src/qphysics.py` for reproducible tests.
-   **[TODO] Action B:** Add Python type hints to all functions in `src/qphysics.py`.
-   **[TODO] Action C:** Vectorize the simulation loop in `experiments/01_stern_gerlach/simulate.py` using NumPy for performance.

### New Experiments (Sabine's & Feynman's Feedback)
-   **[TODO] Action D:** Create a new synthetic experiment, `experiments/02_angle_test/simulate_angle.py`, to verify the measurement probability formula at different angles.

---

## Future Tasks & Research Backlog

These are important tasks to be addressed after the current sprint.

-   **[Backlog] Action E:** Open a GitHub Issue for the "Theoretical Investigation: Physical Meaning of the Quaternion Scalar Component" to address Furey's and Grothendieck's feedback.
-   **[Backlog]** Implement a basic CI/CD pipeline using GitHub Actions.
-   **[Backlog]** Document the Lean 4 setup process.

---

## Completed Tasks

- **Initial Project Setup & Constitution:** All core documents (`CONTRIBUTING.md`, `README.md`, etc.) are in place.
- **Initial Red Team Review:** Completed and feedback incorporated.
- **`qphysics.py` v0.1:** Initial implementation of Axioms 1-3 and Measurement Postulate created.
- **Synthetic Experiment v1:** `simulate.py` for Stern-Gerlach created.
- **PR #13 Review:** Completed by both Red Team and Gemini.