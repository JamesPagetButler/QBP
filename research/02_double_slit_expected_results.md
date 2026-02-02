# Expected Results for the Double-Slit Experiment

This document outlines the real-world experimental results for the Double-Slit experiment (with electrons), establishing the "ground truth" that our synthetic tests must replicate.

## 1. Experimental Method

1.  **Source:** An electron gun fires single electrons, one at a time, towards a barrier.
2.  **Barrier:** The barrier has two narrow, parallel slits.
3.  **Detector:** A screen behind the barrier detects and records the impact position of each electron.

The experiment is run under two key conditions:
*   **Condition A: No "Which-Path" Information.** The experiment runs without any detector at the slits to determine which slit each electron passes through.
*   **Condition B: With "Which-Path" Information.** A detector is placed at one or both slits to observe which path each electron takes.

## 2. Expected Results & Success Criteria

The results of this experiment are fundamentally different depending on whether a measurement is performed at the slits. Our model must successfully reproduce both outcomes.

### Scenario A: No "Which-Path" Information

*   **Observed Quantum Result:** When electrons are fired one by one, their individual impact points on the detector screen appear random. However, as thousands of impacts accumulate, they do **not** form two simple bands behind the slits. Instead, they form a **classic interference pattern** of multiple alternating bright and dark fringes.
*   **Key Insight:** This demonstrates the wave-particle duality of matter. Each individual electron behaves like a wave, passing through *both* slits simultaneously and interfering with itself. Its final position is determined by the probability wave (the wavefunction).
*   **Success Criteria for our Synthetic Test:**
    1.  Our model must represent the electron's state in a way that can propagate through two paths simultaneously.
    2.  The formalism must include a mechanism for these two paths to "interfere."
    3.  The final probability distribution for the electron's position, calculated by our model, must show the characteristic multi-fringe interference pattern.

### Scenario B: With "Which-Path" Information

*   **Observed Quantum Result:** If a detector is placed at the slits to determine which path each electron takes, the interference pattern **vanishes completely**. The electrons behave like classical particles, and two distinct bands form on the detector screen, one directly behind each slit.
*   **Key Insight:** The act of measuring the electron's position at the slits forces it to "choose" a single path. This measurement "collapses the wavefunction," destroying the superposition that is necessary for interference.
*   **Success Criteria for our Synthetic Test:**
    1.  Our formalism must include a "measurement" operation that corresponds to observing the electron's position at a slit.
    2.  When this measurement operation is applied mid-way through the simulation, the final probability distribution must show only two distinct bands, with the interference pattern eliminated.

Successfully modeling both Scenarios A and B will be a major validation of our quaternionic framework's ability to handle superposition and the measurement problem.
