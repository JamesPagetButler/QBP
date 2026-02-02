# Expected Results for Bell's Theorem Experiments

This document outlines the real-world experimental results for Bell's Theorem tests, establishing the "ground truth" for our synthetic test of quantum entanglement and non-locality.

## 1. The Phenomenon

Bell's theorem addresses the "spooky action at a distance" paradox of quantum entanglement. It proves that no physical theory based on the classical principles of **locality** (effects can't travel faster than light) and **realism** (properties exist before they are measured) can reproduce all the predictions of quantum mechanics.

Experiments consistently show that the correlations between entangled particles are stronger than any classical theory allows.

## 2. Experimental Method

A typical Bell test experiment follows this structure:

1.  **Source:** A source creates pairs of entangled particles (e.g., photons with entangled polarization) and sends them in opposite directions.
2.  **Detectors:** Two independent detector stations, "Alice" and "Bob," are placed far apart.
3.  **Random Settings:** At each station, a measurement setting (e.g., the angle of a polarization filter) is chosen randomly and independently for each incoming particle, after the pair has been created.
4.  **Measurement:** Alice and Bob each measure their particle according to their randomly chosen setting and record the outcome (e.g., `+1` for pass, `-1` for fail).
5.  **Correlation:** After repeating the process for thousands of pairs, they compare their lists of settings and outcomes to calculate the statistical correlation between their measurements.

## 3. Key Insights & Ground Truth

The crucial result is not a single value, but a statistical correlation that violates a "Bell Inequality," such as the CHSH inequality.

*   **The CHSH Inequality:** A common formulation of Bell's theorem. It states that for any local-realist theory, a certain combination of correlation measurements, `S`, cannot exceed 2.
    `|S| ≤ 2`  (Classical Limit)

*   **Quantum Prediction:** Quantum mechanics predicts that for specific angles chosen by Alice and Bob, this value `S` can reach up to `2√2 ≈ 2.828`.

*   **Observed Quantum Result:** Decades of increasingly precise experiments have overwhelmingly confirmed the quantum prediction. The observed correlations consistently violate the classical limit of 2, often approaching the quantum maximum of `2√2`.

## 4. Success Criteria for Our Synthetic Test

This is a profound test of our formalism's ability to handle multi-particle, non-local systems.

1.  **Representing Entanglement:** Our first, and most significant, theoretical challenge is to define a **two-particle entangled state** within the quaternionic framework. This cannot be a simple product of two independent state quaternions; it must be a single state object that encodes the non-local connection.
2.  **Modeling the Measurement:** Our synthetic test must simulate the full Bell test experiment:
    *   Create the entangled two-particle state.
    *   For thousands of simulated pairs, randomly select measurement settings (observables) for Alice and Bob.
    *   Apply the `qphysics.measure()` function to each particle against its respective observable.
    *   Record the pairs of outcomes.
3.  **Violating the Inequality:** The primary success criterion is that the statistical correlations calculated from the simulation results **must violate the CHSH inequality**. The calculated `S` value must be significantly greater than 2 and should approach the quantum-predicted value of `2√2` for the chosen angles.

Successfully modeling the violation of Bell's inequality would demonstrate that our quaternionic framework is not a classical "hidden variable" theory and can correctly reproduce one of the deepest and most counter-intuitive features of quantum reality.
