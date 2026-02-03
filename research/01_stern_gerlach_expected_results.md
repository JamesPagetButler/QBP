# Expected Results for the Stern-Gerlach Experiment

This document outlines the real-world experimental results for the Stern-Gerlach (S-G) experiment, establishing the "ground truth" that our synthetic tests must replicate.

## 1. The Experiment

A beam of neutral silver atoms is passed through an inhomogeneous magnetic field. The deflection of the atoms is then measured on a detector screen.

## 2. Classical vs. Quantum Predictions

*   **Classical Prediction:** The magnetic moments of the atoms are assumed to be randomly oriented in all possible directions. This would result in the atoms creating a single, continuous line or smudge on the detector screen.

*   **Observed Quantum Result:** In reality, the beam splits into **two distinct, discrete spots**. No atoms are found between these two points.

## 3. Key Insights & Ground Truth

The observed result is a cornerstone of quantum mechanics and reveals several key truths that our model must reproduce:

1.  **Binary Quantization:** The most critical result is the quantization of the measurement outcome. There are only two possible results, "spin up" and "spin down," corresponding to the two spots on the screen. Our `measure` function must *only* return `+1` or `-1`.

2.  **Probabilistic Nature:** When the initial state of the particles is a superposition relative to the measurement axis (e.g., the particle's spin is oriented along the 'X' axis while the magnetic field is along the 'Z' axis), the outcome is probabilistic.

3.  **Expected Statistical Distribution:** For an initial state that is an equal superposition (e.g., spin-X measured against a Z-axis field), the expected statistical distribution of outcomes over many measurements is **50% "up" and 50% "down"**.

## 4. Success Criteria for Our Synthetic Test

Our `experiments/01_stern_gerlach/simulate.py` script will be considered successful if it meets the following criteria, which directly correspond to the real-world experimental results:

*   The `qphysics.measure()` function must only ever return one of two discrete values (`+1` or `-1`).
*   When simulating a large number of particles prepared in an equal superposition state (e.g., `create_state_from_vector([1, 0, 0])`), the final tally of outcomes must be approximately **50% `+1`** and **50% `-1`**.

## 5. Simulation Parameters

To ensure statistically significant results, our synthetic experiments will adhere to a standard number of trials.

*   **Number of Trials (N):** 1,000,000
*   **Justification:** A trial count of one million provides a statistical error on the order of `1/√N` ≈ 0.1%. This high level of precision allows us to be very confident that our simulation results reflect the true probabilistic nature of our model, rather than statistical noise.
*   **Computational Cost:** The estimated computation time for 1,000,000 trials on the development machine is approximately 38 seconds, which is an acceptable cost for this level of certainty.
