# Expected Results for the Stern-Gerlach Experiment (Ground Truth)

This document outlines the real-world experimental results and formal theoretical predictions for the Stern-Gerlach (S-G) experiment, establishing the "ground truth" that our synthetic tests must replicate.

---

## 1. The Experiment

A beam of neutral silver atoms is passed through an inhomogeneous magnetic field. The deflection of the atoms is then measured on a detector screen.

---

## 2. Classical vs. Quantum Predictions

*   **Classical Prediction:** The magnetic moments of the atoms are assumed to be randomly oriented in all possible directions. This would result in the atoms creating a single, continuous line or smudge on the detector screen.

*   **Observed Quantum Result:** In reality, the beam splits into **two distinct, discrete spots**. No atoms are found between these two points. This observation is a cornerstone of quantum mechanics and reveals the quantization of spin.

---

## 3. Empirical Anchor

**Data type:** Qualitative-binary

### Key Measured Values

| Quantity | Measured Value | Uncertainty | Source | Year | DOI / Identifier |
|----------|---------------|-------------|--------|------|------------------|
| Beam splitting | Two discrete spots (spin-up, spin-down) | Binary outcome — no intermediate values observed | Gerlach, W. & Stern, O. | 1922 | Z. Phys. 9, 349–352 |
| Relative intensity | Approximately equal intensity in both spots | Statistical (N-dependent) | Gerlach & Stern | 1922 | Z. Phys. 9, 349–352 |

### Experimental Confidence

| Factor | Assessment |
|--------|------------|
| Replication status | Replicated thousands of times across all major physics laboratories worldwide. Standard undergraduate lab demonstration. |
| Measurement precision | Binary outcome — the measurement is whether the beam splits into two discrete spots or a continuous smear. No precision issue. |
| Relevance to QBP test | Direct — QBP must reproduce the discrete two-spot splitting (spin quantization) and the 50/50 probability split for orthogonal state/measurement configurations. |

### What "Matching Reality" Means

The Stern-Gerlach experiment produces a qualitative-binary outcome: a beam of silver atoms either splits into two discrete spots or it doesn't. There is no "close enough" — any continuous distribution would falsify both QM and QBP.

For the specific configuration modeled here (spin-x prepared, spin-z measured), "matching reality" means: (1) the measurement function returns only +1 or -1, never any other value, and (2) over many trials, the ratio converges to 50/50 within statistical bounds. The 50/50 ratio for orthogonal axes is a consequence of spin quantization that has been confirmed in every Stern-Gerlach experiment since 1922.

### Null Results and Constraints

No known null results specific to this phenomenon. The discrete two-spot splitting has been universally observed for spin-1/2 particles; no experiment has ever found intermediate outcomes.

---

## 4. Formal Derivation from QBP Axioms

The QBP framework must mathematically reproduce the observed quantum result. We model the most common S-G configuration: preparing a particle with spin along the x-axis and measuring it along the z-axis.

1.  **State Preparation (Spin-X):** A particle with spin oriented along the +x axis is represented by the state quaternion `ψ`. Per our axioms, this corresponds to the pure quaternion `i`.
    *   `ψ = i = ⟨0, 1, 0, 0⟩`

2.  **Observable (Spin-Z):** The measurement of spin along the z-axis is represented by the observable quaternion `O_z`. Per our axioms, this corresponds to the pure quaternion `k`.
    *   `O_z = k = ⟨0, 0, 0, 1⟩`

3.  **Expectation Value Calculation:** The expectation value `⟨O_z⟩` for the state `ψ` is calculated as `⟨O_z⟩ = vecDot(ψ, O_z)`, where `vecDot` is the dot product of the vector parts of the quaternions.
    *   `vecDot(ψ, O_z) = (ψ_i * O_z_i) + (ψ_j * O_z_j) + (ψ_k * O_z_k)`
    *   `vecDot(i, k) = (1 * 0) + (0 * 0) + (0 * 1) = 0`
    *   `⟨O_z⟩ = 0`

4.  **Probability Calculation:** The probability of measuring spin-up (`+1`) or spin-down (`-1`) is derived from the expectation value:
    *   `P(+) = (1 + ⟨O_z⟩) / 2`
    *   `P(-) = (1 - ⟨O_z⟩) / 2`

5.  **Predicted Probabilities:** Substituting the calculated expectation value `⟨O_z⟩ = 0`:
    *   `P(+) = (1 + 0) / 2 = 0.5` (50% probability of spin-up)
    *   `P(-) = (1 - 0) / 2 = 0.5` (50% probability of spin-down)

This formal derivation shows that the QBP framework correctly predicts a 50/50 probability split for orthogonal state/measurement configurations, which is the key quantitative outcome of the S-G experiment.

---

## 5. Prediction Classification

| Prediction | Type | Standard QM | Notes |
|------------|------|-------------|-------|
| P(+) = P(-) = 0.5 for orthogonal states | Validation | 0.5 | Identical to QM |
| Binary outcomes only (+1, -1) | Validation | Same | Spin quantization |

### Classification Summary

**Validation:** This experiment confirms QBP reproduces standard quantum mechanics for the orthogonal state/measurement case (spin-x prepared, spin-z measured). It does not distinguish QBP from QM.

**Novel predictions:** None for this experiment. The 50/50 split for orthogonal states is a foundational QM result that QBP must reproduce to be viable.

### Implications

Experiment 01 establishes that QBP is *consistent* with QM for the simplest spin measurement case. This is necessary but not sufficient for QBP to be a distinct physical theory. See #167 for ongoing research into where QBP predictions might diverge from QM.

---

## 6. Quantitative Predictions & Acceptance Criteria

Our `experiments/01_stern_gerlach/simulate.py` script will be considered successful if it meets the following criteria, which directly correspond to the real-world experimental results and our formal derivation.

### 6.1 Primary Acceptance Criteria

1.  **Binary Measurement Outcome:** The `qphysics.measure()` function must only ever return one of two discrete values: `+1` or `-1`. No other values are permissible.

2.  **Statistical Distribution:** For a simulation of `N` particles prepared in a spin-X state and measured along the Z-axis, the final tally of outcomes must match the expected 50/50 distribution within a statistically significant tolerance.
    *   **Expected Mean Count (Up):** `μ_+ = N * P(+) = N * 0.5`
    *   **Expected Mean Count (Down):** `μ_- = N * P(-) = N * 0.5`
    *   **Standard Deviation (Binomial):** The standard deviation of the count is `σ = sqrt(N * P(+) * P(-)) = sqrt(N * 0.5 * 0.5) = 0.5 * sqrt(N)`.
    *   **Acceptance Criterion:** The measured count for both spin-up and spin-down outcomes must fall within **3 standard deviations (3σ)** of the expected mean count.
        *   `|Count(+) - μ_+| <= 3σ`
        *   `|Count(-) - μ_-| <= 3σ`

### 6.2 Simulation Parameters

To ensure statistically significant results, our synthetic experiments will adhere to a standard number of trials.

*   **Number of Trials (N):** `1,000,000`
*   **Justification:** A trial count of one million provides a statistical error on the order of `1/√N` ≈ 0.1%. For N=1,000,000, `μ = 500,000` and `σ = 0.5 * sqrt(1,000,000) = 500`. The 3σ acceptance range is `500,000 ± 1,500`. This high level of precision allows us to be very confident that our simulation results reflect the true probabilistic nature of our model, rather than statistical noise.
*   **Computational Cost:** The estimated computation time for 1,000,000 trials on the development machine is approximately 38 seconds, which is an acceptable cost for this level of certainty.

---

## 7. References

1.  Gerlach, W.; Stern, O. (1922). "Der experimentelle Nachweis der Richtungsquantelung im Magnetfeld". *Zeitschrift für Physik*. 9 (1): 349–352.
2.  Griffiths, David J.; Schroeter, Darrell F. (2018). *Introduction to Quantum Mechanics*. Cambridge University Press.
