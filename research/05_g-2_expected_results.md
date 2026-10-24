# Expected Results for the Anomalous Magnetic Moment of the Electron (g-2)

This document outlines the real-world experimental results for the g-2 of the electron. This is an **Aspirational Milestone** due to the extraordinary precision required in both theory and experiment.

## 1. The Phenomenon

The g-factor of a particle relates its magnetic moment to its angular momentum. A simple relativistic theory (the Dirac equation) predicts the g-factor of a point-like electron to be **exactly g = 2**.

The "anomalous magnetic moment" is the experimentally measured deviation of `g` from 2. This tiny anomaly is one of the most precisely measured quantities in all of physics.

*   **Observed Value:** `g ≈ 2.002319304...`
*   **The "Anomaly" (aₑ):** `(g - 2) / 2 ≈ 0.001159652...`

## 2. Experimental Method (Penning Trap)

Modern, high-precision measurements are performed by isolating a *single electron* in a device called a Penning Trap.

1.  **Confinement:** A combination of a strong, uniform magnetic field and a weaker electric field traps the electron, forcing it into a tight, circular "cyclotron" motion.
2.  **Precession:** The electron's intrinsic spin causes it to "wobble" or precess around the magnetic field lines, like a tiny spinning top.
3.  **Frequency Measurement:** Scientists use microwaves to exquisitely measure the frequency of the electron's cyclotron motion and the frequency of its spin precession.
4.  **Result:** The g-factor is calculated from the ratio of these two frequencies. The tiny difference between them reveals the anomaly.

## 3. Key Insights & Ground Truth

The fact that `g` is not exactly 2 is a profound confirmation of Quantum Electrodynamics (QED).

*   **The Cause:** The anomaly is caused by the electron interacting with the quantum vacuum. In QED, this is described as the electron interacting with a "cloud" of virtual particles (primarily virtual photons) that constantly pop in and out of existence around it. This self-interaction slightly alters the electron's magnetic moment.
*   **Significance:** The stunning agreement (to more than 10 significant figures) between the experimentally measured value of `g-2` and the value calculated using QED is the single most powerful validation of the Standard Model of particle physics.

## 4. Success Criteria for Our Synthetic Test

This is an extremely advanced test. Our quaternionic formalism must have a rich enough structure to account for self-interaction effects.

*   **Primary Goal:** Our formalism must naturally predict that the g-factor for a fundamental particle is **not exactly 2**. We must be able to derive a self-interaction correction within our quaternion algebra that makes `g > 2`.
*   **Quantitative Goal (Aspirational):** The ultimate goal would be to develop a method to calculate the size of this anomaly within our formalism and show that it matches the first few terms of the QED prediction (e.g., the Schwinger term `α / 2π`).

Achieving the primary goal would be a monumental success. Matching the quantitative value, even approximately, would be a revolutionary achievement for this theoretical framework.

## 5. Prediction Classification

Classification rule (#170 / #736): a row is **Validation** only where this document states that QBP reproduces the standard value; **Novel** only where it states a QBP-specific deviation with a number; otherwise **OPEN**, with the missing statement named. The Notes quote the line relied on.

| Prediction | Type | Standard value (as stated here) | Notes |
|------------|------|---------------------------------|-------|
| g is not exactly 2 (g > 2) | OPEN | "`g ≈ 2.002319304...`" (§1) | Stated only as a goal: "Our formalism must naturally predict that the g-factor for a fundamental particle is **not exactly 2**" (§4). Missing: a QBP derivation of the self-interaction correction — no claim here that QBP reproduces it, and no QBP-specific number. |
| Anomaly aₑ = (g − 2)/2, leading term α/2π | OPEN | "`(g - 2) / 2 ≈ 0.001159652...`" (§1); "the Schwinger term `α / 2π`" (§4) | Stated only as an aspiration: "Quantitative Goal (Aspirational): … show that it matches the first few terms of the QED prediction" (§4). Missing: a QBP-derived value of aₑ to compare against it. |

### Classification Summary

**Validation:** none decidable from this document. It records the QED/experimental ground truth (§1–§3) and the success criteria a QBP model must meet (§4); it does not state that QBP reproduces either quantity above.

**Novel predictions:** none stated. No QBP-specific deviation with a number appears in this document.

### Implications

Both rows are **OPEN**: the classification cannot be made until the Phase 1 ground-truth work (#31) adds the QBP-side derivation of each quantity. A row becomes **Validation** if the document then states that QBP reproduces the standard value, or **Novel** if it states a QBP-specific deviation with a number; the §4 criteria are the gate. Indexed under #170 / #736 — cite, don't assert.
