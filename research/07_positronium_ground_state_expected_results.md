# Expected Results for Modeling Positronium's Ground State

This document outlines the real-world experimental results for the ground state of Positronium (Ps), establishing the "ground truth" for our first synthetic test of a multi-particle bound state.

## 1. The System

Positronium is an "exotic atom" composed of an electron and its antiparticle, the positron, bound together by their mutual electromagnetic attraction. It is a fundamental two-body quantum system, analogous to a hydrogen atom but with a positron replacing the proton. Because the electron and positron have equal mass, the reduced mass of the system is approximately half that of the hydrogen atom, leading to binding energies that are roughly half of hydrogen's.

## 2. The Phenomenon: Hyperfine Splitting

While the simple Bohr model predicts a ground state binding energy of approximately -6.8 eV, the most critical feature of the Positronium ground state (n=1) is that it is not a single energy level. Due to the interaction between the intrinsic magnetic moments (spins) of the electron and positron, this level is split into two distinct sub-levels. This is known as **hyperfine splitting**.

1.  **Para-positronium (p-Ps):**
    *   **Spins:** Anti-parallel (total spin S=0).
    *   **Energy Level:** This is the **lower** energy ground state.
    *   **Decay:** Annihilates into two gamma-ray photons.

2.  **Ortho-positronium (o-Ps):**
    *   **Spins:** Parallel (total spin S=1).
    *   **Energy Level:** This is the **higher** energy ground state.
    *   **Decay:** Annihilates into three gamma-ray photons.

*   **Observed Energy Difference:** The energy splitting between the o-Ps and p-Ps states is approximately **203 GHz**.

## 3. Experimental Method

Experiments measure this energy splitting with high precision using spectroscopy:
1.  **Production:** Positronium is formed, often in a gas or powder.
2.  **Interaction:** The atoms are irradiated with microwaves of a precise frequency.
3.  **Transition:** If the microwave frequency exactly matches the energy gap between the p-Ps and o-Ps states, it can induce a transition between them.
4.  **Detection:** This transition is detected by observing a change in the annihilation gamma-ray signals (e.g., a change from the 3-photon signature of o-Ps to the 2-photon signature of p-Ps).

## 4. Success Criteria for Our Synthetic Test

This is a critical test of our formalism's ability to handle multi-particle systems and their interactions.

1.  **Represent the Two-Particle State:** Our framework must be able to represent the combined state of the electron-positron system, likely via a tensor product of two quaternionic states: `Ψ = ψ_electron ⊗ ψ_positron`.
2.  **Model the Spin-Spin Interaction:** We must define a Hamiltonian operator `H_interaction` within our quaternionic formalism that represents the interaction between the two particle spins.
3.  **Predict Energy Splitting:** When this Hamiltonian is applied to the two-particle system, it must produce two distinct energy eigenvalues. The formalism must show that the state with anti-parallel spins (p-Ps) has a lower energy than the state with parallel spins (o-Ps).
4.  **Quantitative Goal (Aspirational):** The calculated energy difference between the simulated p-Ps and o-Ps states should be reasonably close to the experimentally measured value of ~203 GHz.

Successfully modeling the hyperfine splitting of Positronium would demonstrate our framework's potential to describe interacting particles, a crucial step beyond single-particle quantum mechanics.
