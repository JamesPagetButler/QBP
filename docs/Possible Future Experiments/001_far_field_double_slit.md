# 001: Far-Field Double-Slit with Single-Atom Wave Packets

## Motivation

Sprint 3 (Experiment 03, double-slit) produced near-field BPM results only. The simulation propagates ~32 nm — far too short for Fraunhofer far-field conditions (which require mm-scale propagation). As a result:

- **BPM baseline visibility V ≈ 0.553** (vs analytical far-field V = 1.0)
- The QBP quaternionic coupling signal (V reduction of ~8%) is real but sits on top of a near-field baseline, not a clean far-field fringe pattern
- We have no far-field QBP prediction to compare against actual double-slit experiments

A far-field simulation would let us predict what a real interferometer would measure, making the QBP theory directly testable.

## Physical Setup — Ketterle Group (MIT, 2025)

A recent paper provides an interesting experimental configuration:

> **"Coherent and Incoherent Light Scattering by Single-Atom Wave Packets"**
> Fedoseev, Lin, Lu, Lee, Lyu & Ketterle
> *Physical Review Letters* **135**, 043601 (July 2025)
> DOI: [10.1103/zwhd-1k2t](https://doi.org/10.1103/zwhd-1k2t)

Key features:
- Single photons scattered off Heisenberg uncertainty-limited atomic wave packets
- Ultracold atoms in free space (Mott insulator source)
- Coherent vs incoherent scattering fraction depends on wave packet size relative to photon wavelength
- Directly probes atom-photon entanglement and which-way information

This setup is relevant because the QBP predicts that quaternionic coupling modifies the coherent/incoherent partition — precisely what this experiment measures.

## What We'd Simulate

- **Far-field propagation:** Either extend BPM to mm scale (computationally expensive) or use Fourier-optics far-field transform from near-field BPM output
- **Single-atom wave packets:** Match the Ketterle group's parameters (atom species, wavelength, wave packet size)
- **Observable:** Coherent scattering fraction as a function of quaternionic coupling strength U₁
- **Comparison:** QBP prediction vs standard QM prediction vs experimental data (if available)

## Expected QBP Signature

The quaternionic coupling transfers amplitude from the complex component to the quaternionic component via SO(4) rotation. In a far-field interference experiment, this should:

1. Reduce fringe visibility (as seen in near-field Sprint 3 results)
2. Modify the coherent/incoherent scattering ratio — the quaternionic component acts as an internal degree of freedom that carries which-way information
3. Produce a coupling-strength-dependent shift in the coherence fraction that differs from standard QM decoherence

## Key References

- Fedoseev et al., PRL 135, 043601 (2025) — DOI: 10.1103/zwhd-1k2t
- Sprint 3 results: `analysis/03_double_slit/RESULTS.md`
- Ground truth: `research/03_double_slit_expected_results.md`

## Feasibility Notes

- **BPM capability:** Current BPM handles near-field only. Far-field would require either (a) much larger grid + longer propagation (very expensive), or (b) Fourier transform of near-field output to far-field (moderate effort, new code needed)
- **Computational cost:** Far-field BPM at mm scale with nm resolution is infeasible (~10⁷ grid points per axis). Fourier-optics approach is the practical path.
- **Blockers:**
  - Need to implement Fourier far-field transform
  - Need Ketterle group's experimental parameters (atom species, trap frequencies, photon wavelength)
  - Full paper access required (currently paywalled)

## Status

[x] Idea | [ ] Scoped | [ ] Ready to schedule
