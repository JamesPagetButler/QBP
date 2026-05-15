# Session 13 Working Notes (2026-05-11)

## CCvS Verification (T1–T4) and the Parent BH Lifecycle

**Status:** Working notes, not formal theory. Captures the live thinking from Session 13 for handoff to next session. Items that have hardened are reflected in QBP-Theory v3.1 and CTH v5.3; items captured here are conjectures and research directions awaiting development.

---

## Part 1: T1–T4 Verification of the CCvS Comparison

### Context

Gemini's critique referenced Chamseddine-Connes-van Suijlekom 2018 ("Entropy and the Spectral Action", *Commun. Math. Phys.* 373, 457–471, arXiv:1809.02944) without identifying its significance for QBP. The paper proves that the von Neumann entropy of the fermionic second quantisation of a spectral triple equals the spectral action for a specific universal test function:

$$\chi(x) = h(\sqrt{x}), \qquad h(x) = \frac{x}{1+e^x} + \log(1 + e^{-x})$$

i.e., the Fermi-Dirac vacuum entropy function. The heat-expansion coefficients are:

$$\gamma(a) = \frac{1 - 2^{-2a}}{a} \cdot \pi^{-a} \cdot \xi(2a)$$

where ξ is the Riemann xi function. The 4D coefficients are γ(−2) = 225ζ(5)/4 ≈ 58.33 and γ(−1) = 9ζ(3)/2 ≈ 5.41.

The hypothesis tested: is CCvS's χ the same as (or simply related to) QBP's f(u) = A(1 + 7u − 2.5u²)exp(−u)?

### Tests run (mp-arithmetic, 50 decimal digits)

**T1: Numerical comparison of moments and the f₄ cancellation hypothesis.** FAILED. At QBP's stated cutoff Λ_c = 0.04 M_Pl, CCvS γ(−2) · Λ_c⁴ ≈ 1.5×10⁻⁴ M_Pl⁴. Observed ρ_Λ ≈ 1.2×10⁻¹⁰⁶ M_Pl⁴. The accretion-driven Λ_eff = 2AB is the same order as observed, so it cannot cancel the 10⁻⁴ contribution. Mismatch: ~10¹⁰² orders of magnitude.

**T2: Cayley-Dickson pattern in CCvS coefficients.** CONFIRMED. The closed form γ(−a) for positive integer a contains the factor 2^(2a) − 1 = dim Im 𝒜_(2a), embedding the even-level Cayley-Dickson tower:

| a | 2^(2a)−1 | CD level 2a | Algebra |
|---|---|---|---|
| 1 | 3 | 2 | ℍ |
| 2 | 15 | 4 | 𝕊 |
| 3 | 63 | 6 | chingons (dim 64) |
| 4 | 255 | 8 | dim 256 |

Odd-level algebras (ℝ, ℂ, 𝕆, pathions) do NOT appear in integer-a coefficients. Open question: do they appear in half-integer-a coefficients γ(±1/2), γ(±3/2)?

**T3: Functional-equation map between f and χ.** No simple map exists. Constant-rescaling gives inconsistent A values (0.69 from f₀, 1.80 from f₂). Functional-equation reflection γ(a) ↔ γ(1/2 − a) produces non-constant ratios (15, 90, 547, 3342 across the table). The duality operates at the level of which ζ values appear (structural), not at the level of producing equal coefficients (numerical).

**T4: Fermion/boson sectoring.** Dissolves. Both CCvS and QBP compute one-particle traces of the same Dirac operator. The difference is the test function, not the trace. There is no decomposition of f that recovers χ.

### Net result

- f(u) and χ(u) are different test functions for different observables on the same spectral triple. The candidate function-level identity is killed.
- The Cayley-Dickson structural confluence (T2) is real and independent of the function-level disconfirmation. CCvS's first-principles entropy function has the QBP-relevant Cayley-Dickson tower written into its zeta moments. ℍ at level 2 (where QBP's daughter universe lives) and 𝕊 at level 4 (where QBP's inter-cell topology / information-loss seams live) are exactly the algebras present.
- The "f₄ = 0 from Axiom 1" derivation is killed. f₄ = 0 itself survives on consistency grounds (Λ_eff = 2AB needs no additional contribution) but cannot be derived from the information-preservation axiom.

### CTH updates (v5.2 → v5.3)

- **CONV-spectral-entropy-zeta** (status untested → marginal): T1–T4 results embedded; function-level convergence disconfirmed; spectral-action machinery consistent.
- **CONV-cd-tower-in-zeta-moments** (NEW, status coherent): Even-level CD tower in CCvS coefficients. Tier 4 external structural confluence.
- **KILLED-f4-info-theoretic-justification** (NEW, status incoherent): Axiom 1 → f₄ = 0 argument does not survive the direct entropy computation.
- **WISDOM-003** (revised, v3.1 addendum): "There is only f(u)" → "The spectral triple is the invariant; test functions select observables."

---

## Part 2: The Parent BH Lifecycle and the Hawking-Cycle Hypothesis

### The asymmetry of information accounting

Modern black-hole physics has converged on the resolution that the BH information paradox is an artefact of observer perspective:

- **External observer (Universe 1, parent):** unitary Hawking evolution; the Page curve turns over at half-evaporation; information is preserved in the entanglement structure of the radiation.
- **Internal observer (Universe 2, our universe = inside the BH):** matter crosses the horizon and disappears from view; the inside sees thermal radiation at temperature T_H with no recoverable information.

Both descriptions are correct. In QBP language:
- Universe 1 (parent, 𝕆-physics) ≅ external observer
- Universe 2 (daughter, ℍ-physics, us) ≅ internal observer
- "Information loss at the sedenion seam" = the daughter's view of what is in fact unitary evolution from the parent's view

This sharpens DERIV-sedenion (sedenion zero divisors = information-loss seams). The seams are where the inside observer's accessible information set is bounded by what crosses the horizon. Information is preserved globally (Universe 1's perspective always sees unitarity); locally inside Universe 2, the boundary appears as information destruction.

### The parent BH evolves through cycles

The parent BH's mass evolves under two competing processes:

$$\frac{dM}{dt} = \dot{M}_\text{in}(t) - \frac{C}{M^2}, \qquad C = \frac{\hbar c^4}{15360\,\pi\, G^2}$$

The accretion rate $\dot{M}_\text{in}(t)$ is set by the BH's environment — sometimes large (a galaxy merger pours gas in), sometimes near zero (the BH has cleared its neighbourhood), sometimes between. The Hawking term is always negative, always present.

From inside Universe 2, the QBP relation gives:

$$H(t) = \frac{\dot{M}}{M} = \frac{\dot{M}_\text{in}(t)}{M(t)} - \frac{C}{M^3(t)}$$

The sign of H depends on which term wins. **Universe 2's expansion is not monotonic** — it tracks the sign of the parent's net mass-change, and that sign flips over cosmic-history timescales.

### Timescales

For an SMBH of M = 10⁹ M_☉:

| Process | Timescale |
|---|---|
| Hawking evaporation t_evap ~ M³/C | ~10⁹⁹ years |
| Galactic-merger accretion bursts | ~10⁹ years |
| Quasar duty cycles | ~10⁷–10⁸ years |
| Hawking flux / accretion flux (today) | ~10⁻⁹⁹ |

For the foreseeable cosmic future (~10¹⁴ years at least), the parent BH lives in the accretion-or-quiescent regime, NEVER the Hawking-dominated regime. The death spiral is a 10⁹⁹-year-from-now concern.

But the quiescent-vs-active cycle is on much shorter timescales — comparable to galactic dynamics. From inside Universe 2, this means cosmic expansion history should show *epochs*: bursts during parent accretion, slower epochs during parent quiescence, and (far in the future) genuine contraction once Hawking dominates.

### What we see from inside

We're currently observing H₀ > 0 and apparent acceleration. In the QBP frame, that means we're in an accretion-active phase of the parent. The **Hubble tension** — different values of H₀ from local (Cepheid) vs early-universe (CMB) probes — naturally reads as different cosmic epochs probing different averages of $\dot{M}_\text{in}$: CMB integrates over the parent's earliest accretion history; local probes integrate over its recent rate. They differ by ~8% because the parent's accretion rate has varied at that level.

DESI 1's hints of w ≠ −1 would then reflect the same thing: the parent's accretion rate isn't a single constant, it's varying, and the variation reads as dynamical "dark energy" to a ΛCDM-trained observer.

This is a strengthening of the QBP Hubble-tension story (already PRED-w-not-minus-1 and the §3.5 discussion in the theory doc): not just "irregular accretion" but a specific prediction that the irregularity has structure — bursts on galactic-merger timescales, with cosmic-history-scale modulation as the parent's environment evolved.

### The deep-future death spiral

Far in the future, once the parent's environment is fully depleted, $\dot{M}_\text{in} \to 0$ permanently. Then:

$$\frac{dM}{dt} = -\frac{C}{M^2}, \qquad M(t) = (M_0^3 - 3Ct)^{1/3}$$

M shrinks slowly at first, then catastrophically. From inside Universe 2:

$$H = -\frac{C}{M^3}, \qquad \dot{H} = -\frac{3C^2}{M^6}$$

Both negative, both growing in magnitude. **Universe 2 contracts at an accelerating rate.** Not a "Big Rip" (which requires Λ > 0 growing) but its inverse: accelerating contraction. The Schwarzschild radius shrinks, and Universe 2's spatial extent shrinks with it.

At the very end, when M approaches Planck mass, the semiclassical Hawking picture breaks down. In QBP terms, **the 𝕆→ℍ crystallisation reverses** — the daughter algebra ℍ dissolves back into the parent 𝕆 structure as the boundary degrees of freedom collapse. Information transferred to the outgoing Hawking radiation. Universe 2 ends, its content encoded in Universe 1's outgoing flux.

Complete cycle: crystallisation (BH formation in Universe 1) → daughter universe lives → decrystallisation (BH evaporation) → information returns to Universe 1.

### Five concrete consequences

**1. Sign-changing Λ_eff is a structural prediction.** The current Λ_eff = 2AB derivation assumes pure mixed accretion (both terms positive). Including Hawking, the full H² expansion picks up additional terms whose sign depends on the relative magnitude of accretion vs Hawking. There are epochs where the effective cosmological constant changes sign — Λ_eff > 0 now (acceleration), Λ_eff < 0 in the deep Hawking-dominated future. Discriminator from ΛCDM.

**2. The Hubble tension narrative sharpens.** "Irregular accretion" becomes "structured accretion history with galactic-merger timescale fluctuations on cosmological-scale modulation." Testable: the local-vs-CMB H₀ discrepancy should match the integrated mean-vs-recent accretion rate ratio of a typical SMBH, calculable from observed SMBH duty cycles.

**3. The CCvS comparison gets a candidate refined-Reading-2 resolution.** Reading 2 in its strong form (instantaneous f₄ cancellation by 2AB) failed by 10¹⁰² in T1. A refined version: f₄ = 0 might be a **cycle-averaged condition** rather than instantaneous. CCvS computes the entropy on a static spectral triple. The accretion-phase contribution and the Hawking-phase contribution might cancel exactly when integrated over a full cycle. This requires the CCvS γ(−2) > 0 to have a negative counterpart under the parent-daughter duality. The xi functional equation (CCvS §4: duality between high-energy and low-energy expansion, exchanging even and odd dimension) might *be* the duality between accretion phase (mass in, "high-energy" parent perspective) and Hawking phase (mass out, "low-energy" parent perspective). Not currently formalised; speculative direction worth investigating.

**4. The crystallisation-decrystallisation symmetry connects to OBS-big-crunch.** If Universe 2 has finite lifetime bounded by the parent's Hawking timescale, and the death of Universe 2 is 𝕆→ℍ crystallisation running backwards, then forward crystallisation and reverse decrystallisation are time-reverses of each other. This connects to the existing OBS-big-crunch anchor (currently in CTH, exact content needs checking next session).

**5. CONJ-fu-from-hawking-time-reverse (HIGHEST LEVERAGE).** If forward crystallisation and reverse Hawking decay are time-reverses, then QBP's profile function f(u) — which encodes the crystallisation dynamics — is determined by the same physics that gives Hawking radiation its known temperature and spectrum. The shape of f(u) is not free; it's fixed by the parent BH's evaporation dynamics. This would close W-003's central open problem from an unexpected direction: not "derive f(u) from forward crystallisation dynamics" but "derive f(u) from the Hawking-decay spectrum of the parent algebra 𝕆."

**Why this is interesting:** the Hawking spectrum is well understood — a near-thermal Planckian distribution at T_H = ħc³/(8πGM k_B), with greybody factors from spacetime curvature. Time-reversing it (within the 𝕆 algebra rather than the standard QFT framework) might produce a function with the right structural properties (positive at small u, crossover at u = 2 from Cayley-Dickson doubling, vanishing tail). The crossover at u = 2 in QBP's empirical f(u) is suggestive — Cayley-Dickson doubling is the algebraic operation that makes ℍ from ℂ, and the time-reverse of the BH evaporation IS the daughter-universe-creation process, which IS the ℍ-from-𝕆 crystallisation.

### Proposed CTH additions (NOT YET COMMITTED — for next session)

- **PRED-cyclical-accretion-Hubble-modulation:** the Hubble tension reflects galactic-merger-scale accretion fluctuations in the parent BH, with a specific quantitative prediction comparing local H₀ deviation to SMBH duty-cycle variability. Status: untested (needs the duty-cycle calculation).
- **PRED-sign-changing-Lambda-eff:** Λ_eff changes sign once Hawking dominates accretion. Far-future has contracting universe. Status: untested, mostly unobservable but a structural commitment.
- **CONJ-fu-from-hawking-time-reverse:** Conjecture that f(u) is determined by the time-reverse of parent BH Hawking decay. Status: open conjecture, concrete research direction. If true, closes W-003.

### Next-session work plan

In priority order:
1. **Develop CONJ-fu-from-hawking-time-reverse formally.** Work out what time-reversing the Hawking spectrum in 𝕆-physics actually produces. Compare to QBP's empirical f(u) shape. Check whether the crossover at u = 2 emerges naturally.
2. **Run numerical H(t) simulation for a typical SMBH** (M = 10⁹ M_☉) across cosmic history with realistic accretion variability. Predict the local-vs-CMB H₀ discrepancy from first principles.
3. **Resolve OBS-big-crunch alignment with Hawking-decay framing.** Check current anchor content; update if needed.
4. **Investigate refined-Reading-2 (cycle-averaged f₄ cancellation).** Formalise what the cycle integral has to look like; check whether CCvS functional equation can provide the negative counterpart.

---

## Document Status

This is a working note, not formal theory. Items that harden into derivations or testable predictions get promoted to CTH anchors and QBP-Theory section updates. Items that remain conjectural stay here for handoff continuity.

**Last updated:** 2026-05-11 (Session 13, end-of-session checkpoint)
**Next session:** Continue with CONJ-fu-from-hawking-time-reverse development.
