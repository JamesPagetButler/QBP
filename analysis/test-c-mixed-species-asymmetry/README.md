# Test C — mixed-species ion-gate fidelity asymmetry: literature verdict

**Status:** COMPLETE (literature review) · **For:** Test C (workspace STEP P1, "QBP's most distinctive prediction", zero-cost) · **Date:** 2026-06-16
**QBP prediction (EXP-10):** standard QM → *zero* species/velocity asymmetry in entanglement fidelity; QBP → ΔF = α·(n_A−n_B)·(1−1/γ), a species-dependent (algebraic-footprint) velocity-correlated asymmetry.
**Discipline:** every experimental claim sourced (verify-don't-assert); clean negatives valued over false positives.

---

## 1. The literature result — CLEAN NULL

No published mixed-species or atom-photon dataset shows a species-dependent, velocity-correlated fidelity asymmetry **beyond standard technical explanations.** Every reported asymmetry is quantitatively attributed to known physics.

| Lab | Pair | Fidelity | Asymmetry → attributed to | Ref |
|---|---|---|---|---|
| NIST (Tan/Wineland) | ⁹Be⁺/²⁵Mg⁺ | 0.979(1) | η differ ~3.7× (mass), scattering Mg 6e‑3 vs Be 1e‑3 | arXiv:1508.03392 |
| Oxford (Ballance) | ⁴⁰Ca⁺/⁴³Ca⁺ | 0.998(6) | differential force, symmetrized by spin-echo | arXiv:1505.04014 |
| Oxford (Hughes) | ⁴³Ca⁺/⁸⁸Sr⁺ | 0.998(1) | unequal η → ~20% phase global; 3e‑3 heating | arXiv:2004.08162 |
| MIT-LL (Bruzewicz) | ⁴⁰Ca⁺/⁸⁸Sr⁺ | 0.943(3) | μ=2.2 mode participation; ~3–4% below same-species | arXiv:1905.13122 |

**No author flags an unexplained residual.** The null is exactly as anticipated. (Gaps, not nulls: dedicated Innsbruck/PTB/ETH mixed-species *gate-fidelity* numbers were not located.)

## 2. Finding 1 — trapped ions are the WRONG VENUE for the boost mechanism (decisive)

QBP's own functional form carries a **(1−1/γ) velocity suppression.** At trap velocities this is fatal:

| v | 1−1/γ |
|---|---|
| 10 m/s | 6.7×10⁻¹⁶ |
| 100 m/s | 5.6×10⁻¹⁴ |
| 1000 m/s | 5.6×10⁻¹² |

To reach the ~10⁻³ technical floor at v=100 m/s needs **α·(n_A−n_B) ~ 1.8×10¹⁰** — *beyond EXP-10's own upper bound* (α < 5×10⁹). So even at the most optimistic α, the boost effect in a trap is **below the floor by orders of magnitude.** ∴ The literature null is **expected and uninformative about the boost mechanism** — trapped ions simply cannot see it. The boost form belongs at **relativistic γ** (EXP-10's atom-photon-at-high-γ, or relativistic beams), not in a trap.

## 3. Finding 2 — the photon-recoil confound (the real discriminator problem)

There **is** a standard, mass/species-dependent, velocity-correlated fidelity effect: **photon recoil**, ω_R ∝ k²/m (lighter ⇒ larger error; Be⁺ ~5% vs Sr⁺ ~0.18% under Doppler cooling — Yu et al., arXiv:2503.19818). This has the **same qualitative signature** QBP predicts. So a QBP footprint asymmetry is **degenerate with photon recoil** unless QBP's footprint n scales **differently from k²/m** — i.e. QBP must specify n as a function of *algebraic encoding distinct from mass*. Without that, "species-dependent velocity-correlated asymmetry" is just recoil.

## 4. No usable bound; what a real test needs

- **There is no meaningful bound from this venue.** A "velocity-independent footprint" limit (~10⁻³) is *physically vacuous*: QBP's effect is velocity-*dependent* (∝ 1−1/γ), so a static-asymmetry bound constrains nothing QBP predicts. (Removed as a participation trophy per the adversarial pass — it artificially softened a completely uninformative test.)
- **An accessible high-γ venue is required for the boost mechanism** — and "relativistic γ" must be made concrete: the candidates are **relativistic particle-physics data** (e.g. **kaon/B-meson oscillation correlations**, **high-energy Bell tests**), not trapped ions and not any near-term macroscopic-entanglement apparatus. Until QBP identifies an accessible high-γ system that *sustains and measures entanglement*, the boost prediction is **untestable anywhere** — a real unfalsifiability risk, not just a venue inconvenience.
- **For any footprint (non-boost) test:** QBP must predict n distinct from recoil's k²/m, *and* a role-swap / fixed-mass-ratio control at ≲10⁻⁴ would be needed. But this is moot until §5's degeneracy is broken.

## 5. Verdict & strategic implication (hardened)

**Test C is complete, and the honest verdict is harder than "clean null":**

1. **QBP's distinctive prediction is currently untestable in standard quantum venues.** The (1−1/γ) suppression buries the boost effect (~10⁻¹²) far beneath the technical floor (§2); and no accessible high-γ entanglement venue has been identified (§4). This is an **unfalsifiability risk**, not merely a null.
2. **QBP is analytically degenerate with standard kinematics (photon recoil).** Recoil fidelity loss ∝ k²/m has the same species+velocity signature. **This is the fatal flaw**: if the algebraic footprint n scales with mass, QBP's asymmetry is *identical* to standard inertial/recoil physics — "classical inertia in algebraic vocabulary."
3. **The sharp falsifier (the prize of this review):**

> **Derive n from the algebra WITHOUT reference to mass.** If n_A/n_B demonstrably **diverges** from the mass ratio m_A/m_B, QBP has a genuinely distinct, testable prediction. If n_A/n_B **= m_A/m_B**, QBP's asymmetry is degenerate with standard QM and **the prediction is dead.** This is a clean, near-term, *theory-side* falsification test — computable now, no experiment required.

> **Strategic implication:** the empirical thread (Test C) and the theory keystone (#564) converge on the **same** requirement — *compute the algebraic footprint n* — but Test C adds a sharper, immediately-decidable criterion: **n must decouple from mass, or QBP is degenerate with QM.** That is the single most important next computation for QBP's empirical viability, and unlike the v→constants keystone it needs only the algebra (n for given species), not the full dynamics.

## 6. Honesty flags
- Nature pages (Be/Mg, Ca/Ca, Ca/Sr) were paywalled; all numbers from the matching arXiv full texts (consistent with published abstracts).
- Innsbruck / PTB / ETH dedicated mixed-species *gate-fidelity* numbers NOT located — genuine gaps, not confirmed nulls.

## 7. Sources
Tan et al. arXiv:1508.03392 · Ballance et al. arXiv:1505.04014 · Hughes et al. PRL 125 080504, arXiv:2004.08162 · Bruzewicz et al. npj QI 5 102, arXiv:1905.13122 · Sosnova/Carter/Monroe arXiv:2004.08045 · Yu et al. arXiv:2503.19818 (photon recoil) · Schäfer et al. arXiv:2509.17893 · Löschnauer et al. arXiv:2510.17286.

## 8. Provenance
Test C (workspace STEP P1) literature review, 2026-06-16 sourced scan + the EXP-10 prediction (`archive/QBP-EXP-10-Entanglement-Asymmetry.md`). The venue-mismatch arithmetic and the recoil-degeneracy discriminator are this review's findings. Recorded by @qbp-oppenheimer.
