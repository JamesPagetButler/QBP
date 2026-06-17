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

## 4. The bound, and what a real test needs

- **Loose bound:** published error budgets close to ~10⁻³ with no role-swap-controlled residual → any anomalous *velocity-independent footprint* asymmetry is bounded only to ~**10⁻³** (very loose; far above where a sub-technical signal would live).
- **A clean trapped-ion test would require:** hold the mass ratio fixed (near-equal-mass isotope pairs, or a **role-swap** control) so all known technical asymmetries cancel, benchmark per-role fidelity at **≲10⁻⁴** with full error-budget closure — *and* QBP must predict n distinct from recoil's k²/m. No existing paper does this control.
- **For the boost mechanism:** move to relativistic γ (§2) — not ions.

## 5. Verdict & strategic implication

**Test C (the zero-cost literature review) is complete.** Outcome: a **clean null** that neither validates nor kills QBP, plus three actionable results — (1) **venue mismatch**: trapped ions are blind to the EXP-10 boost mechanism (the (1−1/γ) suppression); (2) the **photon-recoil degeneracy**: QBP's footprint must be specified distinct from k²/m to be distinguishable; (3) a **loose ~10⁻³ bound** + the controlled-experiment design (role-swap / fixed-mass, ≲10⁻⁴).

> **Strategic implication (the recurring theme):** QBP's "most distinctive prediction" is *not* already sitting in the data — and to become a real test it bottlenecks, again, on QBP **specifying the algebraic footprint n quantitatively** (here, distinct from mass/recoil; in #564, the v→constants exponents). The empirical thread and the theory keystone meet at the same requirement: *compute the footprint.* And the boost-form test should be re-homed to a relativistic venue, not trapped ions.

## 6. Honesty flags
- Nature pages (Be/Mg, Ca/Ca, Ca/Sr) were paywalled; all numbers from the matching arXiv full texts (consistent with published abstracts).
- Innsbruck / PTB / ETH dedicated mixed-species *gate-fidelity* numbers NOT located — genuine gaps, not confirmed nulls.

## 7. Sources
Tan et al. arXiv:1508.03392 · Ballance et al. arXiv:1505.04014 · Hughes et al. PRL 125 080504, arXiv:2004.08162 · Bruzewicz et al. npj QI 5 102, arXiv:1905.13122 · Sosnova/Carter/Monroe arXiv:2004.08045 · Yu et al. arXiv:2503.19818 (photon recoil) · Schäfer et al. arXiv:2509.17893 · Löschnauer et al. arXiv:2510.17286.

## 8. Provenance
Test C (workspace STEP P1) literature review, 2026-06-16 sourced scan + the EXP-10 prediction (`archive/QBP-EXP-10-Entanglement-Asymmetry.md`). The venue-mismatch arithmetic and the recoil-degeneracy discriminator are this review's findings. Recorded by @qbp-oppenheimer.
