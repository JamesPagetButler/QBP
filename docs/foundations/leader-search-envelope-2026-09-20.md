# Leaders as maps from the substrate to our universe — back-of-the-envelope: search space, constraints, data (v0.1, 2026-09-20)

**Status:** analysis note written by qbp-oppenheimer at the beekeeper's direction ("do a little back of the envelope on how big the search space is, what would constrain it, and what experimental data constrains it — make sure you've really searched the CTH"). Every number below is an order-of-magnitude estimate under a stated assumption. **Nothing here is ruled, anchored or encoded.** Inputs: the proved rule-flow theorems (PR #667), tests 1–2 (#635), and an exhaustive scripted pass over the ledger (6.1.0: 226 anchors — 40 with provenance E, 27 `experiment`; every MEAS-/OBS-/PRED-/CONSTRAINT-/REF- record read; keyword search for hydrogen, electron, speed of light, Rydberg, Lamb, g-factor, ℏ, drift).

## 1. The state side collapses to one number

| Step | Dimension | Why |
|---|---|---|
| initial data: imaginary unit sedenions | 14 | the state sphere |
| forgotten by the flow | 6 | dω has rank 8, 6-dim fibres (confirmer, #667 records) |
| crystal manifold | 8 | the endpoints |
| gauge: the direction u | 6 | G₂ acts transitively on unit imaginary octonions; the Hessian spectrum depends on b₀² alone (`hessQuad_eq_transverse`) |
| **what a universe inherits** | **1 (b₀²), possibly a phase** | the only substrate quantity an observer could measure |

Our universe has one value of b₀²; the ledger's 0.146 is the ensemble mean (reproduced by test 1: 0.1461 ± 0.0078; the 5–95 % range is [0.001, 0.53]). The relaxation rate 8(1−b₀²) then ranges over [3.7, 8.0] per rule-time unit for 90 % of universes; median 7.4.

## 2. The map side: a few hundred discrete leaders

| Component | Free content | Size |
|---|---|---|
| clock: rule-time → physical time | linear (τ), logarithmic in scale factor (κ), power law | 3 families, 1–2 parameters |
| constants map: transverse coordinate x → each dimensionless constant | one integer power p per constant (single Hessian rate ⇒ hierarchies are integer multiples) + today's value as normalisation (fitted, not predicted) | p ∈ {1..4} for {α, μ, G, Λ}: ≤ 256 discrete leaders |
| matter map (link 4) | undefined — no substrate→hosted-field map exists | not searchable |

Parameter-free predictive content per leader: **the ratios of fractional drift rates**, R_XY = p_X / p_Y, and a common time-dependence e^{−k p t}. This sharpens the ledger's own `INSIGHT-direct-gamma-fixed-ratio-generic` (fixed ratios are generic to any single-field model) into a QBP-specific structure: the ratios are **ratios of small integers**, because the substrate has exactly one relaxation rate.

## 3. The experimental data the ledger holds (all bounds; no detections)

| Anchor | Datum | Epoch |
|---|---|---|
| REF-clock-drift-bounds | α̇/α = 1.0(1.1)×10⁻¹⁸/yr; μ̇/μ = −8(36)×10⁻¹⁸/yr (Yb⁺, 2021) | today |
| CONSTRAINT-gdot | Ġ/G < (2±7)×10⁻¹³/yr (LLR) | today |
| REF-th229-alpha-sensitivity | Th-229 clock: K_α = 5900(2300) — future lever | — |
| MEAS-mu-quasar | Δμ/μ < 10⁻⁶ (H₂ absorption) | z 2–4 |
| OBS-alpha-dipole (marginal, contested) | spatial dipole Δα/α ~ 10⁻⁶ at 4.1σ | z 1–2 |
| MEAS-jwst-alpha-constraint | Δα/α = (0.2±0.7)×10⁻⁴ | z 2.5–9.5 |
| MEAS-G-cmb | G_cosmo/G_lab = 1 ± 0.018 | z ~ 1100 |
| MEAS-alpha-bbn | Δα/α = 2 ± 51 ppm | z ~ 10⁹ (t ≈ 3 min) |
| MEAS-G-bbn | G_BBN/G₀ = 0.99 (+0.06/−0.05) | z ~ 10⁹ |
| OBS-nist-big-G-2026 | G = 6.67387×10⁻¹¹, 235 ppm below BIPM; ~500 ppm scatter across labs | today, spatial? |
| MEAS-hubble-tension | H₀ local vs CMB, 8–13 % | — |
| MEAS-alpha, MEAS-sin2tw, MEAS-alphas, MEAS-koide | today's values (fitted normalisations, not drift) | today |

**Not in the ledger (gaps, for the beekeeper's list):** hydrogen 1S–2S (4×10⁻¹⁵, repeated over years → drift bound ~10⁻¹⁵/yr); the Rydberg constant (CODATA, 2×10⁻¹²); the electron g−2 (1.3×10⁻¹³, 2023) and the α(g−2) vs α(Rb recoil) 5σ tension of 2020–23 — the one laboratory hint of something not sitting still; electron/proton mass ratio from H₂⁺ is in MEAS-mu-quasar (26 ppt) but only as a lab reference; isotropy of c (modern Michelson–Morley, Δc/c < 10⁻¹⁷). None of these is a drift *detection*; the g−2/recoil tension is the only anomaly. Candidates for REF-/MEAS- anchors; not encoded here.

## 4. The arithmetic

**Linear clock (t_phys = τ·t_rule), constant ∝ x (p = 1), residual r = e^{−kt}, k = 7.4.**

| Bound | E-folds required | Meaning |
|---|---|---|
| clocks today, τ = 1 Gyr | n > 22.6 (r < 1.5×10⁻¹⁰) | ≥ 3.1 rule-units elapsed |
| clocks today, τ = 13.8 Gyr | n > 20 | ≥ 2.7 rule-units |
| quasars, 10 Gyr ago | n > 13.8 | ≥ 1.9 rule-units elapsed **before** z ≈ 2 |
| BBN α, t = 3 min | n > 9.9 | ≥ 1.34 rule-units elapsed in the first three minutes ⇒ **τ < 2.2 min per rule-unit** ⇒ today t_rule ~ 3×10¹⁵ ⇒ residual exactly 0 |
| BBN G, CMB G | n > 3, n > 4 | weaker, same direction |

**Finding F1.** Under a linear clock the substrate transient was over within the first minutes; nothing of it is observable at any epoch we probe. "Today's dynamism is the substrate transient" is dead for a linear clock.

**Logarithmic clock (t_rule = κ ln a), r(z) = r₀(1+z)^{kκ}, r₀ ≤ 10⁻⁹ from clocks.**

| κ | r(z=2) | r(z=1100) | r(BBN) |
|---|---|---|---|
| 0.01 | 1.1×10⁻⁹ | 1.7×10⁻⁹ | 4.6×10⁻⁹ |
| 0.071 (BBN α limit) | 1.9×10⁻⁹ | 5×10⁻⁸ | 5×10⁻⁵ |
| 0.30 | 1.1×10⁻⁸ | 5×10⁻³ | 8×10¹⁰ (excluded) |

**Finding F2.** BBN forces κ < 0.071, and then r(z ≈ 1.5) < 2×10⁻⁹. The Webb dipole amplitude (10⁻⁶) would need r₀ ≈ 7×10⁻⁷, 700× above the clock bound. **If the dipole is real it is not the substrate transient**; it is spatial, and the substrate flow is per-universe with no spatial structure. The ledger's OBS-alpha-dipole notes ("consistent with f₀ still evolving") and MEAS-hubble-tension ("the tension IS the crystallisation signal") are in tension with the proved single-rate flow under any monotone clock; they need a boundary-inhomogeneity mechanism, not relaxation.

**Λ as "the least-converged moment" (DERIV-crystallisation-asymptotic).** ρ_Λ / Λ_cut⁴ = 3.9×10⁻¹¹⁸ (Λ_cut = 5.04×10¹⁷ GeV from PRED-cutoff-scale). A residual r ≤ 10⁻⁹ reproduces that only as r^p with **p ≈ 13**.

**Finding F3.** No small integer power lets a relaxation residual supply the observed Λ. The ledger already carries the consistent alternative — PRED-f4-zero-vacuum-energy (f₄ = 0) with Λ_eff as the accretion cross-term (PRED-lambda-as-cross-term, one fitted input z_t) — so DERIV-crystallisation-asymptotic's Λ clause ("the least-converged moment explains why Λ is puzzling") should be flagged as superseded, not carried. Also its "c, ℏ converge fastest" clause is not an observable: c and ℏ are conversion factors (DERIV-constants), only dimensionless combinations can drift.

**Finding F4 (structural, positive).** The single Hessian rate turns PRED-correlated-alpha-G from "some functional correlation" into a sharp form: ΔG/G ∝ (Δα/α)^{p_G/p_α} with a ratio of small integers, and every drift ratio R_XY = p_X/p_Y. CONJ-vconstants-keystone's R_αμ is then constrained to be rational with small numerator and denominator. Testable only on a detection (the 0/0 caveat stands), but it is a QBP fingerprint the ledger did not yet have.

**Finding F5 (what the data cannot do).** Six bounds and zero detections kill any leader predicting visible drift, and cannot distinguish the survivors: all survivors predict undetectable drift today. Selection needs a detection (Th-229 network, ESPRESSO/ELT α) or a different observable. The matter side (black holes as sources) is reached by no datum until link 4 exists.

## 5. Buckets

| Item | Bucket | Test / kill |
|---|---|---|
| one substrate observable per universe (b₀²) | 2 forced | `hessQuad_eq_transverse` + G₂ transitivity (standard; the transitivity itself is not in Lean) |
| single relaxation rate; drift ratios rational | 3 provable-now | linearisation theorem: every smooth observable's residual ∝ x^p — Lean owed |
| linear clock ⇒ transient over in minutes | 3 (BOTE) | kill: a detected drift of any constant today |
| Webb dipole ≠ transient | 3 (BOTE) | kill: a monotone clock reproducing 10⁻⁶ at z≈1.5 under the BBN + clock bounds (none found) |
| Λ ≠ least-converged moment | 3 (BOTE) → flag on DERIV-crystallisation-asymptotic | kill: a derived normalisation giving p ≤ 4 |
| black holes as matter sources | 3 open | untouched by any datum until link 4 |

*Nothing here is a ruling. The flags on DERIV-crystallisation-asymptotic are candidates for a housekeeping issue, not edits.*
