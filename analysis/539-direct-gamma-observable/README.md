# #539 — The direct-Γ observable & the locale system

**Status:** TARGET SPEC (theory core + experimental-state scan) · **For:** #539 Strategy A (microphysical channel), the beekeeper's locale insight · **Date:** 2026-06-13
**Lineage:** `docs/foundations/substrate-foundational-concerns-resolution-2026-06-13.md` §5 (direct-Γ survived its adversarial pass); the keystone #559 (crystallisation = order-parameter magnitude, the *radial/physical* direction, #548 angular = gauge).
**Discipline:** predict a **dimensionless** signature and let clocks referee; structural prediction first, specific number when #559's α(Γ)/μ(Γ) dependence is computed.

---

## 1. The goal (beekeeper)

An observable that reads **crystallisation progress Γ directly** — not via clock-time t. If one exists, a **system of Locales** can be calibrated to it: every observer's Locale Λ(Γ) anchored to the *same physically-observed Γ* → the locales mutually agree → a shared, physically-grounded reference frame **reliable within this universe** (not an arbitrary coordinate choice).

## 2. Where Γ lives, after #559/#548

- **#548:** *which* quaternionic subalgebra the universe crystallised into is **pure gauge** (one G₂ orbit) — the *angular* direction is redundancy.
- **#559 (corrected):** the *radial* direction — the **magnitude of the crystallisation order parameter** (the (2,2) VEV) — is **physical**, and the algebra supplies a sign-indefinite potential that can drive it.
- **∴ Γ is the radial/physical progress** of crystallisation: how far the order parameter has moved, *not* which gauge-equivalent vacuum it sits in. A direct-Γ observable must read the **magnitude**, which is gauge-invariant.

## 3. The signature — single-parameter drift, FIXED RATIO (the dimensionless prediction)

The dimensionless constants depend on where the order parameter sits: **α = α(Γ), μ = μ(Γ)** (and the other SM dimensionless residues). Then by the chain rule, *if a single Γ drives them all*:

$$\frac{\dot\alpha}{\alpha} = \Big(\frac{d\ln\alpha}{d\Gamma}\Big)\dot\Gamma,\qquad \frac{\dot\mu}{\mu} = \Big(\frac{d\ln\mu}{d\Gamma}\Big)\dot\Gamma \;\;\Longrightarrow\;\; \boxed{\;\frac{\dot\alpha/\alpha}{\dot\mu/\mu} = \frac{d\ln\alpha/d\Gamma}{d\ln\mu/d\Gamma} = R_{\alpha\mu}\;\;(\text{a fixed, dimensionless number})\;}$$

**Honest scope (after adversarial pass — §3a):** the fixed-ratio is **NOT a QBP-specific signature.** It is the generic consequence of *any* single-field model (the chain rule). What it buys QBP is a *channel*, not a fingerprint. The Locale is calibrable in principle — read (α, μ, …), invert to Γ — but only QBP's *derived value* of R makes the calibration QBP's rather than a generic scalar's.

### 3a. Adversarial verdict (Gemini Furey/Feynman) — OVERCLAIMED; the value of R is the only fingerprint
The fixed-ratio claim was run through the adversarial gate and came back **(b) legitimate but overclaimed**, bordering on vacuous. The corrections, adopted:
- **Not unique.** A fixed drift-ratio follows from *every* single-parameter model — Bekenstein varying-α, string dilaton, quintessence, any rolling scalar. Presenting it as "the QBP signature" is overclaiming the chain rule. It is **necessary, not sufficient.**
- **0/0 caveat.** Current drifts are consistent with **zero** (α̇/α ≲ 10⁻¹⁸/yr). You cannot measure a ratio of two zeros — the test only switches on once a **non-zero** drift is detected. Until then it is practically dormant.
- **What is genuinely QBP's** (the only fingerprints): **(1) the numerical value of R_αμ** (and R_α,QCD) — *if* the QBP algebra locks it to a specific parameter-free number, and that number is measured, that is a real test; **(2) the time-morphology** — monotone-in-Γ / accretion-correlated, which distinguishes QBP from oscillatory ultralight-DM (but **not** from a slow-rolling quintessence field).
- **Bursty-Γ:** the Γ̇-cancellation in the ratio is correct (trivially valid) — bursty accretion doesn't spoil the *instantaneous* ratio.

> **The verdict's mandate — "derive or die":** without the algebra-derived value of R_αμ, QBP has *a generic scalar-field setup waiting for data to fit*, not a test. **This is the same keystone as #559** (how the dimensionless constants depend on the (2,2)-VEV magnitude). The two threads converge — see §5.

### Discriminator table (corrected — morphology only; value is the real fingerprint)
| Model | Drift structure | Distinguishable from QBP by… |
|---|---|---|
| **QBP crystallisation** | single-parameter; ratio = a *specific derived* R; monotone-in-Γ, accretion-correlated | — |
| Generic single field (Bekenstein/dilaton/quintessence) | single-parameter; ratio fixed but **free/tunable** | **only the derived value of R** (morphology can coincide with quintessence) |
| Ultralight-DM oscillation | constants **oscillate in t** at the DM Compton frequency | time-morphology (ramp vs sinusoid) |
| Independent multi-field | α, μ drift independently → ratio varies in time | ratio-constancy test |

## 4. The experimental handle (state of the art — 2026-06-13 sourced scan)

**The handle is live and rapidly maturing.** Summary of the sourced state:

| Element | State (2024–2026) | Source |
|---|---|---|
| **Th-229 nuclear clock** | Real since **2024** — VUV-comb excitation of the 8.4 eV isomer, freq. measured to ~kHz (×10⁵ improvement) | Zhang…Ye, *Nature* 633, 63 (2024); Tiedau/Schumm, *PRL* 132, 182501 (2024) |
| **α-sensitivity (the lever)** | Measured **K_α = 5900 ± 2300** — ~**10³×** electronic clocks (use the *measured* value, not the older ~10⁴ theory) | Beeks…Ye, Safronova, arXiv:2407.17300 (2024) |
| **+ a unique Λ_QCD lever** | the isomer is a near-cancellation of strong + EM → huge K_QCD too → the **third axis** (strong-force scale) | Fadeev/Berengut/Flambaum, *PRA* 102, 052833 (2020); arXiv:2508.07266 (2025) |
| **Current drift bounds** | (α̇/α) = **1.0(1.1)×10⁻¹⁸/yr**; (μ̇/μ) = **−8(36)×10⁻¹⁸/yr** — both consistent with 0 | Lange…Peik, *PRL* 126, 011102 (2021) |
| **Structured-drift method** | mature (clock-network DM searches: oscillatory + transient) — **all NULL**, no confirmed non-zero | Kennedy…Ye, *PRL* 125, 201302 (2020); Roberts…Derevianko GPS.DM, *Nat.Comm.* 8, 1195 (2017); QSNET, *EPJQT* 9, 12 (2022) |
| **Multi-clock K-framework** | sensitivity coefficients K_α/K_μ/K_QCD differ per transition → solve simultaneously for δα, δμ, δΛ_QCD | Safronova…, *RMP* 90, 025008 (2018); Berengut, arXiv:1807.08337 |
| **High-z (the Γ-axis)** | quasar α/μ, CMB, BBN all **consistent with zero**; the Webb α-dipole is contested + superseded by null distortion-corrected data | Kotuš/Murphy/Carswell, *MNRAS* 464, 3679 (2017); Planck XXIV (2015) |

**Why this realises the locale idea:** the Th-229 nuclear clock (huge K_α *and* K_QCD) read against an optical electronic clock (Sr/Yb⁺, different K_α) and a microwave clock (Cs, carries K_μ) is a **three-transition network with linearly-independent sensitivity vectors** → it measures δα, δμ, δΛ_QCD *separately* → it directly tests the **fixed-ratio** signature of §3. This is the concrete instrument for the beekeeper's "two (now three) independent processes drifting together."

**Independent convergence (worth noting):** the experimental-methodology literature, asked what would distinguish a real new-physics drift, names exactly the §3 signature — *"a predicted constant ratio K_α : K_μ : K_QCD specified in advance,"* plus a non-oscillatory, accretion-correlated time-morphology. QBP's fixed-ratio prediction and the field's discriminator are the **same object**, reached from opposite directions.

**Honesty flags (carry into any write-up):** (i) use the *measured* K_α = 5900(2300), not the older ~10⁴ theory value; (ii) three sources (Fuchs Th-229-DM *PRX* 2025; King 2012 dipole; Whitmore–Murphy 2015 systematics) were confirmed only at press/abstract level in the scan — full-text verify before citing in a publication.

## 5. The convergence — both threads reduce to ONE computation

The adversarial passes on **#559** ("which potential does crystallisation select → what spectrum") and on **#539** ("what is the value of R_αμ") land on the **same keystone**:

> **THE KEYSTONE (shared #559 + #539):** derive the dependence of the dimensionless constants on the crystallisation order-parameter magnitude — **α(v), μ(v), Λ_QCD(v)**, where v = |the (2,2) VEV|. From it: R_αμ = (d ln α/dv)/(d ln μ/dv) is a *parameter-free number*, and the #559 spectrum follows from the same v-dependence.

This is the genuine, well-posed next move for the whole crystallisation program — not a new thread, but the *single* computation both adversaries demanded. It needs the #559 continuation (the selected sign-indefinite potential → v) plus a map from v to the SM dimensionless residues.

## 6. Status / honest summary
- **What's real:** a live, maturing **instrument** (the Th-229 nuclear-clock network, §4) that *can* measure a fixed-ratio across α/μ/Λ_QCD to ~10⁻¹⁸–10⁻¹⁹/yr.
- **What's NOT a QBP result:** the fixed-ratio signature itself — it is generic single-field calculus (§3a), and it is dormant until a non-zero drift is detected (0/0).
- **What QBP must do to have a test:** derive the **value** of R_αμ from the algebra (the §5 keystone). Without it there is no QBP-specific prediction here — only a generic scalar-field channel.
- **Locale payoff:** the locale system is calibratable *if* a direct-Γ observable is confirmed *and* R is QBP-derived; otherwise the "Γ-reading" is indistinguishable from a generic rolling scalar.

## 7. Provenance
Beekeeper's locale insight (#539, 2026-06-13) + the #548/#559 gauge-vs-physical (angular/radial) resolution. The fixed-ratio is the chain-rule consequence of "all dimensionless residues are functions of one Γ" — and the adversarial gate (Gemini Furey/Feynman) correctly deflated it from "QBP signature" to "generic single-field channel; the *value* of R is the only fingerprint." Experimental state from the 2026-06-13 sourced literature scan (Th-229 nuclear clock + clock-network drift bounds). Recorded by @qbp-oppenheimer.
