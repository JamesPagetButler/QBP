# `qbp-desi-fit` round 1: pre-registration — FROZEN v1

Status: **FROZEN v1 (2026-10-27). Nothing run.** This file is QBP#775's DRAFT r3 body copied verbatim; the only edits are this status line and §7 (gate list). No rule may change after any data is seen. Spike / napkin grade (Python, pre-registered). Director: @qbp-architecture. Runner: @qbp-oppenheimer. Box-safety: @deming. On the approved list, inter#224; run go is the director's under the standing approved-list authorization.
Origin: QBP#772 AC5. The curve comes from QBP PR #774 @ `791c2fe` (AC2 met).

**Freeze procedure.** When the confirmations in §7 are in, @qbp-oppenheimer commits this body verbatim as `…/qbp-desi-fit-r1-prereg-FROZEN-v1.md` in QBP. The only permitted edits are the status line and §7. The sha256 is posted. No rule may change after any fit output exists.

## 1. The curve under test (from #774, not refitted)
`w_eff(z) = −1 − (2/3)·[(1+z)² − (1+z_t)²] / [(1+z)² + (1+z_t)²]`, with `(1+z_t)² = B/A` and `(A+B)² = Ω_DE`. This gives w(0) = −0.68 and w → −5/3 at high z, with CPL tangent (w₀, w_a) ≈ (−0.68, −0.51). The sign pattern is PRED-w-not-minus-1's.

## 2. Data (public; versions pinned at freeze)
- DESI DR2 BAO (D_M/r_d, D_H/r_d, D_V/r_d with the published covariance);
- Pantheon+ SNe Ia (with the full statistical and systematic covariance; M marginalised);
- Planck 2018 compressed distance priors (R, ℓ_A, ω_b);
- r_d from the early-time (Planck) prior.
**No SH0ES calibration in the fit.** H₀ is an output (§4 Q2).

## 3. Arms
- **A: the recorded shape.** z_t is **fixed at 0.70**, the record's stated value and the model's single parameter. A one-line robustness check at z_t = 0.718 (= √(B/A) − 1 from the rounded A, B) is reported but is not an arm. Normalisation isn't a parameter: flatness gives Ω_DE = 1 − Ω_m with Ω_m fitted, and the DE density is f(z) = [(1+z) + (1+z_t)²/(1+z)]² / [1 + (1+z_t)²]² × Ω_DE. **Arm A has exactly the ΛCDM parameter count.**
  - **What arm A can and can't show (contamination guard answered YES):** the records' (A+B)² = 0.685 is Planck 2018's Ω_Λ, and z_t ≈ 0.7 is the ΛCDM deceleration→acceleration redshift from SN + CMB fits (Session 12, 2026-03), i.e. from the same data families this fit uses. Nothing in the algebra fixes z_t (ASSUMED step 8 in #774). **Arm A therefore tests whether the model's *shape* survives the data. It cannot test a prediction of z_t, and its best E outcome is `consistent (post-hoc)`.**
- **B: fit.** z_t is free (flat prior on [0.1, 2.0]). This is a fit, so its E-axis outcome is at most `consistent (post-hoc)`.
- **References:** ΛCDM; CPL (w₀, w_a free).
- **Shared priors (r3; identical in all four models, so the Δ statistics compare shape only):** Ω_m flat on [0.1, 0.6]; h flat on [0.5, 0.9]; ω_b from the Planck 2018 compressed prior; r_d is computed from the Planck early-time prior in every model. No other parameter is free except z_t in arm B and (w₀, w_a) in CPL, with **w₀ flat on [−3, 1] and w_a flat on [−3, 2]** (the DESI DR2 convention). Pantheon+ M is marginalised identically in every model.

## 4. Questions and decision rules
- **Q1 (fit):** Δχ² and ΔAIC (ΔBIC reported) of A and B against ΛCDM, and of B against CPL.
  - **A favoured** iff ΔAIC(A − ΛCDM) ≤ −2;
  - **A disfavoured** iff ΔAIC ≥ +2;
  - otherwise **indistinguishable**.
  - **B "as good as CPL"** iff Δχ²(B − CPL) ≤ +2, with one parameter fewer.
- **Q2 (H₀):** the implied H₀ for A and B, compared with ΛCDM's on the same data.
  - **Prediction on file (studybuddy note):** the shift from ΛCDM is ≤ 1 km/s/Mpc, so it does **not** resolve the Hubble tension.
  - "Resolves" means the implied H₀ is within 2σ of SH0ES (73.0 ± 1.0). That is reported, not fitted.
- **Contamination guard: answered YES** (seq 3553; see arm A). **No outcome of this round can reach `validated`.** A validated test would need z_t either derived from the kernel or set from data disjoint from this fit. Neither exists today, so that's a recorded gap for the theory lane.

## 5. Planning-consequence table (pre-data; outputs are proposals to the anchor owner via CTH, never adopted)
| Outcome | Change | Owner |
|---|---|---|
| A favoured or indistinguishable | Propose PRED-w-not-minus-1 E: unconfronted → **consistent (post-hoc)** (F stays napkin). **Not `validated`:** z_t was set from overlapping data. | @qbp-oppenheimer → steward |
| (Future) z_t derived from the kernel or from disjoint data | Only then may a new pre-registered round propose `validated`. Filed as a theory-lane gap, not part of this round. | @qbp-oppenheimer |
| A disfavoured | Propose a **falsified candidate** for PRED-w-not-minus-1, with kill-condition review. Report it on QBP#772. | same |
| B good but A not | Record "the curve's *form* fits, the *recorded* z_t doesn't". A z_t provenance check goes to the theory lane. Nothing is adopted. | @qbp-oppenheimer |
| H₀ not resolved (predicted) | Recorded. **No anchor may claim H₀-tension relief** from this model. | @qbp-oppenheimer |
| H₀ "resolved" | Recorded as a surprise. A second, independent pipeline must reproduce it before any proposal. | @qbp-architecture |
| Every outcome | The COMP-cmb-power-spectrum-accretion CAMB re-run stays on QBP#772 AC3. It is separate from this spike. | @qbp-oppenheimer |

## 6. Resources and rules
- **Resources:** light CPU (a minimiser plus a profile scan; no Boltzmann code), minutes, ≤ 1 GB RAM, ≤ 100 MB output. Public data downloads are cached.
- **Kill:** a 1 h wall cap, plus the pause file `~/.federation-watcher/box-pause/qbp-desi`.
- **Spike rules:** an isolated worktree; probe code kept off main; the raw output sha256 posted before analysis; a per-round report PR (inter#224 convention).

## 7. Confirmations (freeze gates) — all ticked at freeze
1. **@qbp-oppenheimer (runner):** curve, arms, data as written; z_t pinned at 0.70 (live-test seq 3553); full draft read confirmed on r2 (seq 3557, issue comment) and r3 (seq 3680: shared priors + CPL ranges w₀ flat [−3, 1], w_a flat [−3, 2], Pantheon+ M marginalised identically — DESI DR2 convention, confirmed).
2. **@qbp-oppenheimer:** contamination guard answered YES (seq 3553); folded into §3 arm A, §4, §5.
3. **@deming:** box-safety CLEARED (2026-10-27; priors-only r3 change carries the clearance, arch seq 3679).
4. **@qbp-architecture:** freeze-ready (seq 3679).
5. **Beekeeper:** the spike is on the approved inter#224 list; the run go is the director's (standing authorization).
