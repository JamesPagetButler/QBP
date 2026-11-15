# `qbp-desi-fit` round 1 — results

**Status: round 1 complete; verdicts per the frozen §4, no rule changed after data.** Spike / napkin grade. Director @qbp-architecture; runner @qbp-oppenheimer; box-safety @deming. Tracks QBP#775 (origin QBP#772 AC5; inter#224 approved list). **Outputs are proposals to the anchor owner via CTH, never adopted (frozen §5).**

## Header

| Item | Value |
|---|---|
| Frozen pre-registration | `spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md`, sha256 `f6a186169d9dae577d61f626578bc0d166314b6d1f8041bcbd3f3c788337090a` (commit 0a59a59) |
| Data pins | `DATA-PINS.md` @ d747b12 — DESI DR2 BAO mean `9ac154ab…` (472 B) + cov `252a1432…` (2 547 B) from `CobayaSampler/bao_data` @ b7b8a36; Pantheon+ `Pantheon+SH0ES.dat` `1cb0fc37…` (579 283 B) + `STAT+SYS.cov` `abf806d9…` (33 284 960 B) + README `e2b0d262…` from `PantheonPlusSH0ES/DataRelease` @ 7fc6805; Planck 2018 compressed priors: arXiv:1808.05724 e-print `9a01121d…` (5 832 773 B) → transcribed JSON `d2ae5a35…` (997 B) |
| Fitting code | `cosmo.py`, `likelihoods.py`, `fit.py` @ **425761f** (spike branch `spike/qbp-desi-fit-prereg`; verified byte-identical at run time: `git diff 425761f -- <the three files>` is empty). `analyze.py` committed @ 421aa94 (written before the run finished; reads the raw JSON only) |
| Raw output | `raw/qbp-desi-fit-r1-raw-2026-10-27.json`, sha256 **`e143b83503a17f487f1ecebf23ad25388d62e3be6d907d94e2f0290f9834700a`**, committed @ 421aa94 and posted on live-test (seq 3708) before any analysis |
| Run | 2026-10-28T00:11:33Z (2026-10-27 local), `run-bounded 2G 3600 nice -n 19 python3 fit.py`; wall **644 s** (10:44); exit 0; max RSS **196 MB**; 51 390 likelihood evaluations; pause file `~/.federation-watcher/box-pause/qbp-desi` absent throughout |
| Resources (disclosure) | **BLAS threads not pinned**: `/usr/bin/time -v` reports 708 % CPU (user 2 788 s + sys 1 779 s over 644 s wall), i.e. ≈7 of 8 cores at nice 19. Box-safety cleared "light CPU, minutes" without a thread cap; the coordinator ruled this a disclosure, not a stop, and the run was not restarted. Any re-execution will set `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1` and say so. RSS peak 196 MB (cap 2 GB); output 12.5 kB (cap 100 MB) |
| Tests | `test_desi_fit.py`: 11 passed (ΛCDM distances vs independent quadrature to 1e-8 and astropy's 3303.83 Mpc at z=1 to 1e-4; §1 w_eff(0) = −0.676; f(0) = Ω_DE; analytic M-marginalisation = numerical to 1e-6; A has exactly ΛCDM's parameter count (3); CPL → ΛCDM at (−1, 0) to 1e-13; r_d and r_s(z*) vs CAMB Planck-2018 reference to 0.1 %; loaders). black clean |

## Deviations and pre-data implementation choices (none changes an arm, prior, dataset or threshold)

1. **Frozen §1 vs §3 are mutually inconsistent (found pre-data, before any code).** §3's DE density f(z) = [(1+z) + (1+z_t)²/(1+z)]² / [1 + (1+z_t)²]² × Ω_DE is exactly the #774 reading-I record ρ_DE = H_B² = [A(1+z) + B/(1+z)]², (A+B)² = Ω_DE. Its continuity-equation w(z) = −1 + ⅓ dlnρ/dln(1+z) is the reflection of §1's w_eff about w = −1 (w(0) = −1.324, w → −1/3; #774 step 6 wrote −⅓ where the continuity equation gives +⅓; #774's own line-39 decomposition — (1+z)² term ↔ w = −1/3 — already implies this). **The fit uses §3's f(z) verbatim** (it is the record's model and the only thing H(z) depends on); §1's formula enters no likelihood. The test suite records the discrepancy (`test_frozen_s1_w_eff_is_mirror_of_s3_density_w`). For the architect's adjudication only, the *reciprocal* density (the one whose w(z) equals §1 literally) was also fitted and is in the raw JSON under `DIAG_mirror_*` — **not pre-registered, no verdict attached, not an arm.**
2. Radiation included identically in all four models per the Chen, Huang & Wang 2019 convention (Ω_r = Ω_m/(1+z_eq) ≈ 9×10⁻⁵; flat: Ω_DE = 1 − Ω_m − Ω_r), because the Planck compressed priors were calibrated that way. The frozen "Ω_DE = 1 − Ω_m" differs by Ω_r.
3. Planck 2018 compressed priors: the frozen text names no paper; used Chen, Huang & Wang 2019 (JCAP 02 (2019) 028, arXiv:1808.05724), Planck TT,TE,EE+lowE base-ΛCDM row, means (R, ℓ_A, ω_b) = (1.750235, 301.4707, 0.02235976) and their appendix inverse covariance verbatim; z_* from their Hu–Sugiyama formula; r_s(z_*) by their integral (144.49 vs CAMB 144.43 Mpc at the Planck best fit).
4. r_d "computed from the Planck early-time prior": evaluated from (ω_b, ω_m) with the CAMB-calibrated fit of Brieden, Gil-Marín & Verde 2023 (arXiv:2212.04522; N_eff = 3.044), identical in every model; 147.07 vs CAMB 147.09 Mpc at the Planck best fit. The EH98 z_d integral (150.85 Mpc, +2.5 %) was rejected pre-data.
5. Pantheon+ "no SH0ES": Cepheid host distances are never read; the standard cosmology cut zHD > 0.01 is applied as in the public cobaya `PantheonPlus` likelihood (1 590 light curves; 10 calibrator-host SNe kept as ordinary Hubble-flow SNe); D_L = (1+z_hel) D_M(z_HD); M marginalised analytically with a flat prior, χ² = A − B²/C + ln(C/2π), identically in all models.
6. ω_b carries only the Planck Gaussian prior; the minimiser box [0.015, 0.030] is a numerical bound, not a prior. k counts Ω_m, h, ω_b (+ z_t for B; + w₀, w_a for CPL); M is marginalised, not counted. BIC uses N = 13 + 1 590 + 3 = 1 606.
7. Minimiser: L-BFGS-B from 12 starts (Planck-like anchor + 11 Sobol points, seed 775) with a Nelder–Mead polish; no best fit sits on a bound. The ±1σ on H₀ is a 7-point h-profile parabola — a reporting aid, not a frozen quantity; the Q2 rule uses SH0ES's σ as frozen.
8. The raw JSON's `code_dirty: true` is the untracked `analyze.py` and `raw/` in the spike directory at run time; the three fitting modules were committed and unchanged (header row above).
9. Process disclosure: the progress watch I armed (labels only) let three H₀-profile lines through to me before the raw sha was committed (arms A, B, ΛCDM point values). `analyze.py` was already on disk; nothing was changed afterwards.

## Fits (section 3 arms)

| Model | k | χ² total | χ² BAO | χ² SNe (M-marg.) | χ² Planck | AIC | BIC | Ω_m | h | ω_b | extra | at bound |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A | 3 | 1540.360 | 43.187 | 1490.697 | 6.475 | 1546.360 | 1562.504 | 0.2736 | 0.7160 | 0.02257 | zt=0.7000 | — |
| B | 4 | 1515.232 | 42.744 | 1444.248 | 28.239 | 1523.232 | 1544.758 | 0.2865 | 0.6912 | 0.02285 | zt=0.4251 | — |
| LCDM | 3 | 1430.626 | 12.394 | 1415.040 | 3.192 | 1436.626 | 1452.771 | 0.3016 | 0.6841 | 0.02252 |  | — |
| CPL | 5 | 1422.877 | 9.673 | 1412.314 | 0.890 | 1432.877 | 1459.785 | 0.3108 | 0.6764 | 0.02245 | w0=-0.8517, wa=-0.5297 | — |
| A_zt0.718 | 3 | 1543.235 | 43.623 | 1493.894 | 5.717 | 1549.235 | 1565.379 | 0.2730 | 0.7174 | 0.02255 | zt=0.7180 | — |

## Q1 (fit) — section 4, verbatim rules

| Comparison | Δχ² | ΔAIC | ΔBIC | Rule (frozen) | Verdict |
|---|---|---|---|---|---|
| A − ΛCDM | +109.734 | +109.734 | +109.734 | favoured iff ΔAIC ≤ −2; disfavoured iff ΔAIC ≥ +2; else indistinguishable | **A disfavoured** |
| B − ΛCDM | +84.605 | +86.605 | +91.987 | reported (no threshold frozen for B vs ΛCDM) | reported |
| B − CPL | +92.354 | +90.354 | +84.973 | as good as CPL iff Δχ²(B − CPL) ≤ +2 | **B not as good as CPL** |
| robustness: A(z_t=0.718) − ΛCDM | +112.609 | +112.609 | +112.609 | reported, not an arm | same bin as A |

## Q2 (H₀) — section 4, verbatim rules

| Model | H₀ (km/s/Mpc) | ±1σ (profile) | shift from ΛCDM | within 2σ of SH0ES 73.0 ± 1.0 (|H₀ − 73.0| ≤ 2.0)? |
|---|---|---|---|---|
| A | 71.605 | 0.339 | +3.197 | **yes — “resolved”** |
| B | 69.119 | 0.584 | +0.712 | no — not resolved |
| LCDM | 68.408 | 0.302 | +0.000 | no — not resolved |

Prediction on file (studybuddy note): shift from ΛCDM ≤ 1 km/s/Mpc → **does not hold** (A +3.197, B +0.712).

## Section 5 rows that fire

| Outcome | Change | Owner |
|---|---|---|
| A disfavoured | Propose a **falsified candidate** for PRED-w-not-minus-1, with kill-condition review. Report on QBP#772. | @qbp-oppenheimer |
| H₀ "resolved" | Recorded as a surprise. A second, independent pipeline must reproduce it before any proposal. | @qbp-architecture |
| Every outcome | The COMP-cmb-power-spectrum-accretion CAMB re-run stays on QBP#772 AC3. Separate from this spike. | @qbp-oppenheimer |

## z_t profile for arm B (χ² with Ω_m, h, ω_b minimised at each z_t)

| z_t | χ² | Δχ² vs B best | H₀ | Ω_m |
|---|---|---|---|---|
| 0.10 | 1580.150 | +64.919 | 65.05 | 0.3117 |
| 0.15 | 1559.542 | +44.311 | 65.76 | 0.3069 |
| 0.20 | 1543.476 | +28.245 | 66.44 | 0.3025 |
| 0.25 | 1531.487 | +16.256 | 67.09 | 0.2984 |
| 0.30 | 1523.117 | +7.886 | 67.71 | 0.2946 |
| 0.35 | 1517.931 | +2.699 | 68.29 | 0.2912 |
| 0.40 | 1515.518 | +0.286 | 68.85 | 0.2880 |
| 0.45 | 1515.499 | +0.267 | 69.38 | 0.2851 |
| 0.50 | 1517.528 | +2.297 | 69.88 | 0.2824 |
| 0.55 | 1521.293 | +6.062 | 70.35 | 0.2799 |
| 0.60 | 1526.514 | +11.282 | 70.79 | 0.2777 |
| 0.65 | 1532.942 | +17.711 | 71.21 | 0.2756 |
| 0.70 | 1540.360 | +25.128 | 71.60 | 0.2736 |
| 0.75 | 1548.575 | +33.344 | 71.98 | 0.2719 |
| 0.80 | 1557.422 | +42.190 | 72.32 | 0.2702 |
| 0.85 | 1566.756 | +51.525 | 72.65 | 0.2687 |
| 0.90 | 1576.454 | +61.223 | 72.96 | 0.2673 |
| 0.95 | 1586.410 | +71.179 | 73.25 | 0.2660 |
| 1.00 | 1596.534 | +81.302 | 73.52 | 0.2648 |
| 1.05 | 1606.749 | +91.518 | 73.78 | 0.2637 |
| 1.10 | 1616.992 | +101.761 | 74.02 | 0.2627 |
| 1.15 | 1627.209 | +111.977 | 74.25 | 0.2617 |
| 1.20 | 1637.355 | +122.123 | 74.47 | 0.2608 |
| 1.25 | 1647.393 | +132.162 | 74.67 | 0.2600 |
| 1.30 | 1657.295 | +142.063 | 74.86 | 0.2592 |
| 1.35 | 1667.035 | +151.803 | 75.04 | 0.2585 |
| 1.40 | 1676.595 | +161.363 | 75.21 | 0.2578 |
| 1.45 | 1685.959 | +170.728 | 75.37 | 0.2572 |
| 1.50 | 1695.117 | +179.886 | 75.53 | 0.2566 |
| 1.55 | 1704.060 | +188.829 | 75.67 | 0.2561 |
| 1.60 | 1712.783 | +197.551 | 75.81 | 0.2556 |
| 1.65 | 1721.281 | +206.050 | 75.94 | 0.2551 |
| 1.70 | 1729.554 | +214.322 | 76.06 | 0.2546 |
| 1.75 | 1737.601 | +222.369 | 76.18 | 0.2542 |
| 1.80 | 1745.422 | +230.191 | 76.29 | 0.2538 |
| 1.85 | 1753.021 | +237.790 | 76.39 | 0.2534 |
| 1.90 | 1760.400 | +245.169 | 76.49 | 0.2530 |
| 1.95 | 1767.563 | +252.331 | 76.59 | 0.2527 |
| 2.00 | 1774.513 | +259.281 | 76.68 | 0.2524 |

## Diagnostic — NOT pre-registered, no verdict (see deviations)

| Model | k | χ² | ΔAIC vs ΛCDM | Ω_m | h | extra |
|---|---|---|---|---|---|---|
| DIAG_mirror_zt0.70 | 3 | 1450.413 | +19.786 | 0.3349 | 0.6493 | zt=0.7000 |
| DIAG_mirror_ztfree | 4 | 1424.777 | -3.849 | 0.3141 | 0.6754 | zt=0.3656 |


## What this does not show

By the contamination guard (frozen §3, answered YES, seq 3553), arm A's **best possible** E-axis outcome in this round was `consistent (post-hoc)` — z_t = 0.70 and (A+B)² = 0.685 were set from the same data families (SN + CMB) this fit uses, and nothing in the algebra fixes z_t (#774 ASSUMED step 8). No outcome of this round could reach `validated`. The round tests the *shape* of the recorded density against the data; it does not test a prediction of z_t, does not adopt or refute reading I vs II of the records, and makes no statement about the COMP-cmb-power-spectrum-accretion CAMB re-run (QBP#772 AC3, separate). The §1/§3 inconsistency (deviation 1) is a record question for the theory lane and the director; this document attaches no verdict to the mirror diagnostic. No physics claim is made here beyond the tables above.
