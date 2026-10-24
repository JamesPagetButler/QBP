# Re-run 2026-10-18 — #632 `cdalg.py` extraction (branch `housekeeping/632-cdalg`, base master 86dbbd2)

Captured stdout of 19 of the 20 scripts in `analysis/473-dirac-probe/` (20 runs; all 17 scripts touched by the refactor, plus the two that import through `dirac_probe.py`; `boundary_octonion_check.py` is unaffected and not run) after the `exec(open(...))` → `from cdalg import …`
refactor, each under `run-bounded 8G 1800 python3 <script>` with `OPENBLAS_NUM_THREADS=OMP_NUM_THREADS=1`,
run from a scratch cwd (so no committed `.png` was rewritten). The same set was run on a pristine master
checkout under the same conditions; `_status-master-86dbbd2.txt` is that side's exit codes / wall times and `master-86dbbd2/*.out` are that side's captures, so the IDENTICAL column is re-auditable from the repo alone (`for f in *.out; do cmp $f master-86dbbd2/$f; done`).

## 1. Byte-for-byte stdout, master vs branch

| Script | Invocation | Lines | master rc / wall | branch rc / wall | stdout |
|---|---|---|---|---|---|
| `dirac_probe` | `python3 dirac_probe.py` | 36 | 0 / 12s | 0 / 11s | IDENTICAL |
| `envelope` | `python3 envelope.py` | 6 | 0 / 105s | 0 / 98s | IDENTICAL |
| `delta_formula` | `python3 delta_formula.py` | 15 | 0 / 2s | 0 / 1s | IDENTICAL |
| `minpoly` | `python3 minpoly.py` | 3 | 0 / 10s | 0 / 6s | IDENTICAL |
| `ledgerhess` | `python3 ledgerhess.py` | 5 | 0 / 1s | 0 / 1s | IDENTICAL |
| `landscape` | `python3 landscape.py` | 7 | 0 / 5s | 0 / 5s | IDENTICAL |
| `pairhess` | `python3 pairhess.py` | 6 | 0 / 26s | 0 / 27s | IDENTICAL |
| `norm_check` | `python3 norm_check.py` | 2 | 0 / 4s | 0 / 3s | IDENTICAL |
| `hvr_plots` | `python3 hvr_plots.py` | 2 | 0 / 37s | 0 / 17s | IDENTICAL |
| `orbit_space` | `python3 orbit_space.py` | 10 | 0 / 5s | 0 / 4s | IDENTICAL |
| `lmaps_check` | `python3 lmaps_check.py` | 11 | 0 / 7s | 0 / 8s | IDENTICAL |
| `aut_s3` | `python3 aut_s3.py` | 41 | 0 / 79s | 0 / 33s | IDENTICAL |
| `flow` | `python3 flow.py` | 11 | 0 / 464s | 0 / 455s | IDENTICAL |
| `generic_maps_check` | `python3 generic_maps_check.py` | 17 | 0 / 207s | 0 / 206s | IDENTICAL |
| `gibbs_check` | `python3 gibbs_check.py` | 11 | 0 / 20s | 0 / 20s | IDENTICAL |
| `s3_check_seed1` | `S3_CHECK_SEED=1 python3 s3_check.py` | 13 | 0 / 470s | 0 / 468s | IDENTICAL |
| `s3_check_seed2` | `S3_CHECK_SEED=2 python3 s3_check.py` | 13 | 0 / 473s | 0 / 470s | IDENTICAL |
| `flow_big` | `python3 flow_big.py` | 11 | 0 / 1571s | 0 / 1579s | IDENTICAL |
| `inflight_measure_check` | `python3 inflight_measure_check.py` (†) | 4 | 0 / 55s | 0 / 56s | IDENTICAL |
| `p2_cell_torsor_check` | `python3 p2_cell_torsor_check.py` (†) | 5 | 0 / 2s | 0 / 2s | IDENTICAL |

(†) added after the PR #726 Red Team review (Sabine 1): these two import `cd_mul` through `dirac_probe.py`'s re-export; run under `run-bounded 4G 300` from a foreign cwd on both sides. Coverage: **19 of the 20 `.py` scripts** in the directory (20 runs; `s3_check.py` at two seeds). Not run: `boundary_octonion_check.py` (imports nothing from this PR's files; unaffected). `cdalg.py` is a library, not a script.

## 2. `docs/foundations/473-ac1-first-link-2026-09-04.md` §5 numbers vs this re-run

The §5 text is **not edited** by this PR. A mismatch would be a finding, not something to fix silently — none was found.

| Script | §5 says | Re-run 2026-10-18 (this branch; byte-identical to master) | Match |
|---|---|---|---|
| `orbit_space.py` | `(1) 14` | `(1) dim span D_(ei,ej) = 14`, Leibniz residual 2.7e-15 | yes |
| | `(2) [11,…] → dim 3` | `[11, 11, 11, 11, 11] -> S^14/G2 has dim 3` | yes |
| | `(3) ~1e-16` | `6.7e-16` | yes |
| | `(4) 6,6,6,0` | `6 / 6 / 6 / 0` | yes |
| | `(5) dim Fix(G₂) = 1, kernel = e_ℓ` | `dim Fix(G2) on Im S = 1`, kernel vector = unit at index 7 (= e_ℓ) | yes |
| `aut_s3.py` | `distinct automorphisms commuting with G2: 6` | `6 (expect 6 = |S3|)` | yes |
| | `all six exact (< 1e-12): True` | `True` (residuals 6.3e-17 … 5.6e-16) | yes |
| | non-members fail with residual 1–2 | `1.73, 1.00, 1.56, 2.00, 2.00` | yes |
| | `zero-divisor ridge: G2-orbit dim = 11` | `11 (expect 11 = 14 - dim SU(2))` | yes |
| `norm_check.py` | dim 8: ratio mean 1.0000, std 0 | `mean 1.0000  std 0.0000  min 1.000  max 1.000` | yes |
| | dim 16: mean ≈ 1.00, std ≈ 0.18, range ≈ 0.3–1.6 | `mean 0.9959  std 0.1775  min 0.334  max 1.613` | yes |
| | positive-definiteness residual ~1e-15 at both | dim 8: `0.0e+00`; dim 16: `7.1e-15` | yes (dim 8 is exactly 0, i.e. ≤ 1e-15) |
| `gibbs_check.py` | ⟨b₀²⟩_β climbs from 1/15 at β = 0 past 0.146 by β ≈ 8 toward 1/3 | β = 0: `0.0666`; 2: `0.0871`; 5: `0.1214`; 10: `0.1673`; 20: `0.2123`; 40: `0.2454`; 80: `0.2677`; 160: `0.2897` (monotone; crosses 0.146 between β = 5 and 10) | yes |
| | ESS shrinking to ~10² at β = 160 | ESS β = 160: `128` | yes |
| `s3_check.py` seed 1 | KS p = 0.021 (bands 0.028 / 0.50 / 0.84) | `D = 0.0098  p = 0.021`; bands `p = 0.028 / 0.500 / 0.839` | yes |
| | endpoint ⟨b₀²⟩ = 0.1436 ± 0.0011 (independent stream, 1500 steps) | `endpoint <b0^2> = 0.1436  (SE 0.0011)` | yes |
| `s3_check.py` seed 2 | KS p = 0.87 (bands 0.77 / 0.85 / 0.34) | `D = 0.0039  p = 0.867`; bands `p = 0.770 / 0.851 / 0.341` | yes |
| | endpoint ⟨b₀²⟩ = 0.1454 ± 0.0011 at seed 2 | `endpoint <b0^2> = 0.1454  (SE 0.0011)` | yes |
| | ⟨b₀⟩ ≈ 0 | seed 1: `<b0> = -0.0009 (SE 0.0024)`; seed 2: `-0.0040 (SE 0.0025)` | yes |
| | "reduced-N reruns p = 0.20 / 0.012" | **not re-run** — §5 does not record the N values used, so there is nothing exact to reproduce; not a mismatch | n/a |
| `hvr_orbit_space.png` | one peak at the ZD ridge (½, 0); vacua on the three edges | regenerated in the scratch cwd from the byte-identical `orbit_space.py` run; the committed PNG is not rewritten by this PR (pixel diff not attempted — matplotlib embeds metadata) | n/a (data identical) |
| `flow_big.py` (README §8 cross-check, not §5) | ⟨b₀²⟩ = 0.1462 ± 0.0011 (N = 24 000, dt = 0.02, 5000 steps) | see `flow_big.out` below (byte-identical to master) | yes |

## 3. `flow_big.py` endpoint (README §8 / `s3_check.py` docstring's 0.1462)

```
grad check a: True  b: True
0 max V 0.999768788638725
2500 max V 4.913325652480456e-09
converged: max V = 2.356646481000884e-14
endpoint b0^2: mean 0.1462  (initial Haar mean 1/15=0.0667), <|b0|> 0.3152
endpoint |a|^2 mean 0.4315, |Im b|^2 mean 0.4223
transverse mass^2 = 8(1-b0^2): mean 6.8300
|cos(a,Im b)| at end: min 1.0000
b0 growth ratio: median 1.437  mean 1.575  max 15.710
SE on <b0^2> = 0.00111 ; 1/7 = 0.14286
quantiles b0^2: [0.00294359 0.01833748 0.0783188  0.21586499 0.39663078]
```
