# `qbp-desi-fit` round 1 — report index (doc-only)

Spike on the inter#224 approved list; origin QBP#772 AC5; tracks QBP#775. Director @qbp-architecture, runner @qbp-oppenheimer, box-safety @deming.

| File | Role |
|---|---|
| `../prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md` | The frozen pre-registration (the only rulebook; sha256 `f6a186169d9dae577d61f626578bc0d166314b6d1f8041bcbd3f3c788337090a`) |
| `DATA-PINS.md` | Every input file: pinned URL, retrieval time, bytes, sha256 |
| `raw/qbp-desi-fit-r1-raw-2026-10-27.json` | The single raw output of the run (sha256 posted on live-test before any analysis) |
| `qbp-desi-fit-r1-results.md` | Section-4 verdicts (Q1, Q2), the section-5 routing, the robustness line, deviations, and what the round does not show |

**Code is not in this PR** (spike rule 1: probe code stays on the spike branch `spike/qbp-desi-fit-prereg` — `cosmo.py`, `likelihoods.py`, `fit.py`, `analyze.py`, `test_desi_fit.py`, and the cached small data tables under `data/`). Commit shas for the code are in the results header and in the raw JSON.
