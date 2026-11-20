# Lean toolcheck — baseline on the current pins

**Run:** `20261120T204403Z` (2026-11-20 20:44–20:45 UTC) · **overall GREEN — 22/22 files as expected**
(18 tool tests pass, 4 must-fail controls caught with the expected message) · 98 theorems axiom-audited.
Machine-readable record: [`results/results-v4.30.0-c5ea003.json`](results/results-v4.30.0-c5ea003.json)
(+ the `.md` table). Re-run: `cd proofs && lean-toolcheck/run.sh`. A later run on the same pins that is much
slower, or uses much more RSS, than this table is a **finding, not a pass** (#823 R6).

## Versions

| | Value | Source |
|---|---|---|
| Toolchain | `leanprover/lean4:v4.30.0` | `proofs/lean-toolchain` |
| Lean binary reported | `Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit d024af099ca4bf2c86f649261ebf59565dc8c622, Release)` | `lake env lean --version` (preflight) |
| Mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` (stable tag `v4.30.0`) | `proofs/lakefile.lean`; `lake-manifest.json` rev identical (preflight lockstep check) |
| Suite commit | this PR's head (`proofs/lean-toolcheck/`) | — |
| Foundations checker | `scripts/check_lean_foundations.py` at `origin/master` `1892146` | run per file with a zero baseline |

## Box conditions

| | Value |
|---|---|
| Wrapper | `boxrun --gpu --mem-mb 8000 --timeout 19800 --wait` — **one lease for the whole suite** (batch mode), thermal guard on, RSS watch 8000 MB; 1 pinned core |
| Queue | started after 30 s in the queue; cool-start gate Tctl ≤ 58 °C |
| Duration | 71 s lease (68.2 s summed Lean wall time) |
| Thermal | Tctl 55.6 °C at start; max 59.1 °C (boxrun record); **0 guard pauses**, guard action `none`; GPU junction 32 °C (unused) |
| Host | AMD FX-8350 (8 cores), 31 991 MB RAM, 12.6 GB available at the end; other seats' jobs queued around this one |
| Oleans | Mathlib `.oleans` borrowed from the main checkout via a symlinked `proofs/.lake/packages` (rev verified = the pin); nothing was built; page cache **warm** (see note 1) |

## Per-file results

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Axiom audit | Detection (must-fail) |
|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 4.64 | 3767 | 1 thm, no axioms | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.18 | 1840 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.11 | 1921 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.06 | 1952 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.53 | 1972 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 2.99 | 1933 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.35 | 2036 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 3.91 | 2817 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.67 | 2163 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 3.76 | 2393 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.37 | 2958 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.31 | 2147 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.13 | 2022 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 3.89 | 2790 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.03 | 2945 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.02 | 1951 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.41 | 1967 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.27 | 774 | 1 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/…` | must-fail | ✅ caught | 0 | 1.12 | 774 | both thms: `[sorryAx]` | Lean warning ``declaration uses `sorry` `` · `sorryAx` on the direct AND the inheriting theorem · checker `RATCHET violated — sorry: 1 > baseline 0` |
| `must-fail/MF02_NativeDecide/…` | must-fail | ✅ caught | 0 | 1.14 | 774 | `[QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1]` | checker `HARD-BAN violated — native_decide: 1 occurrence` · non-standard axiom |
| `must-fail/MF03_VacuousTrue/…` | must-fail | ✅ caught | 0 | 1.12 | 774 | both thms: **no axioms** (clean!) | checker `HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence` + `RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0` |
| `must-fail/MF04_FalseDecide/…` | must-fail | ✅ caught | 1 | 1.15 | 774 | — (file rejected) | ``Tactic `decide` proved that the proposition 2 + 3 = 1 is false`` (l.19) and ``… 1 - 2 = 0 is false`` (l.22, `Int`) |

"std3" = `{propext, Classical.choice, Quot.sound}`. RSS is `/usr/bin/time` `%M` of the `lake env lean` process tree
(the largest process, i.e. `lean`). Files without a Mathlib import (T17, MF01–MF04) sit at the 774 MB Lean-core floor;
Mathlib-importing files at 1.8–3.8 GB, dominated by the import (cf. the 3.35 GiB `Mathlib.Tactic` floor in
`docs/foundations/lean-build-resource-notes.md`).

### Grader negative control (2026-11-20, not committed)

To show a must-fail that *passes* is reported as a failure, the raw results of this run were copied and five misses
planted (checker exit forced to 0 for MF03; Lean exit forced to 0 for MF04; MF02's axiom list replaced by
`[propext]`; MF01's sorry warning deleted; `sorryAx` injected into a T04 theorem). `toolcheck.py evaluate` on the
copy returned **exit 1 with all five flagged** (`foundations checker did not reject`, `Lean ACCEPTED a must-fail
file`, `axiom audit MISSED`, `expected Lean output … not found`, `non-standard axioms ['sorryAx']`).

## Project layer (QBP's own proofs) — from CI, not re-run locally

| | Value |
|---|---|
| Source | `.github/workflows/lean-foundations.yml` job `lake build (zero errors)`, run **41149457423**, job 124382272424, 2026-10-31 (PR #787 head `f019660`) |
| Same tree as today? | **Yes** — `git rev-parse f019660:proofs` = `origin/master:proofs` = `ed876f0b` (no Lean path has changed on master since #787) |
| Result | `Build completed successfully (3611 jobs)`; 0 errors; 0 `sorry` warnings |
| Re-confirmed | on this PR (#824) at `1215b73`: run 44814875737, `lake build (zero errors)` **pass**, 7 m 08 s job (the suite adds no build target) |
| Axiom output in the log | 1 383 `depends on axioms` reports + 4 `does not depend on any axioms`; **0 non-standard axioms** (parsed from the log). Note: the one documented `native_decide` (#582, `Sprint12-Inherited/SedenionHessianTraceSq.lean`) has no `#print axioms` line, so the log cannot show its axiom |
| Timing | job 6 m 47 s: `lake exe cache get` ≈ 1 m 33 s, `lake build` ≈ 5 m 09 s; 99 QBP modules compiled, 918 s summed module time on the runner |
| Slowest modules | `Foundations.Octonion32Count` 92 s · `SedenionOctonionCount` 80 s · `FanoGenesis` 74 s · `OctonionLaws` 62 s · `Breakdown` 61 s · `Sedenion` 53 s · `Alternator` 38 s · `SeamSpectrum` 24 s · `Substrate.RuleFlow` 21 s · `LeftMulDet` 20 s |
| Peak RSS (box, measured earlier) | `Octonion32Count` 4.4–4.6 GiB; `OctonionAutBranching` closure 5.2 GiB; import floor 3.35 GiB — `docs/foundations/lean-build-resource-notes.md` (2026-10-21/29) |
| Warnings | 36 linter warnings (unusedVariables ×21, unnecessarySeqFocus ×6, unusedSimpArgs ×5, dupNamespace ×3); none are errors |

**Why CI and not a local rebuild:** the estimate for a local `lake build` of all QBP targets on this box is
~30–45 min on one pinned core (918 s of 4-vCPU runner time, FX-8350 single-thread ≈ 1.5–2.5× slower) with a
≥ 4.6 GiB peak, holding the shared box lease the whole time in a queue that other seats' jobs (Agda suite, sc2
runs) were using; it would produce no information CI did not already produce on the *identical* `proofs/`
tree and pins. The tool layer needs only the Mathlib `.oleans`, so only the 22 suite files were run locally.
On the #723 bump branch the project layer is CI's job on the new pins (G1) — plus a local peak-RSS re-measure
of the heavy `decide` modules (FEATURES.md top item 2).

## Notes

1. **Cold cache.** The very first T00 run (65 Mathlib modules, cold page cache) took **39.5 s** wall vs 4.6 s warm
   and pushed the box's IO pressure (`/proc/pressure/io` full avg60) past 20 %; boxrun then refused the *next*
   job with `BOX DEGRADED … needs a reboot`. The pressure fell back to ≈ 0 within ~2 min without a reboot. A cold
   run is the realistic case right after a toolchain bump; compare cold-to-cold.
2. **Sorry-warning text changed.** v4.30.0 prints ``declaration uses `sorry` `` (backticks), not
   `declaration uses 'sorry'`; the suite's first draft keyed on the quotes and MF01 caught it. The grader regex is
   now quote-agnostic.
3. **`native_decide`'s axiom is already per-call on v4.30.0** (`…_native.native_decide.ax_1_1`, measured on
   MF02), not `Lean.ofReduceBool`. So the docstring of `Sprint12-Inherited/SedenionHessianTraceSq.lean`
   ("carries `Lean.ofReduceBool` in its axiom set") is very likely stale already on the current pins — *not
   re-run on that theorem here*; it has no `#print axioms` line. v4.35.0 removes `Lean.ofReduceBool` entirely
   (lean4#14953). The suite's check is name-agnostic (⊄ std3), and `scripts/check_anchor_manifest.py` is
   subset-based, so neither goes blind.
4. **The axiom gate is blind to vacuity** (MF03: clean `#print axioms`); only the checker and a statement review
   catch `: True`.

## Change history

| Date | Run | Change |
|---|---|---|
| 2026-11-20 | `20261120T204403Z` | v1 baseline on `v4.30.0` / `c5ea003` (issue #823 W5) |
