# Lean toolcheck — baseline on the current pins

**Run:** `20261120T212158Z` (2026-11-20 21:24–21:26 UTC, `tools/lean-toolcheck/run.sh --update-baseline`) ·
**overall GREEN — 26/26 files as expected**: 19 tool tests pass, 5 must-fail controls caught with the expected
message, 2 known-limit probes confirmed (report-only) · 105 theorems axiom-audited.
Machine-readable record: [`results/results-v4.30.0-c5ea003.json`](results/results-v4.30.0-c5ea003.json)
(+ the `.md` table). Re-run: `tools/lean-toolcheck/run.sh` — this writes only to `results/runs/<run-id>/`
(gitignored); the committed record changes only with `--update-baseline` on a full GREEN run. A later run on the
same pins that is much slower, or uses much more RSS, than this table is a **finding, not a pass** (#823 R6).

> **Limit: the vacuity check is SYNTACTIC ONLY.** The foundations checker catches the literal `: True :=` (MF03);
> `x = x → True` and `(fun _ => True) 3` pass both the checker and the axiom audit (KL01, report-only). A user
> `axiom` is caught by the axiom audit alone; the checker accepts it (MF05).

## Versions

| | Value | Source |
|---|---|---|
| Toolchain | `leanprover/lean4:v4.30.0` | `proofs/lean-toolchain` |
| Lean binary reported | `Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit d024af099ca4bf2c86f649261ebf59565dc8c622, Release)` | `lake env lean --version`, the `Lean (version` line (preflight; not line 1 — see note 5) |
| Mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` (stable tag `v4.30.0`) | `proofs/lakefile.lean`; `lake-manifest.json` rev identical (re-read after `lake env`) |
| Suite | `tools/lean-toolcheck/` at this PR's head (moved from `proofs/`, PR #824 option (b)) | — |
| Foundations checker | `scripts/check_lean_foundations.py` at `origin/master` `1892146` | run per file with a zero baseline |

## Box conditions

| | Value |
|---|---|
| Wrapper | `boxrun --gpu --mem-mb 8000 --timeout 23400 --wait` — **one lease for the whole suite**, thermal guard on, RSS watch 8000 MB; 1 pinned core |
| Queue | started after 2 m 41 s in the queue (cool-start gate Tctl ≤ 58 °C; an Agda suite and another seat's job queued behind) |
| Duration | 81 s lease (77.2 s summed Lean wall time) |
| Thermal | Tctl 58.1 °C at start; max 61.1 °C (boxrun record); **0 guard pauses**, guard action `none` |
| Host | AMD FX-8350 (8 cores), 31 991 MB RAM, 12.6 GB available at the end |
| Oleans | Mathlib `.oleans` borrowed from the main checkout via a symlinked `proofs/.lake/packages` (rev verified = the pin); nothing was built; page cache warm |

## Per-file results

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Axiom audit | Detection |
|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 5.04 | 3761 | 1 thm, no axioms | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.44 | 1827 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.35 | 1904 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.30 | 1935 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.78 | 1948 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.14 | 1918 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.56 | 2015 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.22 | 2807 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.90 | 2147 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 4.02 | 2376 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.56 | 2950 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.61 | 2125 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.26 | 2008 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 4.11 | 2780 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.42 | 2936 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.25 | 1940 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.72 | 1947 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.27 | 774 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.19 | 774 | 3 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/…` | must-fail | ✅ caught | 0 | 1.15 | 774 | `['sorryAx']` | Lean warning ``declaration uses `sorry` `` · `sorryAx` on the direct, the inheriting AND the `admit` theorem · checker `RATCHET violated — sorry: 1 > baseline 0` (the checker does not count `admit`) |
| `must-fail/MF02_NativeDecide/…` | must-fail | ✅ caught | 0 | 1.14 | 774 | `['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']` | checker `HARD-BAN violated — native_decide: 1 occurrence` · non-standard axiom `…_native.native_decide.ax_1_1` |
| `must-fail/MF03_VacuousTrue/…` | must-fail | ✅ caught | 0 | 1.14 | 774 | 2 thm, no axioms | checker `HARD-BAN … : True := by trivial: 1 occurrence` + `RATCHET … vacuous-: True := theorem: 2 > baseline 0` (literal spelling only — see KL01) |
| `must-fail/MF04_FalseDecide/…` | must-fail | ✅ caught | 1 | 1.14 | 774 | — (file rejected) | ``Tactic `decide` proved that the proposition 2 + 3 = 1 is false`` (l.19) and ``… 1 - 2 = 0 is false`` (l.22, `Int`) |
| `must-fail/MF05_CustomAxiom/…` | must-fail | ✅ caught | 0 | 1.13 | 774 | `['QBPToolcheck.MF05.cheat']` | axiom audit only: `#print axioms` = `[QBPToolcheck.MF05.cheat]`; checker ACCEPTS (known limit, confirmed) |
| `known-limits/KL01_VacuityBypass/…` | known-limit | 🟡 known limit | 0 | 1.17 | 774 | 2 thm, no axioms | 🟡 confirmed: checker exit 0; both theorems `does not depend on any axioms` — vacuity check is syntactic |
| `known-limits/KL02_FinFoldlDecide/…` | known-limit | 🟡 known limit | 1 | 1.17 | 774 | — (file rejected) | 🟡 confirmed: elaborator `decide` stuck on `Fin.foldl` ("did not reduce to `isTrue` or `isFalse`") |

"std3" = `{propext, Classical.choice, Quot.sound}`. RSS is `/usr/bin/time` `%M` of the `lake env lean` process tree
(the largest process, i.e. `lean`). Files without a Mathlib import (T17, T18, MF*, KL*) sit at the 774 MB Lean-core
floor; Mathlib-importing files at 1.8–3.8 GB, dominated by the import (cf. the 3.35 GiB `Mathlib.Tactic` floor in
`docs/foundations/lean-build-resource-notes.md`).

### Repeatability and the observed SIGSEGV flake

| Run | Mode | Files | Result | Lease | Crashes (exit ≥ 128) |
|---|---|---|---|---|---|
| `20261120T211819Z` | **fresh-manifest** (`proofs/lake-manifest.json` deleted first — the F1 path) | 26 | GREEN 26/26 | 92 s | 0 |
| `20261120T212023Z` | normal | 26 | GREEN 26/26 | 81 s | 0 |
| `20261120T212158Z` | `--update-baseline` (this record) | 26 | GREEN 26/26 | 81 s | 0 |
| earlier today (`…204151Z`, `…204403Z`, `…210059Z`) | normal, 22-file suite | 22 | GREEN 22/22 each | 71–74 s | 0 |

**Observed flake, not reproduced here.** The Red Team's first independent run on PR #824 (qbp-architecture,
issuecomment-7050748708, 2026-11-20) saw **T05 and T07 exit 139 (SIGSEGV) at 0.68 s, during import**, then pass
alone (3.1 s / 4.1 s) and in a full re-run; that box also logged intermittent `failed to create thread` aborts the
same day. In the six full runs above (T05 and T07 each ran six times, 3.0–4.3 s, 1.9 / 2.8 GB RSS) there was **no
crash**. I have no burst log of the crashing run (it was the reviewer's), so it is recorded as an observed,
unreproduced flake — source: the reviewer's run. The suite does **not** retry: a crash (exit ≥ 128) is graded
FAIL with exit code, wall and RSS in the result row (`toolcheck.py`), so if it recurs the run is red and the row
plus the boxrun burst log (`~/.box-telemetry/bursts/lean-toolcheck-suite-<run-id>-*/`) are the evidence to hand
to deming.

### Grader negative control (2026-11-20, not committed)

To show a must-fail that *passes* is reported as a failure, raw results were copied and five misses planted
(checker exit forced to 0 for MF03; Lean exit forced to 0 for MF04; MF02's axiom list replaced by `[propext]`;
MF01's sorry warning deleted; `sorryAx` injected into a T04 theorem). `toolcheck.py evaluate` on the copy returned
**exit 1 with all five flagged** (`foundations checker did not reject`, `Lean ACCEPTED a must-fail file`, `axiom
audit MISSED`, `expected Lean output … not found`, `non-standard axioms ['sorryAx']`).

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
tree and pins. The tool layer needs only the Mathlib `.oleans`, so only the suite files (26) were run locally.
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
4. **The axiom gate is blind to vacuity, and the checker's vacuity rule is syntactic** (MF03 + KL01): the checker sees
   only the literal `: True :=`; any other vacuous spelling needs a human reading the statement.

5. **Fresh-checkout preflight (Red Team F1).** With `proofs/lake-manifest.json` absent (it is gitignored, so every
   fresh clone), the first `lake env lean --version` prints seven Lake lines first (`info: QBPProofs: no previous
   manifest, creating one from scratch`, `info: mathlib: running post-update hooks`, the cache-tool lines) and the
   `Lean (version …)` line last; `head -1` read the info line as the version. The preflight now greps the
   `Lean (version` line and re-reads the manifest after `lake env` recreates it. Verified on run `…211819Z`,
   started with the manifest deleted.

## Change history

| Date | Run | Change |
|---|---|---|
| 2026-11-20 | `20261120T204403Z` | v1 baseline on `v4.30.0` / `c5ea003` (issue #823 W5), suite under `proofs/` |
| 2026-11-20 | `20261120T210059Z` | suite moved to `tools/lean-toolcheck/` (PR #824 option (b)); re-run GREEN 22/22, numbers within ±0.3 s / ±25 MB of v1 |
| 2026-11-20 | `20261120T212158Z` | Red Team fix round: +MF05 (custom axiom), +`admit` in MF01, +KL01/KL02 known limits, +T18; preflight fixed for fresh checkouts; runs write to `results/runs/` and only `--update-baseline` touches this record; 3 consecutive full runs GREEN, SIGSEGV flake not reproduced |
