# Lean toolcheck — baseline on the current pins

**Run:** `20261120T223723Z` (2026-11-20 22:37–22:38 UTC, `tools/lean-toolcheck/run.sh --update-baseline`) ·
**overall GREEN — 29/29 files as expected**: 20 tool tests pass, 6 must-fail controls caught with the expected
message, 3 known-limit probes confirmed (report-only) · 109 theorems axiom-audited.
Machine-readable record: [`results/results-v4.30.0-c5ea003.json`](results/results-v4.30.0-c5ea003.json)
(+ the `.md` table). Re-run: `tools/lean-toolcheck/run.sh` — this writes only to `results/runs/<run-id>/`
(gitignored); the committed record changes only with `--update-baseline` on a full GREEN run. A later run on the
same pins that is much slower, or uses much more RSS, than this table is a **finding, not a pass** (#823 R6).

> **Limits.** The vacuity check is SYNTACTIC ONLY: the foundations checker catches the literal `: True :=` (MF03);
> `x = x → True` and `(fun _ => True) 3` pass both the checker and the axiom audit (KL01, report-only). A user
> `axiom` is caught by the axiom audit alone (MF05). The checker's own comment stripper is string-blind: after a
> string containing a block-comment opener it misses a `native_decide` (KL03; the audit still catches it).
>
> **How the grader reads Lean.** `lean --json`; only Lean's message stream is trusted; an axiom report counts only
> as an `information` message positioned at its `#print axioms` command; reports merge worst-case (MF06). Every
> expectation regex is matched against one Lean message or one checker `::error::` line.

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
| Wrapper | `boxrun --gpu --mem-mb 8000 --timeout 26100 --wait` — **one lease for the whole suite**, thermal guard on, RSS watch 8000 MB; 1 pinned core |
| Queue | started after 0 s in the queue (cool-start gate Tctl ≤ 58 °C); the box was busy (Agda suites, other seats' runs) around it |
| Duration | 86 s lease (81.8 s summed Lean wall time) |
| Thermal | Tctl 60.6 °C when the first file started; max 61.9 °C (boxrun record); **0 guard pauses**, guard action `none` |
| Host | AMD FX-8350 (8 cores), 31 991 MB RAM, 12.6 GB available at the end |
| Oleans | Mathlib `.oleans` borrowed from the main checkout via a symlinked `proofs/.lake/packages` (rev verified = the pin); nothing was built; page cache warm |

## Per-file results

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Axiom audit | Detection |
|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 5.22 | 3763 | 1 thm, no axioms | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.52 | 1827 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.35 | 1906 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.35 | 1937 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.81 | 1949 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.30 | 1922 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.67 | 2017 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.44 | 2810 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 4.15 | 2149 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 4.16 | 2378 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.71 | 2951 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.68 | 2127 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.28 | 2010 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 4.14 | 2783 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.42 | 2938 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.16 | 1943 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.56 | 1950 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.26 | 774 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.15 | 774 | 3 thm ⊆ std3 | — |
| `tests/T19_NestedComments.lean` | tool | ✅ PASS | 0 | 1.14 | 774 | 2 thm, no axioms | — |
| `must-fail/MF01_Sorry/…` | must-fail | ✅ caught | 0 | 1.17 | 774 | `['sorryAx']` | Lean warning ``declaration uses `sorry` `` · `sorryAx` on the direct, the inheriting AND the `admit` theorem · checker `RATCHET violated — sorry: 1 > baseline 0` (the checker does not count `admit`) |
| `must-fail/MF02_NativeDecide/…` | must-fail | ✅ caught | 0 | 1.14 | 774 | `['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']` | checker `HARD-BAN violated — native_decide: 1 occurrence` · non-standard axiom `…_native.native_decide.ax_1_1` |
| `must-fail/MF03_VacuousTrue/…` | must-fail | ✅ caught | 0 | 1.12 | 774 | 2 thm, no axioms | checker `HARD-BAN … : True := by trivial: 1 occurrence` + `RATCHET … vacuous-: True := theorem: 2 > baseline 0` (literal spelling only — see KL01) |
| `must-fail/MF04_FalseDecide/…` | must-fail | ✅ caught | 1 | 1.13 | 774 | — (file rejected) | ``Tactic `decide` proved that the proposition 2 + 3 = 1 is false`` (l.19) and ``… 1 - 2 = 0 is false`` (l.22, `Int`) |
| `must-fail/MF05_CustomAxiom/…` | must-fail | ✅ caught | 0 | 1.15 | 774 | `['QBPToolcheck.MF05.cheat']` | axiom audit only: `#print axioms` = `[QBPToolcheck.MF05.cheat]`; checker ACCEPTS (known limit, confirmed) |
| `must-fail/MF06_SpoofedAudit/…` | must-fail | ✅ caught | 0 | 1.16 | 774 | `['sorryAx']` | axiom audit (JSON, position-tied, worst-case) sees `sorryAx` despite 3 printed fake clean reports (ignored) · checker RATCHET |
| `known-limits/KL01_VacuityBypass/…` | known-limit | 🟡 known limit | 0 | 1.13 | 774 | 2 thm, no axioms | 🟡 confirmed: checker exit 0; both theorems `does not depend on any axioms` — vacuity check is syntactic |
| `known-limits/KL02_FinFoldlDecide/…` | known-limit | 🟡 known limit | 1 | 1.14 | 774 | — (file rejected) | 🟡 confirmed: elaborator `decide` stuck on `Fin.foldl` ("did not reduce to `isTrue` or `isFalse`") |
| `known-limits/KL03_CheckerStringComment/…` | known-limit | 🟡 known limit | 0 | 1.14 | 774 | `['QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1']` | 🟡 confirmed: checker exit 0 (string-blind stripper misses the `native_decide`); HARD: audit shows the native axiom |

"std3" = `{propext, Classical.choice, Quot.sound}`. RSS is `/usr/bin/time` `%M` of the `lake env lean` process tree
(the largest process, i.e. `lean`). Files without a Mathlib import (T17–T19, MF*, KL*) sit at the 774 MB Lean-core
floor; Mathlib-importing files at 1.8–3.8 GB, dominated by the import (cf. the 3.35 GiB `Mathlib.Tactic` floor in
`docs/foundations/lean-build-resource-notes.md`). Switching to `lean --json` changed neither time nor RSS.

### Repeatability and the observed SIGSEGV flake

| Run | Mode | Files | Result | Lease | Guard pauses | Crashes (exit ≥ 128) |
|---|---|---|---|---|---|---|
| `20261120T221059Z` | normal (final file set) | 29 | GREEN 29/29 | 132 s | 1 (box at 70.9 °C from other load; paused, resumed) | 0 |
| `20261120T221927Z` | normal | 29 | GREEN 29/29 | 86 s | 0 | 0 |
| `20261120T223723Z` | `--update-baseline` (this record) | 29 | GREEN 29/29 | 86 s | 0 | 0 |
| `…220452Z`, `…220639Z` | normal, during the Gemini round (28 / 29 files) | — | GREEN each | 88 s / — | 0 | 0 |
| `…211819Z`, `…212023Z`, `…212158Z` | Red Team round (26 files; the first with the manifest deleted) | 26 | GREEN each | 81–92 s | 0 | 0 |
| earlier (`…204151Z`, `…204403Z`, `…210059Z`) | 22-file suite | 22 | GREEN each | 71–74 s | 0 | 0 |

**Observed flake, not reproduced here.** The Red Team's first independent run on PR #824 (qbp-architecture,
issuecomment-7050748708, 2026-11-20) saw **T05 and T07 exit 139 (SIGSEGV) at 0.68 s, during import**, then pass
alone (3.1 s / 4.1 s) and in a full re-run; that box also logged intermittent `failed to create thread` aborts the
same day. Across the 11 full runs above, T05 and T07 each ran 11 times (3.0–4.3 s, 1.9 / 2.8 GB RSS) with **no
crash**. I have no burst log of the crashing run (it was the reviewer's), so it is recorded as an observed,
unreproduced flake — source: the reviewer's run. The suite does **not** retry: a crash (exit ≥ 128) is graded
FAIL with exit code, wall and RSS in the result row, so if it recurs the run is red and the row plus the boxrun
burst log (`~/.box-telemetry/bursts/lean-toolcheck-suite-<run-id>-*/`) are the evidence to hand to deming.

### Planted negative controls (`selftest_grader.py`, committed)

Raw logs of a real GREEN run were copied and one defect planted per copy; the grader ran on each copy. Run on this
record's raw logs (`…223723Z`): `python3 -I tools/lean-toolcheck/selftest_grader.py tools/lean-toolcheck <raw> <work> [old toolcheck.py]` → exit 0 ("every plant behaved as required"). The pre-fix rows used `de19998`'s `toolcheck.py`.

| Plant | Grader | Result |
|---|---|---|
| none (the real run) | new | GREEN, exit 0 |
| MF06 spoof (`#eval`-printed fake clean reports, plain + forged JSON) | **pre-fix (`de19998`)** | **FAIL — fooled**: `axiom audit MISSED sorryAx … (got [])` |
| same | new | caught: `sorryAx`; 3 axiom-like messages not positioned at a `#print axioms` command ignored |
| T19 nested comments (`#print axioms ghost` inside a nested comment) | **pre-fix (`de19998`)** | **FAIL**: `no axiom report for QBPToolcheck.T19.ghost` |
| same | new | PASS |
| MF04's error text demoted to an `information` message | new | FAIL: `Lean failed but without the expected message /^19:…/` (anchoring) |
| MF01's checker text moved off its `::error::` line | new | FAIL: `checker rejected but without the expected message` (anchoring) |
| fake clean report for MF05 at another position + a raw stdout line | new | caught: `cheat` still reported; spoof ignored |
| fake clean report for MF05 **at the real `#print axioms` site**, after the real one | new | caught: worst-case merge keeps `cheat` |
| suite copy without `known-limits/` | new | **RED**: `the known-limit layer has zero files` |
| `run.sh ZZZ` (prefix matches nothing) | runner | **REFUSED**, exit 2 |

Earlier controls (Red Team round): five planted misses in MF01–MF04 / T04 were all flagged (exit 1).

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
tree and pins. The tool layer needs only the Mathlib `.oleans`, so only the suite files (29) were run locally.
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
6. **The plain-text `#print axioms` output was spoofable** (Gemini (2)): on v4.30.0 the plain `lean` output prints
   axiom reports WITHOUT a position, interleaved with `#eval` stdout, so a printed fake line was indistinguishable.
   With `--json` each report is a message with `pos` (the `#print axioms` command's line/column) and `#eval` output
   is a separate message at the `#eval`'s position.
7. **The foundations checker itself (KL03)** has the same naive comment regex the grader had, and is string-blind:
   reproduced a `native_decide` in `proofs/QBP/Foundations` that would pass its HARD-BAN (checker exit 0). Not fixed
   here (no gate-script change in this PR); flagged for an issue.

## Change history

| Date | Run | Change |
|---|---|---|
| 2026-11-20 | `20261120T204403Z` | v1 baseline on `v4.30.0` / `c5ea003` (issue #823 W5), suite under `proofs/` |
| 2026-11-20 | `20261120T210059Z` | suite moved to `tools/lean-toolcheck/` (PR #824 option (b)); re-run GREEN 22/22, numbers within ±0.3 s / ±25 MB of v1 |
| 2026-11-20 | `20261120T212158Z` | Red Team fix round: +MF05 (custom axiom), +`admit` in MF01, +KL01/KL02 known limits, +T18; preflight fixed for fresh checkouts; runs write to `results/runs/` and only `--update-baseline` touches this record; 3 consecutive full runs GREEN, SIGSEGV flake not reproduced |
| 2026-11-20 | `20261120T223723Z` | Gemini fix round: `lean --json` + position-tied, worst-case axiom audit (+MF06 spoof control); nesting/string-aware comment lexer (+T19); anchored expectation matching; empty suite/layer/prefix RED; +KL03 (checker string-blind); 3 consecutive full runs GREEN 29/29 |
