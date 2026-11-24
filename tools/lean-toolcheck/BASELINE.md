# Lean toolcheck — baseline on the current pins

**Run:** `20261124T234344Z` (2026-11-24 23:43–23:45 UTC, `tools/lean-toolcheck/run.sh --update-baseline`) ·
**overall GREEN — 37/37 files as expected**: 20 tool tests pass, 14 must-fail controls caught with the expected
message, 3 known-limit probes confirmed (report-only) · 120 theorems axiom-audited. (The per-file table below keeps
the `20261121T021507Z` numbers for T00–MF09; MF10–MF14 rows are from `20261124T234344Z`; the committed
`results/` record is the new run.)
Machine-readable record: [`results/results-v4.30.0-c5ea003.json`](results/results-v4.30.0-c5ea003.json)
(+ the `.md` table). Re-run: `tools/lean-toolcheck/run.sh` — this writes only to `results/runs/<run-id>/`
(gitignored); the committed record changes only with `--update-baseline` on a full GREEN run. A later run on the
same pins that is much slower, or uses much more RSS, than this table is a **finding, not a pass** (#823 R6).

> **Limits.** The vacuity check is SYNTACTIC ONLY: the foundations checker catches the literal `: True :=` (MF03);
> `x = x → True` and `(fun _ => True) 3` pass both the checker and the axiom audit (KL01, report-only). A user
> `axiom` is caught by the axiom audit alone (MF05). The checker's own comment stripper is string-blind: after a
> string containing a block-comment opener it misses a `native_decide` (KL03; the audit still catches it).
>
> **How the grader reads Lean.** `lean --json`; an axiom report counts only as an `information` message positioned
> at its `#print axioms` command; reports merge worst-case (MF06). Stdout is **not** a trusted channel — code the
> file runs can forge a message on `/dev/stdout` and exit before Lean prints the real report (MF14) — so a pass file
> is graded fail-closed: one report per site, none off a site, no non-Lean stdout line, no code-executing construct
> (`EXEC_RE`, a supported-subset denylist; the out-of-process audit is QBP#827). Lines are counted Lean's way:
> bytes, only `\r\n` → `\n`, split at `\n` only (MF10/MF11). Every expectation regex is matched against one Lean
> message or one checker `::error::` line.
>
> **Coverage: the audit covers the `#print axioms` sites the lexer finds (anywhere on a line, MF07); the suite
> convention is one site per theorem.** A file with a brace inside a string literal is refused (MF08: the lexer does
> not model interpolation). Site columns are computed in Lean's `pos.column` unit — codepoints, pinned by probe
> and re-checked on MF09's real output every self-test.

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
| Wrapper | `boxrun --gpu --mem-mb 8000 --timeout 28800 --wait` — **one lease for the whole suite**, thermal guard on, RSS watch 8000 MB; 1 pinned core |
| Queue | started after 0 s in the queue (cool-start gate Tctl ≤ 58 °C); the box was busy (Agda suites, other seats' runs) around it |
| Duration | 91 s lease (86.5 s summed Lean wall time) |
| Thermal | Tctl 57.9 °C when the first file started; max 68.8 °C (boxrun record, other load); **1 guard pause** (paused, resumed; no kill) |
| Host | AMD FX-8350 (8 cores), 31 991 MB RAM, 12.4 GB available at the end |
| Oleans | Mathlib `.oleans` borrowed from the main checkout via a symlinked `proofs/.lake/packages` (rev verified = the pin); nothing was built; page cache warm |

## Per-file results

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Axiom audit | Detection |
|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 4.54 | 3796 | 1 thm, no axioms | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.17 | 1843 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.12 | 1926 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.12 | 1952 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.71 | 1967 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.04 | 1936 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.40 | 2042 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 3.96 | 2844 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.69 | 2166 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 3.80 | 2402 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.32 | 2986 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.36 | 2141 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.14 | 2026 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 3.94 | 2811 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.10 | 2963 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.05 | 1957 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.48 | 1971 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 7.40 | 776 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.35 | 776 | 3 thm ⊆ std3 | — |
| `tests/T19_NestedComments.lean` | tool | ✅ PASS | 0 | 1.14 | 776 | 2 thm, no axioms | — |
| `must-fail/MF01_Sorry/…` | must-fail | ✅ caught | 0 | 1.14 | 776 | `['sorryAx']` | Lean warning ``declaration uses `sorry` `` · `sorryAx` on the direct, the inheriting AND the `admit` theorem · checker `RATCHET violated — sorry: 1 > baseline 0` (the checker does not count `admit`) |
| `must-fail/MF02_NativeDecide/…` | must-fail | ✅ caught | 0 | 1.14 | 776 | `['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']` | checker `HARD-BAN violated — native_decide: 1 occurrence` · non-standard axiom `…_native.native_decide.ax_1_1` |
| `must-fail/MF03_VacuousTrue/…` | must-fail | ✅ caught | 0 | 1.13 | 776 | 2 thm, no axioms | checker `HARD-BAN … : True := by trivial: 1 occurrence` + `RATCHET … vacuous-: True := theorem: 2 > baseline 0` (literal spelling only — see KL01) |
| `must-fail/MF04_FalseDecide/…` | must-fail | ✅ caught | 1 | 1.15 | 776 | — (file rejected) | ``Tactic `decide` proved that the proposition 2 + 3 = 1 is false`` (l.19) and ``… 1 - 2 = 0 is false`` (l.22, `Int`) |
| `must-fail/MF05_CustomAxiom/…` | must-fail | ✅ caught | 0 | 1.13 | 776 | `['QBPToolcheck.MF05.cheat']` | axiom audit only: `#print axioms` = `[QBPToolcheck.MF05.cheat]`; checker ACCEPTS (known limit, confirmed) |
| `must-fail/MF06_SpoofedAudit/…` | must-fail | ✅ caught | 0 | 1.16 | 776 | `['sorryAx']` | axiom audit (JSON, position-tied, worst-case) sees `sorryAx` despite 3 printed fake clean reports (ignored) · checker RATCHET |
| `must-fail/MF07_SameLineSite/…` | must-fail | ✅ caught | 0 | 1.13 | 776 | `[]`; `['QBPToolcheck.MF07.cheat']` | sites found anywhere on a line: `dirty` (col 38) reports `[QBPToolcheck.MF07.cheat]` |
| `must-fail/MF08_InterpolationLexer/…` | must-fail | ✅ caught | 0 | 1.15 | 776 | `[]`; `['QBPToolcheck.MF08.cheat']` | grader REFUSES (brace inside a string literal, l.37); audit of every Lean report still shows `cheat` |
| `must-fail/MF09_NonAsciiColumn/…` (with astral `𝔽`, run `…234344Z`) | must-fail | ✅ caught | 0 | 1.24 | 784 | `[]`; `['QBPToolcheck.MF09.cheat']` | column in Lean's unit (codepoints, pinned vs bytes AND UTF-16): `dirty` after `αβγ` + `𝔽` reports `[QBPToolcheck.MF09.cheat]` |
| `must-fail/MF10_FormFeedLineDesync/…` | must-fail | ✅ caught | 0 | 2.39 | 1444 | `['QBPToolcheck.MF10.cheat']` | lines split at `\n` only: real report at (33, 79) accepted; forged `run_cmd` clean report at (33, 0) ignored |
| `must-fail/MF11_LoneCRLineDesync/…` | must-fail | ✅ caught | 0 | 2.38 | 1444 | `['QBPToolcheck.MF11.cheat']` | bytes read, lone `\r` not a break: real report at line 30 accepted; forged one at line 31 ignored |
| `must-fail/MF12_EscapedQuoteSite/…` | must-fail | ✅ caught | 0 | 1.30 | 784 | `['QBPToolcheck.MF12.cheat']` | site after `"a\"b"` found |
| `must-fail/MF13_CleanBraceRefused/…` | must-fail | ✅ caught | 0 | 1.17 | 784 | `[]` | grader REFUSES (brace in a string, l.19) |
| `must-fail/MF14_ExecForgesStdout/…` | must-fail | ✅ caught | 0 | 1.25 | 784 | `[]` (**forged** — the real report was never printed) | exec refusal (l.27 `#eval`); the stdout audit alone is fooled, as designed |
| `known-limits/KL01_VacuityBypass/…` | known-limit | 🟡 known limit | 0 | 1.13 | 776 | 2 thm, no axioms | 🟡 confirmed: checker exit 0; both theorems `does not depend on any axioms` — vacuity check is syntactic |
| `known-limits/KL02_FinFoldlDecide/…` | known-limit | 🟡 known limit | 1 | 1.14 | 776 | — (file rejected) | 🟡 confirmed: elaborator `decide` stuck on `Fin.foldl` ("did not reduce to `isTrue` or `isFalse`") |
| `known-limits/KL03_CheckerStringComment/…` | known-limit | 🟡 known limit | 0 | 1.15 | 776 | `['QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1']` | 🟡 confirmed: checker exit 0 (string-blind stripper misses the `native_decide`); HARD: audit shows the native axiom |

"std3" = `{propext, Classical.choice, Quot.sound}`. RSS is `/usr/bin/time` `%M` of the `lake env lean` process tree
(the largest process, i.e. `lean`). Files without a Mathlib import (T17–T19, MF*, KL*) sit at the 774 MB Lean-core
floor; Mathlib-importing files at 1.8–3.8 GB, dominated by the import (cf. the 3.35 GiB `Mathlib.Tactic` floor in
`docs/foundations/lean-build-resource-notes.md`). Switching to `lean --json` changed neither time nor RSS.

### Repeatability and the observed SIGSEGV flake

| Run | Mode | Files | Result | Lease | Guard pauses | Crashes (exit ≥ 128) |
|---|---|---|---|---|---|---|
| `20261121T021138Z` | normal (Gemini r3 final set) | 32 | GREEN 32/32 | 85 s | 0 | 0 |
| `20261121T021317Z` | normal | 32 | GREEN 32/32 | 86 s | 0 | 0 |
| `20261121T021507Z` | `--update-baseline` (this record) | 32 | GREEN 32/32 | 91 s | 1 | 0 |
| `20261120T225231Z` | normal (Gemini r2 final set) | 31 | GREEN 31/31 | 87 s | 0 | 0 |
| `20261120T225600Z` | normal | 31 | GREEN 31/31 | 86 s | 0 | 0 |
| `20261120T230310Z` | `--update-baseline` (previous record) | 31 | GREEN 31/31 | 86 s | 0 | 0 |
| `20261120T221059Z` | normal (final file set) | 29 | GREEN 29/29 | 132 s | 1 (box at 70.9 °C from other load; paused, resumed) | 0 |
| `20261120T221927Z` | normal | 29 | GREEN 29/29 | 86 s | 0 | 0 |
| `20261120T223723Z` | `--update-baseline` (previous record) | 29 | GREEN 29/29 | 86 s | 0 | 0 |
| `…220452Z`, `…220639Z` | normal, during the Gemini round (28 / 29 files) | — | GREEN each | 88 s / — | 0 | 0 |
| `…211819Z`, `…212023Z`, `…212158Z` | Red Team round (26 files; the first with the manifest deleted) | 26 | GREEN each | 81–92 s | 0 | 0 |
| earlier (`…204151Z`, `…204403Z`, `…210059Z`) | 22-file suite | 22 | GREEN each | 71–74 s | 0 | 0 |

**Observed flake, not reproduced here.** The Red Team's first independent run on PR #824 (qbp-architecture,
issuecomment-7050748708, 2026-11-20) saw **T05 and T07 exit 139 (SIGSEGV) at 0.68 s, during import**, then pass
alone (3.1 s / 4.1 s) and in a full re-run; that box also logged intermittent `failed to create thread` aborts the
same day. Across the 17 full runs above, T05 and T07 each ran 17 times (3.0–4.3 s, 1.9 / 2.8 GB RSS) with **no
crash**. I have no burst log of the crashing run (it was the reviewer's), so it is recorded as an observed,
unreproduced flake — source: the reviewer's run. The suite does **not** retry: a crash (exit ≥ 128) is graded
FAIL with exit code, wall and RSS in the result row, so if it recurs the run is red and the row plus the boxrun
burst log (`~/.box-telemetry/bursts/lean-toolcheck-suite-<run-id>-*/`) are the evidence to hand to deming.

### Planted negative controls (`selftest_grader.py`, committed)

Raw logs of a real GREEN run were copied and one defect planted per copy; the grader ran on each copy. Run on this
record's raw logs (`…225231Z`, same files): `python3 -I tools/lean-toolcheck/selftest_grader.py tools/lean-toolcheck <raw> <work> [old toolcheck.py]` → exit 0 ("every plant behaved as required"). Pre-fix rows: `de19998`'s grader for MF06/T19, `ef8b54f`'s for MF07/MF08.

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
| MF07 replayed as a **pass-labelled** attack (same-line hidden site, user axiom) | **pre-r2 (`ef8b54f`)** | **PASS — exploitable** (the real report was discarded as unpositioned) |
| same | new | **FAIL**: `QBPToolcheck.MF07.dirty: non-standard axioms ['QBPToolcheck.MF07.cheat']` |
| MF08 replayed as a **pass-labelled** attack (`s!` interpolation hides the rest of the file) | **pre-r2 (`ef8b54f`)** | **PASS — exploitable** |
| same | new | **FAIL**: `grader REFUSES the file: brace inside a string literal` |
| MF09 replayed as a pass-labelled attack (multi-byte prefix before a same-line site) | pre-r3 (`4c0aecb`) and new | **FAIL** both — Lean counts codepoints, the same unit as Python's str index, so there was no mismatch to exploit |
| **unit pin** on MF09's real Lean output | new | PASS: Lean reported column 37 = codepoint offset 37 (UTF-8 byte offset 40) |
| **unit pin** on MF09 with astral `𝔽` (run `…234344Z`) | new | PASS: Lean (33, 45) = codepoints 45; bytes 51; UTF-16 46 |
| **line-rule pins** on MF10 / MF11 real output | new | PASS: Lean line 33 / 30 = `\n`-only rule; Python rule (splitlines / universal newlines) 34 / 31 |
| MF10 / MF11 replayed as pass-labelled attacks (T93/T94) | **`19bbbd4`** | **PASS — exploitable** (real report discarded, forged `run_cmd` report accepted) |
| same | new | **FAIL** (exec refusal, unpositioned report, `cheat`) |
| MF14 replayed as a pass-labelled attack (T98: `#eval` forges `/dev/stdout`, then exits 0) | **`19bbbd4`** | **PASS — exploitable** |
| same | new | **FAIL**: code-executing construct refused |
| MF13 replayed as a pass file (T97, clean + brace) / MF13 with the brace removed | new | **FAIL** by refusal / **FAIL** (`grader-refuses` not met) |
| forged clean report off-site (T96) / at-site as `warning` (T96b), real report removed | new | **FAIL** both (spoof guard: position / severity) |
| clean T01 + duplicate report at a site / + forged report off-site / + non-Lean stdout line / + severity-less JSON at a site | new | **FAIL** each (fail-closed pass rules) |
| MF01 with an UNANCHORED checker regex and the text on a `note:` line | new | **FAIL** (`::error` lines only) |
| T19 with `#print axioms` inside a string literal | new | PASS (strings are not commands) |
| `mutants_grader.py`: 25 grader mutants (M01–M19 reconstructed from the Red Team list, M20–M25 new rules) | new | **24 KILLED, 1 SURVIVED** (M04, equivalent: code-only and original lines have equal length) |
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

### Lean column-unit probe (Gemini r3 (e), 2026-11-21, v4.30.0)

`lake env lean --json` on a 7-line probe, each line with a non-ASCII prefix before a same-line command:

| Source line | Lean `pos.column` | `#` codepoint offset | `#` UTF-8 byte offset | Message |
|---|---|---|---|---|
| `def αβγ : Nat := 1 #print axioms dirty` | **19** | **19** | 22 | `'dirty' depends on axioms: [cheat]` |
| `def ℕℕ : Nat := 2 #print axioms clean` | **18** | **18** | 22 | `'clean' does not depend on any axioms` |
| `def δ : Nat := 3 #eval IO.println "'dirty' does not depend …"` | **17** | **17** (of `#eval`) | 18 | the printed text, as an information message **at the `#eval`** |
| `#eval IO.println "\n'dirty' does not depend …"` (newline inside the output) | **0** | 0 | 0 | the printed text, still at the `#eval`'s own position |

So Lean's column unit is codepoints, and `#eval` output is always positioned at its own `#eval` command, even when it
prints newlines. It can never land on a `#print axioms` site; if it did, worst-case merge would still keep the real
report.

## Line-break probe (Gemini r4 (f), 2026-11-24, `lean --json`, v4.30.0)

One physical line `#check a /- X -/ #check b` per character X; the second `#check`'s reported line shows whether X
starts a line. Then X placed in code position.

| X | in a comment: `b` reported at | in code |
|---|---|---|
| `\r` (lone) | same line, col 37 | error `isolated carriage returns are not allowed` |
| `\v`, `\f`, `\x1c`, `\x1d`, `\x1e` | same line, col 37 | error `expected token` |
| `\x85` | same line, col 38 | error `expected token` |
| U+2028, U+2029 | same line, col 39 | error `expected token` |
| `\r\n` | **next line**, col 4 | accepted (a line break) |

So Lean breaks lines only at `\n`, with `\r\n` normalised (`FileMap.ofString`, `crlfToLf` in `mkInputContext`), and
none of the other characters is even legal outside a comment or string. Gemini's literal counterexample (a form
feed at the start of a code line) is therefore a Lean parse error, not a silent pass; the attack is real once the
character sits in a comment (MF10), and a lone `\r` in a comment is a second, independent vector through Python's
text-mode universal newlines (MF11).

## Change history

| Date | Run | Change |
|---|---|---|
| 2026-11-20 | `20261120T204403Z` | v1 baseline on `v4.30.0` / `c5ea003` (issue #823 W5), suite under `proofs/` |
| 2026-11-20 | `20261120T210059Z` | suite moved to `tools/lean-toolcheck/` (PR #824 option (b)); re-run GREEN 22/22, numbers within ±0.3 s / ±25 MB of v1 |
| 2026-11-20 | `20261120T212158Z` | Red Team fix round: +MF05 (custom axiom), +`admit` in MF01, +KL01/KL02 known limits, +T18; preflight fixed for fresh checkouts; runs write to `results/runs/` and only `--update-baseline` touches this record; 3 consecutive full runs GREEN, SIGSEGV flake not reproduced |
| 2026-11-20 | `20261120T223723Z` | Gemini fix round: `lean --json` + position-tied, worst-case axiom audit (+MF06 spoof control); nesting/string-aware comment lexer (+T19); anchored expectation matching; empty suite/layer/prefix RED; +KL03 (checker string-blind); 3 consecutive full runs GREEN 29/29 |
| 2026-11-20 | `20261120T230310Z` | Gemini r2: sites anywhere on a line (+MF07); braces in strings refused (+MF08); string bodies blanked for site detection; coverage statement; 3 consecutive full runs GREEN 31/31 |
| 2026-11-21 | `20261121T021507Z` | Gemini r3 (e): column unit probed (codepoints) and pinned (`LEAN_COLUMN_UNIT`, computed from the original source line); +MF09; self-test unit pin; 3 consecutive full runs GREEN 32/32 |
| 2026-11-24 | `20261124T234344Z` | Gemini r4 (f) + Red Team (`19bbbd4`): `\n`-only line model, bytes read (+MF10, +MF11, line-rule pins); fail-closed pass rules and `EXEC_RE` code-execution refusal (+MF14); +MF12 (escaped quote), +MF13 (clean-brace refusal); astral `𝔽` in MF09; guard-dependent plants; `mutants_grader.py` 24/25; 3 full runs GREEN (34/34 before MF12–MF14, then 37/37 ×2) |
