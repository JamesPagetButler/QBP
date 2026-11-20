# Baseline — Agda 2.8.0 + agda/cubical `7b9019b` (2026-11-20)

The recorded reference for QBP#823 R6: versions, per-file pass/fail, wall time
and peak RSS, plus the box conditions. Any future pin move is compared against
this table; a big slowdown is a finding, not a pass.

## Toolchain and box

| item | value |
|---|---|
| Agda | 2.8.0 (official prebuilt static Linux bindist, `~/agda-2.8.0/agda`); CI pin 2.8.0 → `agda_match = true` |
| agda/cubical | CI pin `7b9019b2993535d6931991d87f5c762aee87a67a`; local `~/cubical` HEAD identical → `pin_match = true`; library `cubical-0.9`, flags `--cubical --safe --no-import-sorts --guardedness` |
| library interfaces | `~/cubical/_build` (38 MB, built 2026-08-31) present → library-dependent files load interfaces instead of re-checking the closure |
| box | AMD FX-8350, 32 GB; run via `boxrun --gpu --mem-mb 8000 --timeout 3600 --wait`, 1 thread, nice 19 |
| Tctl at start | 59.6 °C (full run); 40.2 °C (cold project-layer run) |
| run | `run.sh --layer all --update-baseline`, 2026-11-20T22:31:59Z → 2026-11-20T22:35:37Z (summed agda wall 213.5 s) |
| result | **0 unexpected** — 51 PASS · 4 REJECTED · 1 KNOWN-HOLE · 11 controls PASS; exit 0 |
| records | `results/results-2.8.0-7b9019b.json` / `.md` (full), `results/results-2.8.0-7b9019b-cold.json` / `.md` (project layer, QBP interfaces removed first) |
| scanner | PR #826's `scripts/agda_forbidden_tokens.py` (`origin/housekeeping/823-agda-ci-forbidden-tokens` @ `45a050e`, sha256 `a87ccd2daf512069…`), placed locally and uncommitted for this run; the control FAILS without it |
| timing note | this run's `lib` layer summed 135 s vs 83 s in the previous baseline run on the same pins (Tctl 59.6 °C at start, box shared with other seats' jobs; boxrun pauses at 65 °C): a box-temperature effect, not a toolchain change — the R6 comparison for a candidate should use a cool box (Tctl ≤ 50 °C at start) |

Peak RSS over the whole run: **507 MiB** (`SubstrateCharge.agda`, warm) / **644 MiB** (same file, cold). Nothing came near the 8 GB cap.

## Must-fail results (the gate bites)

| control | expected | observed |
|---|---|---|
| `mustfail/Postulate.agda` — top-level `postulate` under `--safe` | reject, `Cannot postulate` | REJECTED (rc 42) |
| `mustfail/Terminating.agda` — `{-# TERMINATING #-}` under `--safe` | reject, `TERMINATING` | REJECTED (rc 42) |
| `mustfail/Hole.agda` — `?` left in | reject, `Unsolved interaction metas` | REJECTED (rc 42) |
| `mustfail/BadPath.agda` — `λ _ → true : true ≡ false` | reject, `UnequalTerms` | REJECTED (rc 42) |
| `mustfail/LetPostulate.agda` — `let postulate p : ⊥ in p` under `--safe` (AFFECTED 2.8.0–2.8.0.2, FIXED-IN 2.9.0) | **known hole on 2.8.0** (agda/agda#8341) | **KNOWN-HOLE: accepted, rc 0** on Agda 2.8.0 < FIXED-IN — covered by the `forbidden-tokens` control (0 hits in 17 gated files, `--require-safe`). Grading test `TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 run.sh --layer mustfail` → `ACCEPTED … REGRESSION`, exit 1 (run 20261120T212435Z) |
| control `forbidden-tokens` — `forbidden_tokens.sh --require-safe` over the 17 gated files (raw text) | 0 hits | PASS |
| control `fixture-PlantedForbidden` (PLANTED: 9) | exactly 9 hits | PASS |
| control `fixture-B1StringFakeComment` (`s = "{-"` before a let-bound axiom) | exactly 1 hit | PASS |
| control `fixture-B2IdentifierDashDash` (`a--b` before an axiom on the same line) | exactly 1 hit | PASS |
| control `no-nested-source` — no `.agda`/`.lagda*` below the top level of a gated tree (`_build/` included) | 0 nested | PASS |
| controls `manifest-{tool,lib,mustfail,control,substrate,cubical}` — every `MANIFEST` entry found and run (12/22/5/3 exact; 4/13 listed ⊆ found) | 6 PASS | PASS |
| grader self-test (before the run) | 19/19 | PASS |

## Full run (all layers; QBP's own interfaces warm from the preceding run; `--update-baseline`)

| layer | file | status | rc | wall s | max RSS MiB |
|---|---|---|---|---|---|
| control | `manifest-tool` | PASS | — | — | 12 found, 12 listed |
| tool | `CircleHIT.agda` | PASS | 0 | 0.07 | 44.2 |
| tool | `CoreSyntax.agda` | PASS | 0 | 0.06 | 45.6 |
| tool | `GlueUa.agda` | PASS | 0 | 0.08 | 48.1 |
| tool | `Guardedness.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `HComp.agda` | PASS | 0 | 0.06 | 44.9 |
| tool | `Interval.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `LibFlags.agda` | PASS | 0 | 0.03 | 43.5 |
| tool | `LossyUnification.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `Opaque.agda` | PASS | 0 | 0.04 | 44.0 |
| tool | `PathP.agda` | PASS | 0 | 0.04 | 44.4 |
| tool | `SuspJoinHIT.agda` | PASS | 0 | 0.05 | 45.5 |
| tool | `Transp.agda` | PASS | 0 | 0.05 | 44.8 |
| control | `manifest-lib` | PASS | — | — | 22 found, 22 listed |
| lib | `LibConnected.agda` | PASS | 0 | 5.40 | 379.0 |
| lib | `LibDataBoolNat.agda` | PASS | 0 | 2.13 | 170.3 |
| lib | `LibDataInt.agda` | PASS | 0 | 3.48 | 234.4 |
| lib | `LibDataSigma.agda` | PASS | 0 | 0.81 | 93.4 |
| lib | `LibEquivIso.agda` | PASS | 0 | 0.34 | 67.0 |
| lib | `LibFunction.agda` | PASS | 0 | 0.17 | 55.3 |
| lib | `LibGroupBase.agda` | PASS | 0 | 5.92 | 399.1 |
| lib | `LibHLevelsGroupoid.agda` | PASS | 0 | 1.21 | 116.2 |
| lib | `LibHopf.agda` | PASS | 0 | 5.75 | 374.6 |
| lib | `LibHSpace.agda` | PASS | 0 | 5.72 | 380.0 |
| lib | `LibJoin.agda` | PASS | 0 | 56.29 | 327.9 |
| lib | `LibLoopspace.agda` | PASS | 0 | 4.32 | 295.9 |
| lib | `LibPinSn.agda` | PASS | 0 | 7.81 | 493.0 |
| lib | `LibPointed.agda` | PASS | 0 | 1.42 | 124.0 |
| lib | `LibPrelude.agda` | PASS | 0 | 0.15 | 56.1 |
| lib | `LibS1.agda` | PASS | 0 | 3.57 | 250.7 |
| lib | `LibSn.agda` | PASS | 0 | 5.50 | 376.5 |
| lib | `LibSnDegree.agda` | PASS | 0 | 7.89 | 473.3 |
| lib | `LibSnMultiplication.agda` | PASS | 0 | 5.80 | 371.6 |
| lib | `LibSusp.agda` | PASS | 0 | 4.79 | 335.5 |
| lib | `LibTruncations.agda` | PASS | 0 | 4.46 | 302.7 |
| lib | `LibUnivalence.agda` | PASS | 0 | 2.19 | 171.9 |
| control | `manifest-mustfail` | PASS | — | — | 5 found, 5 listed |
| mustfail | `BadPath.agda` | REJECTED | 42 | 0.04 | 44.3 |
| mustfail | `Hole.agda` | REJECTED | 42 | 0.04 | 44.6 |
| mustfail | `LetPostulate.agda` | KNOWN-HOLE | 0 | 0.03 | 43.5 |
| mustfail | `Postulate.agda` | REJECTED | 42 | 0.03 | 44.1 |
| mustfail | `Terminating.agda` | REJECTED | 42 | 0.03 | 43.8 |
| control | `manifest-substrate` | PASS | — | — | 4 found, 4 listed |
| substrate | `QBPHSpace.agda` | PASS | 0 | 0.04 | 44.1 |
| substrate | `QBPJoin.agda` | PASS | 0 | 0.05 | 45.3 |
| substrate | `QBPSpheres.agda` | PASS | 0 | 0.04 | 44.6 |
| substrate | `QBPSubstrate.agda` | PASS | 0 | 0.04 | 44.3 |
| control | `manifest-cubical` | PASS | — | — | 13 found, 13 listed |
| cubical | `AssocTransport.agda` | PASS | 0 | 5.71 | 394.5 |
| cubical | `CDAssocBool.agda` | PASS | 0 | 5.64 | 395.7 |
| cubical | `CDAssocCubesStatus.agda` | PASS | 0 | 5.87 | 401.2 |
| cubical | `CDAssocReduction.agda` | PASS | 0 | 5.64 | 372.9 |
| cubical | `CDJoinBR.agda` | PASS | 0 | 5.54 | 381.9 |
| cubical | `CDLawsBool.agda` | PASS | 0 | 5.53 | 379.8 |
| cubical | `Diamond.agda` | PASS | 0 | 4.55 | 293.1 |
| cubical | `HopfNoAssoc.agda` | PASS | 0 | 5.61 | 362.1 |
| cubical | `QBPS3HSpace.agda` | PASS | 0 | 5.68 | 380.7 |
| cubical | `QuaternionicHopf.agda` | PASS | 0 | 6.00 | 401.9 |
| cubical | `S3FromCD.agda` | PASS | 0 | 5.86 | 413.8 |
| cubical | `SkyrmionCharge.agda` | PASS | 0 | 7.92 | 503.7 |
| cubical | `SubstrateCharge.agda` | PASS | 0 | 7.92 | 507.4 |
| control | `no-nested-source` | PASS | — | — | no .agda/.lagda* source below the top level of proofs/agda or proofs/agda-cubical |
| control | `forbidden-tokens` | PASS | — | — | 0 hits over proofs/agda + proofs/agda-cubical (--require-safe; scripts/agda_forbidden_tokens.py) |
| control | `manifest-control` | PASS | — | — | 3 found, 3 listed |
| control | `fixture-B1StringFakeComment` | PASS | — | — | fixture yields 1/1 planted hits |
| control | `fixture-B2IdentifierDashDash` | PASS | — | — | fixture yields 1/1 planted hits |
| control | `fixture-PlantedForbidden` | PASS | — | — | fixture yields 9/9 planted hits |

Summed agda wall time: tool 0.60 s · lib 135.1 s · mustfail 0.17 s · project 77.6 s.

## Project layer, cold (QBP's `_build/` removed first; library interfaces still warm)

Same 17 files, `run.sh --layer project`, 2026-11-20T20:55:31Z → 20:56:56Z, all PASS; summed wall 84.5 s (vs 77.1 s warm). The files that absorb a re-check of their QBP imports: `CDAssocBool` 8.66 s / 450 MiB, `HopfNoAssoc` 6.37 s, `SkyrmionCharge` 9.01 s / 554 MiB, `SubstrateCharge` 10.20 s / **644 MiB** (the run's peak). Nothing else moved by more than 0.1 s. Reading: QBP's own chain is cheap; the cost of a library-dependent check is loading the pinned library's interfaces (~4–5 s, ~300 MiB floor per file). A cold *library* build (no `~/cubical/_build`, what CI does each time) was not measured here — it re-checks the import closure of all 34 modules and is the dominant cost of the CI job.

## Demonstrations (Gemini round, `review-20261120-214517`; each fix has a failing case)

| finding | demonstration | observed |
|---|---|---|
| (5) baseline written before grading | `TOOLCHECK_INJECT_FAIL=1 run.sh --layer tool --update-baseline` (run `20261120T215843Z`) | `control FAIL injected-failure`, `1 UNEXPECTED`, exit 1; `sha256sum results/results-2.8.0-7b9019b.{json,md}` before = after (`8c11d9a4…`, `157cad15…`): **baseline byte-identical** |
| (6) empty / renamed layer goes green | alt `MANIFEST` without `tool/Interval.agda` and with `tool/RenamedOrMissing.agda`, `TOOLCHECK_MANIFEST=… run.sh --layer tool` (run `20261120T215848Z`) | `control FAIL manifest-tool … listed but not found: RenamedOrMissing.agda`, exit 1 |
| (1) empty `EXPECT:` always matches; match against the whole log | grader self-test cases `fail-empty-expect` → WRONG-ERROR, `fail-msg-only-in-echo` (message present only in the `Checking postulate-in-name …` echo) → WRONG-ERROR, `fail-wrong-message` → WRONG-ERROR, `hole-empty-expect` → WRONG-ERROR | 19/19 self-test cases ok; the self-test runs before every suite run and `run.sh --self-test` runs it alone |
| (4) signal exit counted as `rc != 0` | self-test cases `pass-signal-137`, `fail-signal-not-reject` (rc 139 with the expected message present), `hole-signal` → CRASH | CRASH is unexpected in every layer |
| (3) flat `*.agda` globs | planted tree: `root/Clean.agda` (clean), `root/sub/Lit.lagda.md` (let-bound axiom, no `--safe`), `root/sub/x.agda-lib` (pragma name in a comment), `root/sub/_build/Hidden.agda` (`primTrustMe-user`), `root/sub/Link.agda` → symlink to an outside file; `forbidden_tokens.sh --require-safe root` | 6 hits: symlink, `_build` token, literate token, `.agda-lib` token, 2 missing-safe; PR #826's script at `45a050e` on the same tree: 5 findings on the same four files (it also reads through the symlink) |
| (3) r2 — one scanner, fail-closed | `run.sh --layer project` with `scripts/agda_forbidden_tokens.py` absent (run `20261120T221533Z`) | `control FAIL forbidden-tokens … requires PR #826's scanner (scripts/agda_forbidden_tokens.py)`, the three fixtures FAIL (0 hits), `5 UNEXPECTED`, exit 1. The green baseline below was produced with #826's file placed locally from `origin/housekeeping/823-agda-ci-forbidden-tokens` (uncommitted); **#825 merges after #826** |
| (7) r2 — unchecked nested source | planted `proofs/agda/_build/nested/Planted.lagda.md` (a let-bound axiom, git-ignored path), same run `20261120T221533Z` | `control FAIL no-nested-source … unchecked nested source: proofs/agda/_build/nested/Planted.lagda.md`; the file is not type-checked (CI's `*.agda` loop would not see it either); removed after the run |
| F2 (Red Team) hole not keyed to the pin | `TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 run.sh --layer mustfail` (run `20261120T212435Z`) | `mustfail ACCEPTED LetPostulate.agda … REGRESSION`, exit 1; self-test `hole-at-fix-accepted`, `hole-after-fix-accepted` → ACCEPTED |

## How to reproduce

```bash
cd <QBP checkout>
TOOLCHECK_MEM_MB=8000 TOOLCHECK_TIMEOUT=3600 tools/agda-toolcheck/run.sh --update-baseline   # full; rewrites results/results-*.{json,md}
rm -rf proofs/agda/_build proofs/agda-cubical/_build
TOOLCHECK_TAG=cold tools/agda-toolcheck/run.sh --layer project --update-baseline  # cold project layer → results-*-cold.{json,md}
TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 tools/agda-toolcheck/run.sh --layer mustfail   # F2 grading test: must exit 1
```

Resource estimate used for this run (pre-run gate): ≤ 1 GB RSS per file expected from the README figures (SubstrateCharge < 700 MB, QuaternionicHopf < 530 MB), ≤ 6 GB worst case for `SkyrmionCharge` under `--lossy-unification`; disk < 50 MB of interface files; cap 8 GB RSS / 3600 s enforced by boxrun. Observed: 644 MiB peak (cold), 507 MiB (warm full run), 2 min 57 s for the full run.
