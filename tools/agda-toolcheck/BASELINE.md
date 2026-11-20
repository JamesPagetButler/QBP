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
| Tctl at start | 56 °C (full run); 40.2 °C (cold project-layer run) |
| run | `run.sh --layer all --update-baseline`, 2026-11-20T21:26:11Z → 2026-11-20T21:29:08Z (summed agda wall 174.3 s) |
| result | **0 unexpected** — 51 PASS · 4 REJECTED · 1 KNOWN-HOLE · 4 controls PASS; exit 0 |
| records | `results/results-2.8.0-7b9019b.json` / `.md` (full), `results/results-2.8.0-7b9019b-cold.json` / `.md` (project layer, QBP interfaces removed first) |

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

## Full run (all layers; QBP's own interfaces warm from the preceding run; `--update-baseline`)

| layer | file | status | rc | wall s | max RSS MiB |
|---|---|---|---|---|---|
| tool | `CircleHIT.agda` | PASS | 0 | 0.04 | 44.2 |
| tool | `CoreSyntax.agda` | PASS | 0 | 0.06 | 45.6 |
| tool | `GlueUa.agda` | PASS | 0 | 0.09 | 48.0 |
| tool | `Guardedness.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `HComp.agda` | PASS | 0 | 0.06 | 44.9 |
| tool | `Interval.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `LibFlags.agda` | PASS | 0 | 0.03 | 43.5 |
| tool | `LossyUnification.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `Opaque.agda` | PASS | 0 | 0.04 | 44.0 |
| tool | `PathP.agda` | PASS | 0 | 0.04 | 44.4 |
| tool | `SuspJoinHIT.agda` | PASS | 0 | 0.05 | 45.5 |
| tool | `Transp.agda` | PASS | 0 | 0.05 | 44.8 |
| lib | `LibConnected.agda` | PASS | 0 | 5.47 | 378.8 |
| lib | `LibDataBoolNat.agda` | PASS | 0 | 2.07 | 170.3 |
| lib | `LibDataInt.agda` | PASS | 0 | 3.33 | 234.4 |
| lib | `LibDataSigma.agda` | PASS | 0 | 0.79 | 93.4 |
| lib | `LibEquivIso.agda` | PASS | 0 | 0.34 | 67.0 |
| lib | `LibFunction.agda` | PASS | 0 | 0.17 | 55.3 |
| lib | `LibGroupBase.agda` | PASS | 0 | 5.73 | 399.0 |
| lib | `LibHLevelsGroupoid.agda` | PASS | 0 | 1.16 | 116.2 |
| lib | `LibHopf.agda` | PASS | 0 | 5.63 | 374.8 |
| lib | `LibHSpace.agda` | PASS | 0 | 5.57 | 379.8 |
| lib | `LibJoin.agda` | PASS | 0 | 4.59 | 323.7 |
| lib | `LibLoopspace.agda` | PASS | 0 | 4.14 | 295.8 |
| lib | `LibPinSn.agda` | PASS | 0 | 7.59 | 493.0 |
| lib | `LibPointed.agda` | PASS | 0 | 1.41 | 124.0 |
| lib | `LibPrelude.agda` | PASS | 0 | 0.14 | 56.0 |
| lib | `LibS1.agda` | PASS | 0 | 3.54 | 250.6 |
| lib | `LibSn.agda` | PASS | 0 | 5.48 | 376.5 |
| lib | `LibSnDegree.agda` | PASS | 0 | 7.78 | 473.3 |
| lib | `LibSnMultiplication.agda` | PASS | 0 | 5.61 | 371.6 |
| lib | `LibSusp.agda` | PASS | 0 | 4.76 | 335.5 |
| lib | `LibTruncations.agda` | PASS | 0 | 4.31 | 302.6 |
| lib | `LibUnivalence.agda` | PASS | 0 | 2.06 | 171.9 |
| mustfail | `BadPath.agda` | REJECTED | 42 | 0.04 | 44.4 |
| mustfail | `Hole.agda` | REJECTED | 42 | 0.04 | 44.6 |
| mustfail | `LetPostulate.agda` | KNOWN-HOLE | 0 | 0.03 | 43.5 |
| mustfail | `Postulate.agda` | REJECTED | 42 | 0.03 | 44.1 |
| mustfail | `Terminating.agda` | REJECTED | 42 | 0.03 | 43.8 |
| substrate | `QBPHSpace.agda` | PASS | 0 | 0.04 | 44.0 |
| substrate | `QBPJoin.agda` | PASS | 0 | 0.05 | 45.2 |
| substrate | `QBPSpheres.agda` | PASS | 0 | 0.04 | 44.5 |
| substrate | `QBPSubstrate.agda` | PASS | 0 | 0.04 | 44.2 |
| cubical | `AssocTransport.agda` | PASS | 0 | 5.89 | 391.1 |
| cubical | `CDAssocBool.agda` | PASS | 0 | 19.15 | 395.7 |
| cubical | `CDAssocCubesStatus.agda` | PASS | 0 | 5.89 | 401.1 |
| cubical | `CDAssocReduction.agda` | PASS | 0 | 5.67 | 372.5 |
| cubical | `CDJoinBR.agda` | PASS | 0 | 5.79 | 381.9 |
| cubical | `CDLawsBool.agda` | PASS | 0 | 5.57 | 379.8 |
| cubical | `Diamond.agda` | PASS | 0 | 4.57 | 293.2 |
| cubical | `HopfNoAssoc.agda` | PASS | 0 | 5.56 | 362.0 |
| cubical | `QBPS3HSpace.agda` | PASS | 0 | 5.65 | 380.8 |
| cubical | `QuaternionicHopf.agda` | PASS | 0 | 5.99 | 401.8 |
| cubical | `S3FromCD.agda` | PASS | 0 | 5.77 | 413.8 |
| cubical | `SkyrmionCharge.agda` | PASS | 0 | 8.05 | 503.6 |
| cubical | `SubstrateCharge.agda` | PASS | 0 | 8.19 | 507.4 |
| control | `forbidden-tokens` | PASS | — | — | 0 hits in 17 files (--require-safe) |
| control | `fixture-B1StringFakeComment` | PASS | — | — | fixture yields 1/1 planted hits |
| control | `fixture-B2IdentifierDashDash` | PASS | — | — | fixture yields 1/1 planted hits |
| control | `fixture-PlantedForbidden` | PASS | — | — | fixture yields 9/9 planted hits |

Summed agda wall time: tool 0.58 s · lib 81.7 s · mustfail 0.17 s · project 91.9 s.

## Project layer, cold (QBP's `_build/` removed first; library interfaces still warm)

Same 17 files, `run.sh --layer project`, 2026-11-20T20:55:31Z → 20:56:56Z, all PASS; summed wall 84.5 s (vs 77.1 s warm). The files that absorb a re-check of their QBP imports: `CDAssocBool` 8.66 s / 450 MiB, `HopfNoAssoc` 6.37 s, `SkyrmionCharge` 9.01 s / 554 MiB, `SubstrateCharge` 10.20 s / **644 MiB** (the run's peak). Nothing else moved by more than 0.1 s. Reading: QBP's own chain is cheap; the cost of a library-dependent check is loading the pinned library's interfaces (~4–5 s, ~300 MiB floor per file). A cold *library* build (no `~/cubical/_build`, what CI does each time) was not measured here — it re-checks the import closure of all 34 modules and is the dominant cost of the CI job.

## How to reproduce

```bash
cd <QBP checkout>
TOOLCHECK_MEM_MB=8000 TOOLCHECK_TIMEOUT=3600 tools/agda-toolcheck/run.sh --update-baseline   # full; rewrites results/results-*.{json,md}
rm -rf proofs/agda/_build proofs/agda-cubical/_build
TOOLCHECK_TAG=cold tools/agda-toolcheck/run.sh --layer project --update-baseline  # cold project layer → results-*-cold.{json,md}
TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 tools/agda-toolcheck/run.sh --layer mustfail   # F2 grading test: must exit 1
```

Resource estimate used for this run (pre-run gate): ≤ 1 GB RSS per file expected from the README figures (SubstrateCharge < 700 MB, QuaternionicHopf < 530 MB), ≤ 6 GB worst case for `SkyrmionCharge` under `--lossy-unification`; disk < 50 MB of interface files; cap 8 GB RSS / 3600 s enforced by boxrun. Observed: 644 MiB peak (cold), 507 MiB (warm full run), 2 min 57 s for the full run.
