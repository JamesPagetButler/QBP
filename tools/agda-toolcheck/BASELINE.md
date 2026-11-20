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
| Tctl at start | 53.4 °C (full run); 40.2 °C (cold project-layer run) |
| run | `run.sh --layer all`, 2026-11-20T20:49:59Z → 20:52:40Z (2 min 41 s incl. jq/time overhead; summed agda wall 158.6 s) |
| result | **0 unexpected** — 52 PASS · 4 REJECTED · 1 KNOWN-HOLE · 1 control PASS; exit 0 |
| records | `results/results-2.8.0-7b9019b.json` / `.md` (full), `results/results-2.8.0-7b9019b-cold.json` / `.md` (project layer, QBP interfaces removed first) |

Peak RSS over the whole run: **508 MiB** (`SubstrateCharge.agda`, warm) / **644 MiB** (same file, cold). Nothing came near the 8 GB cap.

## Must-fail results (the gate bites)

| control | expected | observed |
|---|---|---|
| `mustfail/Postulate.agda` — top-level `postulate` under `--safe` | reject, `Cannot postulate` | REJECTED (rc 42) |
| `mustfail/Terminating.agda` — `{-# TERMINATING #-}` under `--safe` | reject, `TERMINATING` | REJECTED (rc 42) |
| `mustfail/Hole.agda` — `?` left in | reject, `Unsolved interaction metas` | REJECTED (rc 42) |
| `mustfail/BadPath.agda` — `λ _ → true : true ≡ false` | reject, `UnequalTerms` | REJECTED (rc 42) |
| `mustfail/LetPostulate.agda` — `let postulate p : ⊥ in p` under `--safe` | **known hole on 2.8.0** (agda/agda#8341) | **KNOWN-HOLE: accepted, rc 0** — covered by the `no-forbidden-token` control (0 hits in 17 gated files) |

## Full run (all layers; QBP's own interfaces warm from the preceding run)

| layer | file | status | rc | wall s | max RSS MiB |
|---|---|---|---|---|---|
| tool | `CircleHIT.agda` | PASS | 0 | 0.04 | 44.2 |
| tool | `CoreSyntax.agda` | PASS | 0 | 0.06 | 45.6 |
| tool | `GlueUa.agda` | PASS | 0 | 0.08 | 48.0 |
| tool | `Guardedness.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `HComp.agda` | PASS | 0 | 0.06 | 44.9 |
| tool | `Interval.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `LibFlags.agda` | PASS | 0 | 0.03 | 43.5 |
| tool | `LossyUnification.agda` | PASS | 0 | 0.04 | 44.1 |
| tool | `Opaque.agda` | PASS | 0 | 0.04 | 44.0 |
| tool | `PathP.agda` | PASS | 0 | 0.04 | 44.4 |
| tool | `SuspJoinHIT.agda` | PASS | 0 | 0.05 | 45.5 |
| tool | `Transp.agda` | PASS | 0 | 0.05 | 44.7 |
| lib | `LibConnected.agda` | PASS | 0 | 5.32 | 377.0 |
| lib | `LibDataBoolNat.agda` | PASS | 0 | 2.05 | 164.2 |
| lib | `LibDataInt.agda` | PASS | 0 | 3.32 | 236.2 |
| lib | `LibDataSigma.agda` | PASS | 0 | 0.79 | 92.5 |
| lib | `LibEquivIso.agda` | PASS | 0 | 0.33 | 67.0 |
| lib | `LibFunction.agda` | PASS | 0 | 0.17 | 55.3 |
| lib | `LibGroupBase.agda` | PASS | 0 | 5.78 | 369.1 |
| lib | `LibHLevelsGroupoid.agda` | PASS | 0 | 1.12 | 115.3 |
| lib | `LibHopf.agda` | PASS | 0 | 5.57 | 372.8 |
| lib | `LibHSpace.agda` | PASS | 0 | 5.44 | 379.5 |
| lib | `LibJoin.agda` | PASS | 0 | 4.53 | 325.2 |
| lib | `LibLoopspace.agda` | PASS | 0 | 4.09 | 283.0 |
| lib | `LibPinSn.agda` | PASS | 0 | 7.54 | 465.3 |
| lib | `LibPointed.agda` | PASS | 0 | 1.36 | 130.2 |
| lib | `LibPrelude.agda` | PASS | 0 | 0.23 | 56.7 |
| lib | `LibS1.agda` | PASS | 0 | 3.50 | 253.6 |
| lib | `LibSn.agda` | PASS | 0 | 5.43 | 376.6 |
| lib | `LibSnDegree.agda` | PASS | 0 | 7.57 | 464.7 |
| lib | `LibSnMultiplication.agda` | PASS | 0 | 5.58 | 378.3 |
| lib | `LibSusp.agda` | PASS | 0 | 4.70 | 337.9 |
| lib | `LibTruncations.agda` | PASS | 0 | 4.30 | 294.1 |
| lib | `LibUnivalence.agda` | PASS | 0 | 2.04 | 168.8 |
| mustfail | `BadPath.agda` | REJECTED | 42 | 0.04 | 44.4 |
| mustfail | `Hole.agda` | REJECTED | 42 | 0.04 | 44.6 |
| mustfail | `LetPostulate.agda` | KNOWN-HOLE | 0 | 0.03 | 43.6 |
| mustfail | `Postulate.agda` | REJECTED | 42 | 0.03 | 44.1 |
| mustfail | `Terminating.agda` | REJECTED | 42 | 0.03 | 43.8 |
| substrate | `QBPHSpace.agda` | PASS | 0 | 0.04 | 44.0 |
| substrate | `QBPJoin.agda` | PASS | 0 | 0.05 | 45.2 |
| substrate | `QBPSpheres.agda` | PASS | 0 | 0.04 | 44.5 |
| substrate | `QBPSubstrate.agda` | PASS | 0 | 0.04 | 44.2 |
| cubical | `AssocTransport.agda` | PASS | 0 | 5.59 | 394.1 |
| cubical | `CDAssocBool.agda` | PASS | 0 | 5.56 | 395.6 |
| cubical | `CDAssocCubesStatus.agda` | PASS | 0 | 5.82 | 401.1 |
| cubical | `CDAssocReduction.agda` | PASS | 0 | 5.62 | 372.9 |
| cubical | `CDJoinBR.agda` | PASS | 0 | 5.49 | 381.9 |
| cubical | `CDLawsBool.agda` | PASS | 0 | 5.48 | 379.7 |
| cubical | `Diamond.agda` | PASS | 0 | 4.55 | 293.1 |
| cubical | `HopfNoAssoc.agda` | PASS | 0 | 5.51 | 362.0 |
| cubical | `QBPS3HSpace.agda` | PASS | 0 | 5.59 | 380.8 |
| cubical | `QuaternionicHopf.agda` | PASS | 0 | 6.06 | 401.8 |
| cubical | `S3FromCD.agda` | PASS | 0 | 5.72 | 413.7 |
| cubical | `SkyrmionCharge.agda` | PASS | 0 | 7.93 | 503.5 |
| cubical | `SubstrateCharge.agda` | PASS | 0 | 7.96 | 507.4 |
| control | `no-forbidden-token` | PASS | — | — | 0 hits in 17 files |

Summed agda wall time: tool 0.57 s · lib 76.9 s · mustfail 0.17 s · project 77.1 s.

## Project layer, cold (QBP's `_build/` removed first; library interfaces still warm)

Same 17 files, `run.sh --layer project`, 2026-11-20T20:55:31Z → 20:56:56Z, all PASS; summed wall 84.5 s (vs 77.1 s warm). The files that absorb a re-check of their QBP imports: `CDAssocBool` 8.66 s / 450 MiB, `HopfNoAssoc` 6.37 s, `SkyrmionCharge` 9.01 s / 554 MiB, `SubstrateCharge` 10.20 s / **644 MiB** (the run's peak). Nothing else moved by more than 0.1 s. Reading: QBP's own chain is cheap; the cost of a library-dependent check is loading the pinned library's interfaces (~4–5 s, ~300 MiB floor per file). A cold *library* build (no `~/cubical/_build`, what CI does each time) was not measured here — it re-checks the import closure of all 34 modules and is the dominant cost of the CI job.

## How to reproduce

```bash
cd <QBP checkout>
TOOLCHECK_MEM_MB=8000 TOOLCHECK_TIMEOUT=3600 tools/agda-toolcheck/run.sh          # full
rm -rf proofs/agda/_build proofs/agda-cubical/_build
TOOLCHECK_TAG=cold tools/agda-toolcheck/run.sh --layer project                    # cold project layer
```

Resource estimate used for this run (pre-run gate): ≤ 1 GB RSS per file expected from the README figures (SubstrateCharge < 700 MB, QuaternionicHopf < 530 MB), ≤ 6 GB worst case for `SkyrmionCharge` under `--lossy-unification`; disk < 50 MB of interface files; cap 8 GB RSS / 3600 s enforced by boxrun. Observed: 644 MiB peak, 2 min 41 s.
