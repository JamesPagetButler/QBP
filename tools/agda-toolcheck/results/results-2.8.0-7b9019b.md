# agda-toolcheck results — Agda 2.8.0, agda/cubical 7b9019b

Run 20261120T225839Z: 2026-11-20T22:58:39Z → 2026-11-20T23:01:23Z · Tctl at start 57.4 C · layer all · unexpected 0

| layer | file | status | rc | wall s | max RSS MiB | detail |
|---|---|---|---|---|---|---|
| control | `manifest-tool` | PASS | 0 | 0 | 0 | 12 found, 12 listed |
| tool | `CircleHIT.agda` | PASS | 0 | 0.04 | 45.5 |  |
| tool | `CoreSyntax.agda` | PASS | 0 | 0.06 | 46.8 |  |
| tool | `GlueUa.agda` | PASS | 0 | 0.08 | 49.3 |  |
| tool | `Guardedness.agda` | PASS | 0 | 0.04 | 45.3 |  |
| tool | `HComp.agda` | PASS | 0 | 0.06 | 46.1 |  |
| tool | `Interval.agda` | PASS | 0 | 0.04 | 45.4 |  |
| tool | `LibFlags.agda` | PASS | 0 | 0.03 | 44.7 |  |
| tool | `LossyUnification.agda` | PASS | 0 | 0.04 | 45.4 |  |
| tool | `Opaque.agda` | PASS | 0 | 0.04 | 45.2 |  |
| tool | `PathP.agda` | PASS | 0 | 0.04 | 45.6 |  |
| tool | `SuspJoinHIT.agda` | PASS | 0 | 0.05 | 46.8 |  |
| tool | `Transp.agda` | PASS | 0 | 0.05 | 46 |  |
| control | `manifest-lib` | PASS | 0 | 0 | 0 | 22 found, 22 listed |
| lib | `LibConnected.agda` | PASS | 0 | 5.31 | 380.2 |  |
| lib | `LibDataBoolNat.agda` | PASS | 0 | 2.05 | 171.6 |  |
| lib | `LibDataInt.agda` | PASS | 0 | 3.33 | 235.7 |  |
| lib | `LibDataSigma.agda` | PASS | 0 | 0.8 | 94.7 |  |
| lib | `LibEquivIso.agda` | PASS | 0 | 0.33 | 68.4 |  |
| lib | `LibFunction.agda` | PASS | 0 | 0.16 | 56.5 |  |
| lib | `LibGroupBase.agda` | PASS | 0 | 5.76 | 400.4 |  |
| lib | `LibHLevelsGroupoid.agda` | PASS | 0 | 1.15 | 117.5 |  |
| lib | `LibHopf.agda` | PASS | 0 | 5.69 | 376.1 |  |
| lib | `LibHSpace.agda` | PASS | 0 | 5.62 | 381.3 |  |
| lib | `LibJoin.agda` | PASS | 0 | 4.75 | 331 |  |
| lib | `LibLoopspace.agda` | PASS | 0 | 4.13 | 297.1 |  |
| lib | `LibPinSn.agda` | PASS | 0 | 7.52 | 494.4 |  |
| lib | `LibPointed.agda` | PASS | 0 | 1.35 | 125.3 |  |
| lib | `LibPrelude.agda` | PASS | 0 | 0.14 | 57.3 |  |
| lib | `LibS1.agda` | PASS | 0 | 3.47 | 251.9 |  |
| lib | `LibSn.agda` | PASS | 0 | 5.42 | 377.9 |  |
| lib | `LibSnDegree.agda` | PASS | 0 | 7.56 | 474.6 |  |
| lib | `LibSnMultiplication.agda` | PASS | 0 | 5.64 | 373 |  |
| lib | `LibSusp.agda` | PASS | 0 | 4.68 | 336.9 |  |
| lib | `LibTruncations.agda` | PASS | 0 | 4.31 | 303.8 |  |
| lib | `LibUnivalence.agda` | PASS | 0 | 2.05 | 173.2 |  |
| control | `manifest-mustfail` | PASS | 0 | 0 | 0 | 5 found, 5 listed |
| mustfail | `BadPath.agda` | REJECTED | 42 | 0.04 | 45.8 |  |
| mustfail | `Hole.agda` | REJECTED | 42 | 0.04 | 45.9 |  |
| mustfail | `LetPostulate.agda` | KNOWN-HOLE | 0 | 0.03 | 44.9 | accepted on Agda 2.8.0 < 2.9.0 (agda/agda#8341) |
| mustfail | `Postulate.agda` | REJECTED | 42 | 0.03 | 45.5 |  |
| mustfail | `Terminating.agda` | REJECTED | 42 | 0.03 | 45.1 |  |
| control | `manifest-substrate` | PASS | 0 | 0 | 0 | 4 found, 4 listed |
| substrate | `QBPHSpace.agda` | PASS | 0 | 0.04 | 45.3 |  |
| substrate | `QBPJoin.agda` | PASS | 0 | 0.05 | 46.5 |  |
| substrate | `QBPSpheres.agda` | PASS | 0 | 0.04 | 45.8 |  |
| substrate | `QBPSubstrate.agda` | PASS | 0 | 0.04 | 45.5 |  |
| control | `manifest-cubical` | PASS | 0 | 0 | 0 | 13 found, 13 listed |
| cubical | `AssocTransport.agda` | PASS | 0 | 5.67 | 395.7 |  |
| cubical | `CDAssocBool.agda` | PASS | 0 | 5.82 | 397 |  |
| cubical | `CDAssocCubesStatus.agda` | PASS | 0 | 6.03 | 402.5 |  |
| cubical | `CDAssocReduction.agda` | PASS | 0 | 5.69 | 374.3 |  |
| cubical | `CDJoinBR.agda` | PASS | 0 | 5.51 | 383.2 |  |
| cubical | `CDLawsBool.agda` | PASS | 0 | 5.49 | 381.1 |  |
| cubical | `Diamond.agda` | PASS | 0 | 4.53 | 294.5 |  |
| cubical | `HopfNoAssoc.agda` | PASS | 0 | 5.5 | 363.4 |  |
| cubical | `QBPS3HSpace.agda` | PASS | 0 | 5.65 | 382.1 |  |
| cubical | `QuaternionicHopf.agda` | PASS | 0 | 6.04 | 403.2 |  |
| cubical | `S3FromCD.agda` | PASS | 0 | 5.72 | 415.1 |  |
| cubical | `SkyrmionCharge.agda` | PASS | 0 | 7.91 | 504.9 |  |
| cubical | `SubstrateCharge.agda` | PASS | 0 | 7.98 | 508.8 |  |
| control | `no-nested-source` | PASS | 0 | 0 | 0 | no .agda/.lagda* source below the top level of proofs/agda or proofs/agda-cubical |
| control | `forbidden-tokens` | PASS | 0 | 0 | 0 | 0 hits over proofs/agda + proofs/agda-cubical (--require-safe; scripts/agda_forbidden_tokens.py) |
| control | `manifest-control` | PASS | 0 | 0 | 0 | 3 found, 3 listed |
| control | `fixture-B1StringFakeComment` | PASS | 0 | 0 | 0 | fixture yields 1/1 planted hits |
| control | `fixture-B2IdentifierDashDash` | PASS | 0 | 0 | 0 | fixture yields 1/1 planted hits |
| control | `fixture-PlantedForbidden` | PASS | 0 | 0 | 0 | fixture yields 9/9 planted hits |
