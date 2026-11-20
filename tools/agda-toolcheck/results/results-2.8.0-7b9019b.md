# agda-toolcheck results — Agda 2.8.0, agda/cubical 7b9019b

Run 20261120T224439Z: 2026-11-20T22:44:39Z → 2026-11-20T22:48:52Z · Tctl at start 63.6 C · layer all · unexpected 0

| layer | file | status | rc | wall s | max RSS MiB | detail |
|---|---|---|---|---|---|---|
| control | `manifest-tool` | PASS | 0 | 0 | 0 | 12 found, 12 listed |
| tool | `CircleHIT.agda` | PASS | 0 | 0.04 | 44.3 |  |
| tool | `CoreSyntax.agda` | PASS | 0 | 0.07 | 45.7 |  |
| tool | `GlueUa.agda` | PASS | 0 | 0.11 | 48.1 |  |
| tool | `Guardedness.agda` | PASS | 0 | 0.05 | 44.3 |  |
| tool | `HComp.agda` | PASS | 0 | 0.06 | 44.9 |  |
| tool | `Interval.agda` | PASS | 0 | 0.04 | 44.2 |  |
| tool | `LibFlags.agda` | PASS | 0 | 0.03 | 43.6 |  |
| tool | `LossyUnification.agda` | PASS | 0 | 0.04 | 44.2 |  |
| tool | `Opaque.agda` | PASS | 0 | 0.05 | 44.1 |  |
| tool | `PathP.agda` | PASS | 0 | 0.05 | 44.4 |  |
| tool | `SuspJoinHIT.agda` | PASS | 0 | 0.05 | 45.6 |  |
| tool | `Transp.agda` | PASS | 0 | 0.05 | 44.8 |  |
| control | `manifest-lib` | PASS | 0 | 0 | 0 | 22 found, 22 listed |
| lib | `LibConnected.agda` | PASS | 0 | 5.54 | 378.8 |  |
| lib | `LibDataBoolNat.agda` | PASS | 0 | 2.1 | 170.3 |  |
| lib | `LibDataInt.agda` | PASS | 0 | 3.49 | 234.5 |  |
| lib | `LibDataSigma.agda` | PASS | 0 | 0.81 | 93.4 |  |
| lib | `LibEquivIso.agda` | PASS | 0 | 0.33 | 67.2 |  |
| lib | `LibFunction.agda` | PASS | 0 | 0.17 | 55.3 |  |
| lib | `LibGroupBase.agda` | PASS | 0 | 5.83 | 399.1 |  |
| lib | `LibHLevelsGroupoid.agda` | PASS | 0 | 1.14 | 116.3 |  |
| lib | `LibHopf.agda` | PASS | 0 | 5.74 | 374.9 |  |
| lib | `LibHSpace.agda` | PASS | 0 | 5.6 | 379.9 |  |
| lib | `LibJoin.agda` | PASS | 0 | 4.74 | 329.8 |  |
| lib | `LibLoopspace.agda` | PASS | 0 | 4.16 | 295.9 |  |
| lib | `LibPinSn.agda` | PASS | 0 | 7.7 | 493 |  |
| lib | `LibPointed.agda` | PASS | 0 | 1.36 | 124 |  |
| lib | `LibPrelude.agda` | PASS | 0 | 0.15 | 56.1 |  |
| lib | `LibS1.agda` | PASS | 0 | 3.56 | 250.7 |  |
| lib | `LibSn.agda` | PASS | 0 | 5.54 | 376.6 |  |
| lib | `LibSnDegree.agda` | PASS | 0 | 7.8 | 473.3 |  |
| lib | `LibSnMultiplication.agda` | PASS | 0 | 5.66 | 371.6 |  |
| lib | `LibSusp.agda` | PASS | 0 | 4.75 | 335.7 |  |
| lib | `LibTruncations.agda` | PASS | 0 | 4.41 | 302.6 |  |
| lib | `LibUnivalence.agda` | PASS | 0 | 2.09 | 172 |  |
| control | `manifest-mustfail` | PASS | 0 | 0 | 0 | 5 found, 5 listed |
| mustfail | `BadPath.agda` | REJECTED | 42 | 0.04 | 44.5 |  |
| mustfail | `Hole.agda` | REJECTED | 42 | 0.04 | 44.6 |  |
| mustfail | `LetPostulate.agda` | KNOWN-HOLE | 0 | 0.03 | 43.6 | accepted on Agda 2.8.0 < 2.9.0 (agda/agda#8341) |
| mustfail | `Postulate.agda` | REJECTED | 42 | 0.03 | 44.2 |  |
| mustfail | `Terminating.agda` | REJECTED | 42 | 0.03 | 43.9 |  |
| control | `manifest-substrate` | PASS | 0 | 0 | 0 | 4 found, 4 listed |
| substrate | `QBPHSpace.agda` | PASS | 0 | 0.04 | 44.1 |  |
| substrate | `QBPJoin.agda` | PASS | 0 | 0.05 | 45.3 |  |
| substrate | `QBPSpheres.agda` | PASS | 0 | 0.04 | 44.6 |  |
| substrate | `QBPSubstrate.agda` | PASS | 0 | 0.04 | 44.3 |  |
| control | `manifest-cubical` | PASS | 0 | 0 | 0 | 13 found, 13 listed |
| cubical | `AssocTransport.agda` | PASS | 0 | 5.78 | 394.2 |  |
| cubical | `CDAssocBool.agda` | PASS | 0 | 25.26 | 395.9 |  |
| cubical | `CDAssocCubesStatus.agda` | PASS | 0 | 5.95 | 401.2 |  |
| cubical | `CDAssocReduction.agda` | PASS | 0 | 5.75 | 373 |  |
| cubical | `CDJoinBR.agda` | PASS | 0 | 5.66 | 381.9 |  |
| cubical | `CDLawsBool.agda` | PASS | 0 | 5.68 | 379.8 |  |
| cubical | `Diamond.agda` | PASS | 0 | 4.66 | 293.2 |  |
| cubical | `HopfNoAssoc.agda` | PASS | 0 | 5.69 | 362.1 |  |
| cubical | `QBPS3HSpace.agda` | PASS | 0 | 5.87 | 380.8 |  |
| cubical | `QuaternionicHopf.agda` | PASS | 0 | 6.06 | 401.9 |  |
| cubical | `S3FromCD.agda` | PASS | 0 | 72.9 | 413.8 |  |
| cubical | `SkyrmionCharge.agda` | PASS | 0 | 8.06 | 503.7 |  |
| cubical | `SubstrateCharge.agda` | PASS | 0 | 8.09 | 507.5 |  |
| control | `no-nested-source` | PASS | 0 | 0 | 0 | no .agda/.lagda* source below the top level of proofs/agda or proofs/agda-cubical |
| control | `forbidden-tokens` | PASS | 0 | 0 | 0 | 0 hits over proofs/agda + proofs/agda-cubical (--require-safe; scripts/agda_forbidden_tokens.py) |
| control | `manifest-control` | PASS | 0 | 0 | 0 | 3 found, 3 listed |
| control | `fixture-B1StringFakeComment` | PASS | 0 | 0 | 0 | fixture yields 1/1 planted hits |
| control | `fixture-B2IdentifierDashDash` | PASS | 0 | 0 | 0 | fixture yields 1/1 planted hits |
| control | `fixture-PlantedForbidden` | PASS | 0 | 0 | 0 | fixture yields 9/9 planted hits |
