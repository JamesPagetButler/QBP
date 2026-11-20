# Lean toolcheck results — leanprover/lean4:v4.30.0 / Mathlib c5ea003

Run 20261120T210059Z · 2026-11-20T21:02:13Z · overall **GREEN** (22/22 as expected)

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |
|---|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 4.99 | 3762 | 47.0→45.9 | 1 thm ⊆ std3 | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.36 | 1839 | 45.9→48.4 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.14 | 1910 | 48.4→47.6 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.15 | 1940 | 47.6→48.8 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.58 | 1952 | 48.8→49.4 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.01 | 1925 | 49.6→49.2 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.61 | 2018 | 49.0→51.4 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.13 | 2817 | 51.8→55.9 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.71 | 2149 | 55.6→51.9 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 3.9 | 2380 | 52.0→53.9 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.6 | 2958 | 54.1→54.0 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.47 | 2129 | 54.0→54.8 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.11 | 2011 | 55.0→56.5 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 4.06 | 2789 | 56.8→56.1 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.26 | 2944 | 56.1→57.1 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.06 | 1944 | 57.5→56.5 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.49 | 1951 | 56.5→56.8 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.25 | 774 | 56.6→56.6 | 1 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/MF01_Sorry.lean` | must-fail | ✅ PASS | 0 | 1.13 | 774 | 56.9→56.6 | 2 thm; non-std: sorryAx | Lean output: /warning: declaration uses [`']sorry[`']/; axiom audit: QBPToolcheck.MF01.unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.uses_unproved ⊇ sorryAx; checker: /RATCHET violated — sorry: 1 > baseline 0/ |
| `must-fail/MF02_NativeDecide/MF02_NativeDecide.lean` | must-fail | ✅ PASS | 0 | 1.14 | 774 | 56.4→55.5 | 1 thm; non-std: QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.MF02.by_native has non-standard ['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']; checker: /HARD-BAN violated — native_decide: 1 occurrence/ |
| `must-fail/MF03_VacuousTrue/MF03_VacuousTrue.lean` | must-fail | ✅ PASS | 0 | 1.14 | 774 | 55.5→55.9 | 2 thm ⊆ std3 | checker: /HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence/; checker: /RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0/ |
| `must-fail/MF04_FalseDecide/MF04_FalseDecide.lean` | must-fail | ✅ PASS | 1 | 1.12 | 774 | 55.9→55.5 | — | Lean rejected: /:19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false/; Lean rejected: /:22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false/ |
