# Lean toolcheck results — leanprover/lean4:v4.30.0 / Mathlib c5ea003

Run 20261120T212158Z · 2026-11-20T21:26:00Z · overall **GREEN** (26/26 as expected)

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |
|---|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 5.04 | 3761 | 58.1→59.6 | 1 thm ⊆ std3 | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.44 | 1827 | 59.8→60.4 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.35 | 1904 | 60.4→59.6 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.3 | 1935 | 59.6→60.0 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.78 | 1948 | 60.0→59.5 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.14 | 1918 | 59.6→59.9 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.56 | 2015 | 59.8→59.9 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.22 | 2807 | 59.9→60.4 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.9 | 2147 | 60.2→61.1 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 4.02 | 2376 | 61.2→60.5 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.56 | 2950 | 60.4→60.2 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.61 | 2125 | 60.1→60.1 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.26 | 2008 | 60.2→59.5 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 4.11 | 2780 | 59.6→60.1 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.42 | 2936 | 59.9→60.6 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.25 | 1940 | 60.5→59.5 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.72 | 1947 | 59.5→60.9 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.27 | 774 | 60.9→60.2 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.19 | 774 | 60.2→59.9 | 3 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/MF01_Sorry.lean` | must-fail | ✅ PASS | 0 | 1.15 | 774 | 60.0→59.6 | 3 thm; non-std: sorryAx | Lean output: /warning: declaration uses [`']sorry[`']/; axiom audit: QBPToolcheck.MF01.unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.uses_unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.admitted ⊇ sorryAx; checker: /RATCHET violated — sorry: 1 > baseline 0/ |
| `must-fail/MF02_NativeDecide/MF02_NativeDecide.lean` | must-fail | ✅ PASS | 0 | 1.14 | 774 | 59.6→59.5 | 1 thm; non-std: QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.MF02.by_native has non-standard ['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']; checker: /HARD-BAN violated — native_decide: 1 occurrence/ |
| `must-fail/MF03_VacuousTrue/MF03_VacuousTrue.lean` | must-fail | ✅ PASS | 0 | 1.14 | 774 | 59.5→59.6 | 2 thm ⊆ std3 | checker: /HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence/; checker: /RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0/ |
| `must-fail/MF04_FalseDecide/MF04_FalseDecide.lean` | must-fail | ✅ PASS | 1 | 1.14 | 774 | 59.8→60.0 | — | Lean rejected: /:19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false/; Lean rejected: /:22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false/ |
| `must-fail/MF05_CustomAxiom/MF05_CustomAxiom.lean` | must-fail | ✅ PASS | 0 | 1.13 | 774 | 60.0→60.0 | 1 thm; non-std: QBPToolcheck.MF05.cheat | axiom audit: QBPToolcheck.MF05.one_eq_two ⊇ QBPToolcheck.MF05.cheat; axiom audit: QBPToolcheck.MF05.one_eq_two has non-standard ['QBPToolcheck.MF05.cheat']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
| `known-limits/KL01_VacuityBypass/KL01_VacuityBypass.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.17 | 774 | 60.0→60.1 | 2 thm ⊆ std3 | KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.refl_implies_true` is clean ([]); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.alternativity` is clean ([]) |
| `known-limits/KL02_FinFoldlDecide/KL02_FinFoldlDecide.lean` | known-limit | 🟡 KNOWN-LIMIT | 1 | 1.17 | 774 | 60.1→59.6 | — | KNOWN-LIMIT confirmed: Lean still rejects with /did not reduce to `isTrue` or `isFalse`/ |
