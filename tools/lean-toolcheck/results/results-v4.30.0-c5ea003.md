# Lean toolcheck results — leanprover/lean4:v4.30.0 / Mathlib c5ea003

Run 20261120T223723Z · 2026-11-20T22:38:50Z · overall **GREEN** (29/29 as expected)

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |
|---|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 5.22 | 3763 | 60.6→60.4 | 1 thm ⊆ std3 | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.52 | 1827 | 60.2→59.8 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.35 | 1906 | 59.6→59.2 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.35 | 1937 | 59.4→61.0 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.81 | 1949 | 60.9→61.5 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.3 | 1922 | 61.4→60.0 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.67 | 2017 | 60.1→60.8 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.44 | 2810 | 60.8→60.9 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 4.15 | 2149 | 61.0→61.0 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 4.16 | 2378 | 61.1→60.6 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.71 | 2951 | 60.8→61.9 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.68 | 2127 | 61.9→61.4 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.28 | 2010 | 61.4→60.5 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 4.14 | 2783 | 60.5→61.1 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.42 | 2938 | 61.1→61.4 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.16 | 1943 | 61.2→61.1 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.56 | 1950 | 61.1→61.4 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.26 | 774 | 61.5→60.4 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.15 | 774 | 60.6→60.0 | 3 thm ⊆ std3 | — |
| `tests/T19_NestedComments.lean` | tool | ✅ PASS | 0 | 1.14 | 774 | 60.2→60.0 | 2 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/MF01_Sorry.lean` | must-fail | ✅ PASS | 0 | 1.17 | 774 | 60.2→60.5 | 3 thm; non-std: sorryAx | Lean output: /^\d+:\d+: warning: declaration uses [`']sorry[`']$/; axiom audit: QBPToolcheck.MF01.unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.uses_unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.admitted ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF02_NativeDecide/MF02_NativeDecide.lean` | must-fail | ✅ PASS | 0 | 1.14 | 774 | 60.5→60.9 | 1 thm; non-std: QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.MF02.by_native has non-standard ['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']; checker: /^::error::HARD-BAN violated — native_decide: 1 occurrence/ |
| `must-fail/MF03_VacuousTrue/MF03_VacuousTrue.lean` | must-fail | ✅ PASS | 0 | 1.12 | 774 | 60.9→60.5 | 2 thm ⊆ std3 | checker: /^::error::HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence/; checker: /^::error::RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0/ |
| `must-fail/MF04_FalseDecide/MF04_FalseDecide.lean` | must-fail | ✅ PASS | 1 | 1.13 | 774 | 60.6→60.9 | — | Lean rejected: /^19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false/; Lean rejected: /^22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false/ |
| `must-fail/MF05_CustomAxiom/MF05_CustomAxiom.lean` | must-fail | ✅ PASS | 0 | 1.15 | 774 | 61.0→60.6 | 1 thm; non-std: QBPToolcheck.MF05.cheat | axiom audit: QBPToolcheck.MF05.one_eq_two ⊇ QBPToolcheck.MF05.cheat; axiom audit: QBPToolcheck.MF05.one_eq_two has non-standard ['QBPToolcheck.MF05.cheat']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
| `must-fail/MF06_SpoofedAudit/MF06_SpoofedAudit.lean` | must-fail | ✅ PASS | 0 | 1.16 | 774 | 60.6→60.9 | 1 thm; non-std: sorryAx | axiom audit ignored 3 axiom-like message(s) not positioned at a `#print axioms` command (spoof guard); axiom audit: QBPToolcheck.MF06.spoofed ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `known-limits/KL01_VacuityBypass/KL01_VacuityBypass.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.13 | 774 | 60.9→61.0 | 2 thm ⊆ std3 | KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.refl_implies_true` is clean ([]); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.alternativity` is clean ([]) |
| `known-limits/KL02_FinFoldlDecide/KL02_FinFoldlDecide.lean` | known-limit | 🟡 KNOWN-LIMIT | 1 | 1.14 | 774 | 61.0→60.9 | — | KNOWN-LIMIT confirmed: Lean still rejects with /(?s)^19:\d+: error: Tactic `decide` failed.*did not reduce to `isTrue` or `isFalse`/ |
| `known-limits/KL03_CheckerStringComment/KL03_CheckerStringComment.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.14 | 774 | 61.0→61.1 | 1 thm; non-std: QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.KL03.hidden_native has non-standard ['QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
