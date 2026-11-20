# Lean toolcheck results — leanprover/lean4:v4.30.0 / Mathlib c5ea003

Run 20261120T230310Z · 2026-11-20T23:05:11Z · overall **GREEN** (31/31 as expected)

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |
|---|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 4.91 | 3766 | 59.0→57.1 | 1 thm ⊆ std3 | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.26 | 1840 | 57.0→58.4 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.12 | 1921 | 58.4→59.1 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.12 | 1946 | 59.2→58.1 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.6 | 1956 | 58.2→59.2 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.04 | 1934 | 59.2→59.4 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.42 | 2027 | 59.6→58.8 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.13 | 2816 | 58.6→60.0 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.8 | 2151 | 60.0→58.6 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 3.85 | 2380 | 58.8→59.0 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.46 | 2959 | 59.1→59.6 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.39 | 2128 | 59.8→59.5 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.13 | 2023 | 59.6→58.5 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 3.99 | 2789 | 58.5→59.0 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.29 | 2946 | 59.0→59.5 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.05 | 1951 | 59.4→59.5 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.46 | 1958 | 59.5→59.5 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.3 | 774 | 59.6→59.6 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.17 | 774 | 59.5→58.9 | 3 thm ⊆ std3 | — |
| `tests/T19_NestedComments.lean` | tool | ✅ PASS | 0 | 1.14 | 774 | 58.9→59.8 | 2 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/MF01_Sorry.lean` | must-fail | ✅ PASS | 0 | 1.15 | 774 | 59.8→58.9 | 3 thm; non-std: sorryAx | Lean output: /^\d+:\d+: warning: declaration uses [`']sorry[`']$/; axiom audit: QBPToolcheck.MF01.unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.uses_unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.admitted ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF02_NativeDecide/MF02_NativeDecide.lean` | must-fail | ✅ PASS | 0 | 1.13 | 774 | 58.9→58.9 | 1 thm; non-std: QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.MF02.by_native has non-standard ['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']; checker: /^::error::HARD-BAN violated — native_decide: 1 occurrence/ |
| `must-fail/MF03_VacuousTrue/MF03_VacuousTrue.lean` | must-fail | ✅ PASS | 0 | 1.15 | 774 | 58.9→58.8 | 2 thm ⊆ std3 | checker: /^::error::HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence/; checker: /^::error::RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0/ |
| `must-fail/MF04_FalseDecide/MF04_FalseDecide.lean` | must-fail | ✅ PASS | 1 | 1.16 | 774 | 58.9→58.9 | — | Lean rejected: /^19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false/; Lean rejected: /^22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false/ |
| `must-fail/MF05_CustomAxiom/MF05_CustomAxiom.lean` | must-fail | ✅ PASS | 0 | 1.13 | 774 | 59.1→58.6 | 1 thm; non-std: QBPToolcheck.MF05.cheat | axiom audit: QBPToolcheck.MF05.one_eq_two ⊇ QBPToolcheck.MF05.cheat; axiom audit: QBPToolcheck.MF05.one_eq_two has non-standard ['QBPToolcheck.MF05.cheat']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
| `must-fail/MF06_SpoofedAudit/MF06_SpoofedAudit.lean` | must-fail | ✅ PASS | 0 | 1.17 | 774 | 58.9→58.2 | 1 thm; non-std: sorryAx | axiom audit ignored 3 axiom-like message(s) not positioned at a `#print axioms` command (spoof guard); axiom audit: QBPToolcheck.MF06.spoofed ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF07_SameLineSite/MF07_SameLineSite.lean` | must-fail | ✅ PASS | 0 | 1.15 | 774 | 58.5→58.4 | 2 thm; non-std: QBPToolcheck.MF07.cheat | axiom audit: QBPToolcheck.MF07.dirty ⊇ QBPToolcheck.MF07.cheat; axiom audit: QBPToolcheck.MF07.dirty has non-standard ['QBPToolcheck.MF07.cheat'] |
| `must-fail/MF08_InterpolationLexer/MF08_InterpolationLexer.lean` | must-fail | ✅ PASS | 0 | 1.2 | 774 | 58.4→58.8 | 2 thm; non-std: QBPToolcheck.MF08.cheat | grader REFUSES the file: brace inside a string literal at line(s) [38] — possible interpolation, which the lexer does not model (write a literal brace as \x7B); axiom audit: QBPToolcheck.MF08.dirty ⊇ QBPToolcheck.MF08.cheat |
| `known-limits/KL01_VacuityBypass/KL01_VacuityBypass.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.16 | 774 | 59.0→59.2 | 2 thm ⊆ std3 | KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.refl_implies_true` is clean ([]); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.alternativity` is clean ([]) |
| `known-limits/KL02_FinFoldlDecide/KL02_FinFoldlDecide.lean` | known-limit | 🟡 KNOWN-LIMIT | 1 | 1.17 | 774 | 59.2→59.1 | — | KNOWN-LIMIT confirmed: Lean still rejects with /(?s)^19:\d+: error: Tactic `decide` failed.*did not reduce to `isTrue` or `isFalse`/ |
| `known-limits/KL03_CheckerStringComment/KL03_CheckerStringComment.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.15 | 774 | 59.2→59.2 | 1 thm; non-std: QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.KL03.hidden_native has non-standard ['QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
