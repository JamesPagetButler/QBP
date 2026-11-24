# Lean toolcheck results — leanprover/lean4:v4.30.0 / Mathlib c5ea003

Run 20261124T234344Z · 2026-11-24T23:45:32Z · overall **GREEN** (37/37 as expected)

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |
|---|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 5.39 | 3786 | 58.0→58.8 | 1 thm ⊆ std3 | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.6 | 1847 | 58.9→59.5 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.53 | 1926 | 59.5→59.1 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.35 | 1958 | 59.0→59.4 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.92 | 1971 | 59.4→60.2 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.26 | 1940 | 60.2→60.4 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.71 | 2038 | 60.2→59.9 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 4.45 | 2834 | 59.8→61.4 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 4.01 | 2169 | 61.4→61.2 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 4.31 | 2398 | 61.1→62.2 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.87 | 2976 | 62.5→61.4 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.75 | 2149 | 61.6→61.9 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.46 | 2032 | 61.9→61.5 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 4.34 | 2806 | 61.6→61.4 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.58 | 2962 | 61.4→61.8 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.43 | 1965 | 61.6→61.4 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.79 | 1971 | 61.6→61.6 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 1.34 | 784 | 61.9→62.0 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.22 | 784 | 62.0→61.2 | 3 thm ⊆ std3 | — |
| `tests/T19_NestedComments.lean` | tool | ✅ PASS | 0 | 1.25 | 785 | 61.5→61.4 | 2 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/MF01_Sorry.lean` | must-fail | ✅ PASS | 0 | 1.19 | 784 | 61.6→61.1 | 3 thm; non-std: sorryAx | Lean output: /^\d+:\d+: warning: declaration uses [`']sorry[`']$/; axiom audit: QBPToolcheck.MF01.unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.uses_unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.admitted ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF02_NativeDecide/MF02_NativeDecide.lean` | must-fail | ✅ PASS | 0 | 1.2 | 784 | 61.2→61.0 | 1 thm; non-std: QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.MF02.by_native has non-standard ['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']; checker: /^::error::HARD-BAN violated — native_decide: 1 occurrence/ |
| `must-fail/MF03_VacuousTrue/MF03_VacuousTrue.lean` | must-fail | ✅ PASS | 0 | 1.17 | 784 | 61.1→61.5 | 2 thm ⊆ std3 | checker: /^::error::HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence/; checker: /^::error::RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0/ |
| `must-fail/MF04_FalseDecide/MF04_FalseDecide.lean` | must-fail | ✅ PASS | 1 | 1.2 | 784 | 61.5→61.4 | — | Lean rejected: /^19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false/; Lean rejected: /^22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false/ |
| `must-fail/MF05_CustomAxiom/MF05_CustomAxiom.lean` | must-fail | ✅ PASS | 0 | 1.18 | 784 | 61.5→61.5 | 1 thm; non-std: QBPToolcheck.MF05.cheat | axiom audit: QBPToolcheck.MF05.one_eq_two ⊇ QBPToolcheck.MF05.cheat; axiom audit: QBPToolcheck.MF05.one_eq_two has non-standard ['QBPToolcheck.MF05.cheat']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
| `must-fail/MF06_SpoofedAudit/MF06_SpoofedAudit.lean` | must-fail | ✅ PASS | 0 | 1.2 | 784 | 61.5→61.9 | 1 thm; non-std: sorryAx | axiom audit ignored 3 axiom-like message(s) not positioned at a `#print axioms` command (spoof guard); axiom audit: QBPToolcheck.MF06.spoofed ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF07_SameLineSite/MF07_SameLineSite.lean` | must-fail | ✅ PASS | 0 | 1.19 | 784 | 61.8→61.4 | 2 thm; non-std: QBPToolcheck.MF07.cheat | axiom audit: QBPToolcheck.MF07.dirty ⊇ QBPToolcheck.MF07.cheat; axiom audit: QBPToolcheck.MF07.dirty has non-standard ['QBPToolcheck.MF07.cheat'] |
| `must-fail/MF08_InterpolationLexer/MF08_InterpolationLexer.lean` | must-fail | ✅ PASS | 0 | 1.17 | 784 | 61.5→61.1 | 2 thm; non-std: QBPToolcheck.MF08.cheat | grader REFUSES the file: brace inside a string literal at line(s) [38] — possible interpolation, which the lexer does not model (write a literal brace as \x7B); axiom audit: QBPToolcheck.MF08.dirty ⊇ QBPToolcheck.MF08.cheat |
| `must-fail/MF09_NonAsciiColumn/MF09_NonAsciiColumn.lean` | must-fail | ✅ PASS | 0 | 1.24 | 784 | 61.2→61.9 | 2 thm; non-std: QBPToolcheck.MF09.cheat | axiom audit: QBPToolcheck.MF09.dirty ⊇ QBPToolcheck.MF09.cheat; axiom audit: QBPToolcheck.MF09.dirty has non-standard ['QBPToolcheck.MF09.cheat'] |
| `must-fail/MF10_FormFeedLineDesync/MF10_FormFeedLineDesync.lean` | must-fail | ✅ PASS | 0 | 2.39 | 1444 | 61.9→62.9 | 1 thm; non-std: QBPToolcheck.MF10.cheat | axiom audit ignored 1 axiom-like message(s) not positioned at a `#print axioms` command (spoof guard); axiom audit: QBPToolcheck.MF10.dirty ⊇ QBPToolcheck.MF10.cheat; axiom audit: QBPToolcheck.MF10.dirty has non-standard ['QBPToolcheck.MF10.cheat'] |
| `must-fail/MF11_LoneCRLineDesync/MF11_LoneCRLineDesync.lean` | must-fail | ✅ PASS | 0 | 2.38 | 1444 | 63.0→62.5 | 1 thm; non-std: QBPToolcheck.MF11.cheat | axiom audit ignored 1 axiom-like message(s) not positioned at a `#print axioms` command (spoof guard); axiom audit: QBPToolcheck.MF11.dirty ⊇ QBPToolcheck.MF11.cheat; axiom audit: QBPToolcheck.MF11.dirty has non-standard ['QBPToolcheck.MF11.cheat'] |
| `must-fail/MF12_EscapedQuoteSite/MF12_EscapedQuoteSite.lean` | must-fail | ✅ PASS | 0 | 1.3 | 784 | 62.5→61.5 | 1 thm; non-std: QBPToolcheck.MF12.cheat | axiom audit: QBPToolcheck.MF12.dirty ⊇ QBPToolcheck.MF12.cheat; axiom audit: QBPToolcheck.MF12.dirty has non-standard ['QBPToolcheck.MF12.cheat'] |
| `must-fail/MF13_CleanBraceRefused/MF13_CleanBraceRefused.lean` | must-fail | ✅ PASS | 0 | 1.17 | 784 | 61.8→62.1 | 1 thm ⊆ std3 | grader REFUSES the file: brace inside a string literal at line(s) [19] — possible interpolation, which the lexer does not model (write a literal brace as \x7B) |
| `must-fail/MF14_ExecForgesStdout/MF14_ExecForgesStdout.lean` | must-fail | ✅ PASS | 0 | 1.25 | 784 | 62.2→62.5 | 1 thm ⊆ std3 | file RUNS code during elaboration (l.27 `#eval`) — it could forge or suppress Lean's stdout, so no audit of it is trusted |
| `known-limits/KL01_VacuityBypass/KL01_VacuityBypass.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.19 | 784 | 62.4→62.4 | 2 thm ⊆ std3 | KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.refl_implies_true` is clean ([]); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.alternativity` is clean ([]) |
| `known-limits/KL02_FinFoldlDecide/KL02_FinFoldlDecide.lean` | known-limit | 🟡 KNOWN-LIMIT | 1 | 1.25 | 784 | 62.4→63.2 | — | KNOWN-LIMIT confirmed: Lean still rejects with /(?s)^19:\d+: error: Tactic `decide` failed.*did not reduce to `isTrue` or `isFalse`/ |
| `known-limits/KL03_CheckerStringComment/KL03_CheckerStringComment.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.22 | 784 | 63.6→64.0 | 1 thm; non-std: QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.KL03.hidden_native has non-standard ['QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
