# Lean toolcheck results — leanprover/lean4:v4.30.0 / Mathlib c5ea003

Run 20261121T021507Z · 2026-11-21T02:16:49Z · overall **GREEN** (32/32 as expected)

| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |
|---|---|---|---|---|---|---|---|---|
| `tests/T00_ImportSurface.lean` | tool | ✅ PASS | 0 | 4.54 | 3796 | 57.9→57.9 | 1 thm ⊆ std3 | — |
| `tests/T01_DecideFin.lean` | tool | ✅ PASS | 0 | 3.17 | 1843 | 57.8→57.4 | 5 thm ⊆ std3 | — |
| `tests/T02_DecidableInstances.lean` | tool | ✅ PASS | 0 | 3.12 | 1926 | 57.5→57.5 | 4 thm ⊆ std3 | — |
| `tests/T03_FinCases.lean` | tool | ✅ PASS | 0 | 3.12 | 1952 | 57.5→59.0 | 3 thm ⊆ std3 | — |
| `tests/T04_Ring.lean` | tool | ✅ PASS | 0 | 3.71 | 1967 | 58.8→59.2 | 5 thm ⊆ std3 | — |
| `tests/T05_FieldSimp.lean` | tool | ✅ PASS | 0 | 3.04 | 1936 | 59.1→58.8 | 3 thm ⊆ std3 | — |
| `tests/T06_LinarithPositivity.lean` | tool | ✅ PASS | 0 | 3.4 | 2042 | 58.8→59.5 | 5 thm ⊆ std3 | — |
| `tests/T07_NormNumCasts.lean` | tool | ✅ PASS | 0 | 3.96 | 2844 | 59.6→59.0 | 6 thm ⊆ std3 | — |
| `tests/T08_ModuleLinComb.lean` | tool | ✅ PASS | 0 | 3.69 | 2166 | 59.2→59.5 | 5 thm ⊆ std3 | — |
| `tests/T09_SimpFamily.lean` | tool | ✅ PASS | 0 | 3.8 | 2402 | 59.6→58.6 | 9 thm ⊆ std3 | — |
| `tests/T10_Quaternion.lean` | tool | ✅ PASS | 0 | 4.32 | 2986 | 58.5→58.2 | 5 thm ⊆ std3 | — |
| `tests/T11_NonAssocHierarchy.lean` | tool | ✅ PASS | 0 | 5.36 | 2141 | 58.2→58.8 | 3 thm ⊆ std3 | — |
| `tests/T12_FinsetSum.lean` | tool | ✅ PASS | 0 | 3.14 | 2026 | 58.8→58.6 | 7 thm ⊆ std3 | — |
| `tests/T13_RealAnalysis.lean` | tool | ✅ PASS | 0 | 3.94 | 2811 | 58.6→58.8 | 8 thm ⊆ std3 | — |
| `tests/T14_LinearAlgebra.lean` | tool | ✅ PASS | 0 | 4.1 | 2963 | 58.8→59.1 | 5 thm ⊆ std3 | — |
| `tests/T15_Complex.lean` | tool | ✅ PASS | 0 | 3.05 | 1957 | 59.1→58.9 | 5 thm ⊆ std3 | — |
| `tests/T16_CoreTactics.lean` | tool | ✅ PASS | 0 | 3.48 | 1971 | 59.0→67.9 | 13 thm ⊆ std3 | — |
| `tests/T17_FloatOracle.lean` | tool | ✅ PASS | 0 | 7.4 | 776 | 67.6→52.9 | 1 thm ⊆ std3 | — |
| `tests/T18_FinFold.lean` | tool | ✅ PASS | 0 | 1.35 | 776 | 53.1→55.5 | 3 thm ⊆ std3 | — |
| `tests/T19_NestedComments.lean` | tool | ✅ PASS | 0 | 1.14 | 776 | 55.8→56.5 | 2 thm ⊆ std3 | — |
| `must-fail/MF01_Sorry/MF01_Sorry.lean` | must-fail | ✅ PASS | 0 | 1.14 | 776 | 56.6→57.2 | 3 thm; non-std: sorryAx | Lean output: /^\d+:\d+: warning: declaration uses [`']sorry[`']$/; axiom audit: QBPToolcheck.MF01.unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.uses_unproved ⊇ sorryAx; axiom audit: QBPToolcheck.MF01.admitted ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF02_NativeDecide/MF02_NativeDecide.lean` | must-fail | ✅ PASS | 0 | 1.14 | 776 | 57.4→56.9 | 1 thm; non-std: QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.MF02.by_native has non-standard ['QBPToolcheck.MF02.by_native._native.native_decide.ax_1_1']; checker: /^::error::HARD-BAN violated — native_decide: 1 occurrence/ |
| `must-fail/MF03_VacuousTrue/MF03_VacuousTrue.lean` | must-fail | ✅ PASS | 0 | 1.13 | 776 | 57.1→57.1 | 2 thm ⊆ std3 | checker: /^::error::HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence/; checker: /^::error::RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0/ |
| `must-fail/MF04_FalseDecide/MF04_FalseDecide.lean` | must-fail | ✅ PASS | 1 | 1.15 | 776 | 57.4→57.4 | — | Lean rejected: /^19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false/; Lean rejected: /^22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false/ |
| `must-fail/MF05_CustomAxiom/MF05_CustomAxiom.lean` | must-fail | ✅ PASS | 0 | 1.13 | 776 | 57.5→57.2 | 1 thm; non-std: QBPToolcheck.MF05.cheat | axiom audit: QBPToolcheck.MF05.one_eq_two ⊇ QBPToolcheck.MF05.cheat; axiom audit: QBPToolcheck.MF05.one_eq_two has non-standard ['QBPToolcheck.MF05.cheat']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
| `must-fail/MF06_SpoofedAudit/MF06_SpoofedAudit.lean` | must-fail | ✅ PASS | 0 | 1.16 | 776 | 57.1→57.1 | 1 thm; non-std: sorryAx | axiom audit ignored 3 axiom-like message(s) not positioned at a `#print axioms` command (spoof guard); axiom audit: QBPToolcheck.MF06.spoofed ⊇ sorryAx; checker: /^::error::RATCHET violated — sorry: 1 > baseline 0\./ |
| `must-fail/MF07_SameLineSite/MF07_SameLineSite.lean` | must-fail | ✅ PASS | 0 | 1.13 | 776 | 57.2→57.2 | 2 thm; non-std: QBPToolcheck.MF07.cheat | axiom audit: QBPToolcheck.MF07.dirty ⊇ QBPToolcheck.MF07.cheat; axiom audit: QBPToolcheck.MF07.dirty has non-standard ['QBPToolcheck.MF07.cheat'] |
| `must-fail/MF08_InterpolationLexer/MF08_InterpolationLexer.lean` | must-fail | ✅ PASS | 0 | 1.15 | 776 | 57.4→57.5 | 2 thm; non-std: QBPToolcheck.MF08.cheat | grader REFUSES the file: brace inside a string literal at line(s) [38] — possible interpolation, which the lexer does not model (write a literal brace as \x7B); axiom audit: QBPToolcheck.MF08.dirty ⊇ QBPToolcheck.MF08.cheat |
| `must-fail/MF09_NonAsciiColumn/MF09_NonAsciiColumn.lean` | must-fail | ✅ PASS | 0 | 1.14 | 776 | 57.5→57.2 | 2 thm; non-std: QBPToolcheck.MF09.cheat | axiom audit: QBPToolcheck.MF09.dirty ⊇ QBPToolcheck.MF09.cheat; axiom audit: QBPToolcheck.MF09.dirty has non-standard ['QBPToolcheck.MF09.cheat'] |
| `known-limits/KL01_VacuityBypass/KL01_VacuityBypass.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.13 | 776 | 57.2→57.2 | 2 thm ⊆ std3 | KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.refl_implies_true` is clean ([]); KNOWN-LIMIT confirmed: `#print axioms QBPToolcheck.KL01.alternativity` is clean ([]) |
| `known-limits/KL02_FinFoldlDecide/KL02_FinFoldlDecide.lean` | known-limit | 🟡 KNOWN-LIMIT | 1 | 1.14 | 776 | 57.4→57.4 | — | KNOWN-LIMIT confirmed: Lean still rejects with /(?s)^19:\d+: error: Tactic `decide` failed.*did not reduce to `isTrue` or `isFalse`/ |
| `known-limits/KL03_CheckerStringComment/KL03_CheckerStringComment.lean` | known-limit | 🟡 KNOWN-LIMIT | 0 | 1.15 | 776 | 57.5→57.5 | 1 thm; non-std: QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1 | axiom audit: QBPToolcheck.KL03.hidden_native has non-standard ['QBPToolcheck.KL03.hidden_native._native.native_decide.ax_1_1']; KNOWN-LIMIT confirmed: foundations checker accepts the file (exit 0) |
