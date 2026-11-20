/-
TOOLCHECK MF01 — MUST-FAIL control: `sorry`, direct and inherited through a dependency,
plus `admit` (a `sorry` synonym the text checker does not match).

Lean ACCEPTS this file (exit 0, warnings only) — which is exactly why `sorry` is
dangerous. The suite must detect it two ways:
  (1) the axiom audit: `#print axioms` shows `sorryAx` for ALL THREE theorems — the
      direct one, the one that only *uses* the sorried lemma (taint propagates,
      federation standard §2/§3), and the `admit` one;
  (2) the foundations checker (`scripts/check_lean_foundations.py`, zero baseline)
      rejects the new `sorry` under its RATCHET rule. It counts the word `sorry` only:
      the `admit` theorem is NOT counted (sorry: 1, not 2), so for `admit` the axiom
      audit is the only detector — the reason the audit is the completeness gate.
If any detection is missing, the suite FAILS (a must-fail that passes is a failure).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: lean-output ^\d+:\d+: warning: declaration uses [`']sorry[`']$
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF01.unproved sorryAx
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF01.uses_unproved sorryAx
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF01.admitted sorryAx
TOOLCHECK-EXPECT: checker-reject ^::error::RATCHET violated — sorry: 1 > baseline 0\.
-/

namespace QBPToolcheck.MF01

/-- An unproved statement (deliberate). -/
theorem unproved : ∀ n : Nat, n + 0 = n := by
  sorry

/-- A theorem whose own proof is complete but rests on `unproved`. -/
theorem uses_unproved : 5 + 0 = 5 := unproved 5

/-- `admit` — the tactic synonym for `sorry` (Red Team F2 note on PR #824). -/
theorem admitted : 2 + 2 = 5 := by
  admit

end QBPToolcheck.MF01

#print axioms QBPToolcheck.MF01.unproved
#print axioms QBPToolcheck.MF01.uses_unproved
#print axioms QBPToolcheck.MF01.admitted
