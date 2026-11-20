/-
TOOLCHECK MF01 — MUST-FAIL control: `sorry`, direct and inherited through a dependency.

Lean ACCEPTS this file (exit 0, a warning only) — which is exactly why `sorry` is
dangerous. The suite must detect it two ways:
  (1) the axiom audit: `#print axioms` shows `sorryAx` for BOTH theorems — the
      direct one and the one that only *uses* the sorried lemma (taint propagates,
      federation standard §2/§3);
  (2) the foundations checker (`scripts/check_lean_foundations.py`, zero baseline)
      rejects the new `sorry` under its RATCHET rule.
If either detection is missing, the suite FAILS (a must-fail that passes is a failure).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: lean-output warning: declaration uses [`']sorry[`']
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF01.unproved sorryAx
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF01.uses_unproved sorryAx
TOOLCHECK-EXPECT: checker-reject RATCHET violated — sorry: 1 > baseline 0
-/

namespace QBPToolcheck.MF01

/-- An unproved statement (deliberate). -/
theorem unproved : ∀ n : Nat, n + 0 = n := by
  sorry

/-- A theorem whose own proof is complete but rests on `unproved`. -/
theorem uses_unproved : 5 + 0 = 5 := unproved 5

end QBPToolcheck.MF01

#print axioms QBPToolcheck.MF01.unproved
#print axioms QBPToolcheck.MF01.uses_unproved
