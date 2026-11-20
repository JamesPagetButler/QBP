/-
TOOLCHECK MF03 — MUST-FAIL control: vacuous `: True :=` "theorems" (the #472 class:
a non-alternative octonion table survived behind `alternativity : True := by trivial`).

Lean ACCEPTS this file AND the axiom audit is CLEAN (`True.intro` needs no axioms) —
`#print axioms` cannot see vacuity. For the LITERAL shape `: True :=` the foundations
checker catches it:
  - `: True := by trivial` is a HARD-BAN;
  - any `: True :=` theorem is a RATCHET item (zero baseline here ⇒ rejected).
LIMIT — the checker's vacuity detection is SYNTACTIC ONLY (a regex on `: True :=`).
A vacuous statement in any other spelling — `x = x → True`, or the #472 shape behind a
beta-redex `(fun _ => True) 3` — passes BOTH the checker and the axiom audit. Those are
pinned as report-only known limits in `known-limits/KL01_VacuityBypass/` (Red Team F3 on
PR #824). Only a human reading the statement catches them. If the checker misses either
literal form here, the suite FAILS.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: checker-reject HARD-BAN violated — vacuous-proof `: True := by trivial`: 1 occurrence
TOOLCHECK-EXPECT: checker-reject RATCHET violated — vacuous-`: True :=` theorem: 2 > baseline 0
-/

namespace QBPToolcheck.MF03

/-- The #472 stub shape. -/
theorem octonion_is_alternative : True := by trivial

/-- The same vacuity with a term-mode body (not matched by the hard-ban regex). -/
theorem sedenion_is_flexible : True := trivial

end QBPToolcheck.MF03

#print axioms QBPToolcheck.MF03.octonion_is_alternative
#print axioms QBPToolcheck.MF03.sedenion_is_flexible
