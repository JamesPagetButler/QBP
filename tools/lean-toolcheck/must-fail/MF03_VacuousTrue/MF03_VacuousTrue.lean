/-
TOOLCHECK MF03 — MUST-FAIL control: vacuous `: True :=` "theorems" (the #472 class:
a non-alternative octonion table survived behind `alternativity : True := by trivial`).

Lean ACCEPTS this file AND the axiom audit is CLEAN (`True.intro` needs no axioms) —
`#print axioms` cannot see vacuity. Only the foundations checker catches it:
  - `: True := by trivial` is a HARD-BAN;
  - any `: True :=` theorem is a RATCHET item (zero baseline here ⇒ rejected).
This control documents that the axiom gate alone is NOT sufficient (statement-level
review + the checker are both needed). If the checker misses either form, the suite FAILS.

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
