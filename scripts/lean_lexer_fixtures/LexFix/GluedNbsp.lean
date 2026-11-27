-- PR #829 Red Team r2 finding 5 (probe T6): U+00A0 (no-break space) is NOT Lean whitespace,
-- so a token may start with it. To Lean `<U+00A0>/-` is that token and `vac` is CODE; a
-- lexer that exempted Unicode spaces opened a comment there and hid `vac`.
namespace LexFix.GluedNbsp

macro " /-" : term => `((0 : Nat))

def z : Nat :=  /-

theorem vac : True := trivial

-- -/

end LexFix.GluedNbsp
