-- PR #829 Red Team r2 finding 5 (probe T5): a user token that STARTS with `(` and contains
-- `/-`. To Lean `(/-` is that token, so `vac` is CODE; a lexer that exempted `(` opened a
-- comment there and hid `vac` up to the `-/` in the line comment.
namespace LexFix.GluedParen

macro "(/-" : term => `((0 : Nat))

def z : Nat := (/-

theorem vac : True := trivial

-- -/

end LexFix.GluedParen
