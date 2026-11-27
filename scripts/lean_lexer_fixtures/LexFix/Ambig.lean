-- PR #829 (same class): Lean looks for `--` / `/-` only at a token boundary. In `//-n` the
-- symbol token `//` (subtype notation) is matched first, so `-n < 0` and `vac` are CODE to
-- Lean. A lexer without Lean's token table cannot tell, so the checker REFUSES a comment
-- opener glued to a symbol character.
namespace LexFix.Ambig

def Neg : Type := { n : Int //-n > 0 }

theorem vac : True := trivial

def close : String := "-/"

end LexFix.Ambig
