-- PR #829 Gemini r2 finding 1 (same lexer-gap class as PR #824 T89/T90), shape P4: hex precedence + raw-string atom (a context with no space required).
-- A lexer that read only decimal digits took `0` and then an identifier, read the rest as an
-- ordinary string with an escape, and opened a FAKE comment at `/-`, hiding `vac`. Lexed per
-- Lean's `numberFnAux`, `vac` is code; the glued number and the literal are refused.
namespace LexFix.NumNotation

notation:0x41r"\" " /- " => (0 : Nat)

theorem vac : True := trivial

def close : String := "-/"

end LexFix.NumNotation
