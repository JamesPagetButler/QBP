-- PR #829 Gemini r2 finding 1 (same lexer-gap class as PR #824 T89/T90), shape P2: hex number + char literal.
-- A lexer that read only decimal digits took `0` and then an identifier, read the rest as an
-- ordinary string with an escape, and opened a FAKE comment at `/-`, hiding `vac`. Lexed per
-- Lean's `numberFnAux`, `vac` is code; the glued number and the literal are refused.
-- Lean 4.30 ITSELF rejects this file (an argument needs whitespace before it; CI run
-- 45672287560: "unexpected token; expected command" right after the number), so this
-- exact forge is not real; the self-test asserts the rejection. NumNotation.lean is the
-- same shape in a context with no space required, and Lean does compile that one.
namespace LexFix.NumHexChar

def g (a : Nat) (b : Char) (c : String) : Nat := a + b.toNat + c.length
def a := g 0x1'\"' " /- "

theorem vac : True := trivial

def close : String := "-/"

end LexFix.NumHexChar
