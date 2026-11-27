-- PR #829 Gemini r1 finding 3 (char-literal class). In `x'"''/-"` the `'` belongs to the
-- identifier `x'` (a notation variable) and `"''/-"` is a STRING (the notation's atom), so `vac`
-- is CODE to Lean. The first Python lexer took `'"'` for a char literal, opened a comment at
-- `/-` and hid `vac`. (A notation item list is one of the places where an identifier may be
-- followed by a string with no space; a function application needs the space.)
namespace LexFix.CharPrime

notation:max "qbpop" x'"''/-" => x' ++ "!"

theorem vac : True := trivial

def close : String := "-/"

end LexFix.CharPrime
