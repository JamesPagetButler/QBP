-- PR #829 (same lexer-desync class): an escaped identifier `«…»` may hold a comment opener.
-- To Lean it is a name, so `vac` is CODE.
namespace LexFix.Guillemet

def «/-» : Nat := 1

theorem vac : True := trivial

def close : String := "-/"

end LexFix.Guillemet
