-- PR #829 Gemini r1 finding 2: a raw string holding `"` and a comment opener. To Lean the
-- string ends at `"#` and `vac` is CODE; the first Python lexer closed the string at the inner
-- `"`, opened a comment at `/-` and hid `vac` up to the `-/` in `close`.
namespace LexFix.Raw

def opener : String := r#" " /- "#

theorem vac : True := trivial

def close : String := "-/"

end LexFix.Raw
