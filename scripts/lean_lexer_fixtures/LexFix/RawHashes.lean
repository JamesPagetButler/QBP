-- PR #829 Gemini r1 finding 2, two `#`: the body holds `"#` (which does NOT close an `r##"`
-- string) and a comment opener. To Lean `vac` is CODE.
namespace LexFix.RawHashes

def opener : String := r##" "# /- "##

theorem vac : True := trivial

def close : String := "-/"

end LexFix.RawHashes
