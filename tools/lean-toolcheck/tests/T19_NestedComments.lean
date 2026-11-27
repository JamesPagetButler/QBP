/-
TOOLCHECK T19 — nested block comments and comment-like strings around theorem names
(Gemini (6) on PR #824: the grader's old non-greedy regex stripper ended a nested block
comment at its FIRST inner closer, exposing the rest as "code").

Feature: Lean block comments NEST (an opener inside a block comment opens a deeper level —
which is why this header spells no comment markers literally: writing one here would itself
open a nested comment and swallow the file, as the first run of this test showed), a double
dash starts a line comment, and comment markers inside string literals are just characters.
The grader
derives the expected `#print axioms` targets from comment-stripped source, so it must lex
these exactly as Lean does. Below, `ghost` appears in a `#print axioms` line that is INSIDE a
nested comment (Lean never runs it; the old stripper expected a report for it and failed
this file), and `real_after_nested` sits right after a nested comment (it must still be
seen and audited).

Used by: every QBP file with nested or doc comments (the grader parses all of them).

TOOLCHECK-EXPECT: pass
-/

namespace QBPToolcheck.T19

/- outer /- inner -/ still the outer comment:
#print axioms QBPToolcheck.T19.ghost
-/
/-- A theorem right after a nested comment. -/
theorem real_after_nested : (3 : Nat) + 4 = 7 := rfl

/-- A string that contains comment markers is not a comment. -/
def tricky : String := "/- not a comment -- nor this"

theorem tricky_eq : tricky = "/- not a comment -- nor this" := rfl

/- /- /- three deep -/ -/ #print axioms QBPToolcheck.T19.ghost2 -/

end QBPToolcheck.T19

#print axioms QBPToolcheck.T19.real_after_nested
#print axioms QBPToolcheck.T19.tricky_eq
