/-
TOOLCHECK MF08 — MUST-FAIL control: string INTERPOLATION used to desynchronise the grader's
lexer from Lean's (Gemini r2 (c) on PR #824).

The definition `evil` below is an interpolated string whose `{ … }` hole holds another
string containing a block-comment opener. Lean reads it as a string expression. A lexer
that does not model interpolation sees a short string, then a comment opener in CODE,
and treats the REST OF THE FILE as a comment — so the `#print axioms` for `dirty` (which
rests on a user axiom) vanishes from the expected sites, and in a pass-labelled file only
`clean` would be audited.

Decision (supported subset, not full interpolation lexing): the grader REFUSES any suite
file with a brace inside a string literal. Every interpolation needs a brace inside the
first string segment the simple lexer sees, so refusing braces makes the string rule exact
for every accepted file. Literal braces are written as \x7B / \x7D (T17, MF06). On a
refused file the lexer's site list is not trusted, so the grader audits EVERY axiom report
Lean emitted (worst-case merged) — it must still report `cheat` for `dirty`.
`selftest_grader.py` replays this file as a pass-labelled attack.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: grader-refuses
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF08.dirty QBPToolcheck.MF08.cheat
-/

namespace QBPToolcheck.MF08

/-- The cheat. -/
axiom cheat : False

theorem clean : (1 : Nat) = 1 := rfl

end QBPToolcheck.MF08

#print axioms QBPToolcheck.MF08.clean

namespace QBPToolcheck.MF08

def evil : String := s!" { " /- " } "

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF08

#print axioms QBPToolcheck.MF08.dirty
