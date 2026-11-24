/-
TOOLCHECK MF13 — MUST-FAIL control: a CLEAN file with a brace inside a string literal
(Red Team mutants M13/M19 on PR #824).

Everything here is honestly proved, but the string contains a brace, which the lexer does not
model (possible interpolation). The grader must REFUSE the file. `selftest_grader.py` replays
it as a pass-labelled file (must FAIL by refusal alone: kills "an unexpected refusal is not a
failure") and with the brace removed from the source copy (must FAIL: kills "`grader-refuses`
on a file that is not refused does not fail").

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: grader-refuses
-/

namespace QBPToolcheck.MF13

theorem clean : (1 : Nat) = 1 := rfl

def braced : String := "a { b"

end QBPToolcheck.MF13

#print axioms QBPToolcheck.MF13.clean
