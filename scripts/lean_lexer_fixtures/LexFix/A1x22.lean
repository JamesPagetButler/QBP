-- PR #829 Red Team r5 finding 1 (the quote written as the escape `\x22`), reproduced on Lean 4.30: the file DECLARES a
-- token containing a quote. Lean reads that token whole; a lexer reads a quote, opens a string,
-- desyncs into a FAKE comment at `/-` and hides `vac`. Lean compiles this file and `vac` is a
-- real declaration. The token-declaring command is refused (interim ban, QBP#836).
namespace LexFix.A1x22

notation "zz\x22" x => x
def a : String := zz" " /- "
theorem vac : True := by trivial
def close : String := "-/"

end LexFix.A1x22
