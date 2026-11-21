/-
TOOLCHECK MF06 — MUST-FAIL control: a SPOOFED axiom audit (Gemini (2) on PR #824).

`spoofed` really uses `sorry`, so Lean's `#print axioms` reports `[sorryAx]`. The file
then PRINTS fake "clean" reports — before and after the real one, in the plain text form
and as a forged `--json`-shaped line — trying to make the grader see
"'QBPToolcheck.MF06.spoofed' does not depend on any axioms". Before the fix, the plain
text parser read the fake line after the real one and overwrote `sorryAx` with `[]`.

The grader must still see `sorryAx`, because (a) it trusts only Lean's own `--json`
message stream, and only an `information` message positioned exactly at a
`#print axioms QBPToolcheck.MF06.spoofed` command (the `#eval` output arrives as a
message at the `#eval`'s position and is rejected), and (b) reports merge worst-case,
so nothing can clear a non-standard axiom once reported. The checker also catches the
`sorry`. If the audit is fooled, the suite FAILS.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF06.spoofed sorryAx
TOOLCHECK-EXPECT: checker-reject ^::error::RATCHET violated — sorry: 1 > baseline 0\.
-/

namespace QBPToolcheck.MF06

/-- Really unproved. -/
theorem spoofed : 2 + 2 = 5 := by
  sorry

end QBPToolcheck.MF06

#eval IO.println "'QBPToolcheck.MF06.spoofed' does not depend on any axioms"
#print axioms QBPToolcheck.MF06.spoofed
#eval IO.println "'QBPToolcheck.MF06.spoofed' does not depend on any axioms"
#eval IO.println "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":31,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF06.spoofed' does not depend on any axioms\"\x7D"
