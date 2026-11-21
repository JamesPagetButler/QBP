/-
TOOLCHECK MF07 — MUST-FAIL control: a `#print axioms` site that is NOT at the start of
its line (Gemini r2 (b) on PR #824).

`dirty` rests on a user axiom. Its `#print axioms` command sits on the same line as the
one for `clean`, after it. The pre-fix grader only looked for sites at the start of a line,
so it never expected a report for `dirty` and discarded Lean's real report for it as
"unpositioned". In a pass-labelled file that is a silent pass: only `clean` gets audited.
The grader must find the site anywhere on the line (column = the `#` of the command) and
see `QBPToolcheck.MF07.cheat`. The checker has no rule for `axiom`, so the audit is the
only detector. `selftest_grader.py` replays this file as a pass-labelled attack.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF07.dirty QBPToolcheck.MF07.cheat
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF07.dirty
-/

namespace QBPToolcheck.MF07

/-- The cheat. -/
axiom cheat : False

theorem clean : (1 : Nat) = 1 := rfl

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF07

#print axioms QBPToolcheck.MF07.clean #print axioms QBPToolcheck.MF07.dirty
