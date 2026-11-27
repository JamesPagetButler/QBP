/-
TOOLCHECK MF11 — MUST-FAIL control: a LONE CARRIAGE RETURN (0x0d) in a comment desyncs the
line count (found while fixing Gemini r4 (f) on PR #824). The literal CR is between the brackets:
[]
Lean does not start a line at a lone `\r` (`FileMap` breaks at `\n` only; the frontend
rewrites only `\r\n`). Python's text-mode read applies universal newlines and turns a lone
`\r` into `\n`, so the pre-fix grader (`read_text`) saw every later line ONE LOWER than Lean:
it expected the `dirty` report one line below the real `#print axioms`, which is exactly where
the `run_cmd` emits a genuine `information` message forging a clean report. The real report
was discarded as "unpositioned" and the forged one accepted: a pass-labelled copy passed.
The grader must read bytes, apply only Lean's `\r\n` -> `\n`, split at `\n` only, and see
`QBPToolcheck.MF11.cheat`. `selftest_grader.py` replays this file as a pass-labelled attack.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF11.dirty QBPToolcheck.MF11.cheat
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF11.dirty
-/

import Lean

namespace QBPToolcheck.MF11

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF11

#print axioms QBPToolcheck.MF11.dirty
run_cmd Lean.logInfo "'QBPToolcheck.MF11.dirty' does not depend on any axioms"
