/-
TOOLCHECK MF10 — MUST-FAIL control: a FORM FEED (0x0c) in a comment desyncs the line count
(Gemini r4 (f) on PR #824). The literal form feed is on the next line, between the brackets:
[]
Lean's `FileMap` starts a new line only at `\n` (and the frontend rewrites `\r\n` to `\n`);
Python's `str.splitlines()` also breaks at `\f`, `\v`, `\r`, `\x1c`-`\x1e`, `\x85`, U+2028,
U+2029. The pre-fix grader took site LINES from the comment-blanked text (form feed -> space,
so the lines were right) but site COLUMNS from `src.splitlines()[ln - 1]`, which after the form
feed is the PREVIOUS Lean line. Below, that previous line is empty, so the grader expected the
`dirty` report at column 0 — exactly where the `run_cmd` on the same line emits a genuine
`information` message forging a clean report. The real report (column > 0) was discarded as
"unpositioned" and the forged one accepted: a pass-labelled copy of this file passed.
The grader must split at `\n` only and see `QBPToolcheck.MF10.cheat`. The checker has no rule
for `axiom`, so the audit is the only detector. `selftest_grader.py` replays this file as a
pass-labelled attack. Lean's own line counting is probed in the PR #824 r4 response.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF10.dirty QBPToolcheck.MF10.cheat
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF10.dirty
-/

import Lean

namespace QBPToolcheck.MF10

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF10

run_cmd Lean.logInfo "'QBPToolcheck.MF10.dirty' does not depend on any axioms" #print axioms QBPToolcheck.MF10.dirty
