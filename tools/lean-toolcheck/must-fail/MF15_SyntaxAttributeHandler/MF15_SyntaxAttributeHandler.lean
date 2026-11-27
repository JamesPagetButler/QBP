/-
TOOLCHECK MF15 — MUST-FAIL control (Red Team r2 T80 on PR #824): `syntax` + a plain `def` + `attribute [command_elab …]`.

No `#eval`/`run_cmd` token appears in code, so the `c333116` token denylist missed it, and the
trigger forges a clean `--json` report for `dirty` (which rests on `axiom cheat : False`) at its
`#print axioms` site on `/dev/stdout`, then exits 0 before Lean prints the real report. Any
user syntax or handler can expand to `#eval`, so only the pass-file SUBSET (a top-level command
allowlist + attribute allowlist + syntax/handler keyword refusal) refuses this class, and the
STRUCTURAL audit (PR #829 auditor on a fresh .olean) fails it closed: the file exits before an
.olean is written.
`selftest_grader.py` replays this file as a pass-labelled attack. The audit cannot see `cheat`
on stdout; the subset refusal and the structural audit are the detectors.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
TOOLCHECK-EXPECT: audit-fails
-/
import Lean
open Lean Elab Command

namespace QBPToolcheck.MF15

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF15

syntax (name := qbpGo15) "qbp_go_15" : command

def goImpl15 : CommandElab := fun _ => do
  let h ← IO.FS.Handle.mk "/dev/stdout" .append
  h.putStrLn (String.ofList (List.replicate 8000 ' '))
  h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":42,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF15.dirty' does not depend on any axioms\"\x7D"
  h.flush
  IO.Process.exit 0

attribute [command_elab qbpGo15] goImpl15

qbp_go_15
#print axioms QBPToolcheck.MF15.dirty
