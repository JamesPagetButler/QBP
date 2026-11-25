/-
TOOLCHECK MF16 — MUST-FAIL control (Red Team r2 T81 on PR #824): the handler attribute is NOT first in the `@[…]` list (`@[inline, command_elab …]`).

No `#eval`/`run_cmd` token appears in code, so the `c333116` token denylist missed it, and the
trigger forges a clean `--json` report for `dirty` (which rests on `axiom cheat : False`) at its
`#print axioms` site on `/dev/stdout`, then exits 0 before Lean prints the real report. Any
user syntax or handler can expand to `#eval`, so only the pass-file SUBSET (a top-level command
allowlist + attribute allowlist + syntax/handler keyword refusal) closes this class.
`selftest_grader.py` replays this file as a pass-labelled attack. The audit cannot see `cheat`
here; the subset refusal is the only detector.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/
import Lean
open Lean Elab Command

namespace QBPToolcheck.MF16

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF16

syntax (name := qbpGo16) "qbp_go_16" : command

@[inline, command_elab qbpGo16] def goImpl16 : CommandElab := fun _ => do
  let h ← IO.FS.Handle.mk "/dev/stdout" .append
  h.putStrLn (String.ofList (List.replicate 8000 ' '))
  h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":37,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF16.dirty' does not depend on any axioms\"\x7D"
  h.flush
  IO.Process.exit 0

qbp_go_16
#print axioms QBPToolcheck.MF16.dirty
