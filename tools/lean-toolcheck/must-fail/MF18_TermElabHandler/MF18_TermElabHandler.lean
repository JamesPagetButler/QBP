/-
TOOLCHECK MF18 — MUST-FAIL control (Red Team r2 T83 on PR #824): a `syntax … : term` + `attribute [term_elab …]`, fired from inside an ordinary `def`.

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
open Lean Elab Term

namespace QBPToolcheck.MF18

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF18

syntax (name := qbpGo18) "qbp_go_18" : term

def goImpl18 : TermElab := fun _ _ => do
  let h ← IO.FS.Handle.mk "/dev/stdout" .append
  h.putStrLn (String.ofList (List.replicate 8000 ' '))
  h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":42,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF18.dirty' does not depend on any axioms\"\x7D"
  h.flush
  IO.Process.exit 0

attribute [term_elab qbpGo18] goImpl18

def QBPToolcheck.MF18.trigger : Nat := qbp_go_18
#print axioms QBPToolcheck.MF18.dirty
