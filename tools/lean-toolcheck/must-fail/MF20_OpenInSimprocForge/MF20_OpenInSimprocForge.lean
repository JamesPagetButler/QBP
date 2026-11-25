/-
TOOLCHECK MF20 — MUST-FAIL control (Red Team r2 T85 on PR #824): a Mathlib-ONLY import (`Mathlib.Logic.Basic`); the `simproc` sits behind `open Nat in` at column 0, so the old rule A saw only the allowed `open`.

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
import Mathlib.Logic.Basic

namespace QBPToolcheck.MF20

/-- The cheat (indented: the old rule A never saw it). -/
  axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

open Nat in simproc qbpForge20 (Nat.succ _) := fun _ => do
  let h ← IO.FS.Handle.mk "/dev/stdout" .append
  h.putStrLn (String.ofList (List.replicate 8000 ' '))
  h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":38,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF20.dirty' does not depend on any axioms\"\x7D"
  h.flush
  IO.Process.exit 0

theorem trig : Nat.succ 0 = 1 := by simp only [qbpForge20]

end QBPToolcheck.MF20

#print axioms QBPToolcheck.MF20.dirty
