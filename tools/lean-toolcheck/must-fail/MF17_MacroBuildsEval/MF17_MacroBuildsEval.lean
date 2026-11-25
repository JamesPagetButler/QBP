/-
TOOLCHECK MF17 — MUST-FAIL control (Red Team r2 T82 on PR #824): a `macro` builds an `#eval` node from `mkAtom "#eval"` (the `#eval` token is inside a string, so it is blanked from the code-only text). No import at all.

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

namespace QBPToolcheck.MF17

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF17

macro "qbp_go_17" : command => do
  let t ← `(term| show IO Unit from do
    let h ← IO.FS.Handle.mk "/dev/stdout" .append
    h.putStrLn (String.ofList (List.replicate 8000 ' '))
    h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":38,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF17.dirty' does not depend on any axioms\"\x7D"
    h.flush
    IO.Process.exit 0)
  pure ⟨Lean.Syntax.node Lean.SourceInfo.none `Lean.Parser.Command.eval #[Lean.mkAtom "#eval", t.raw]⟩

qbp_go_17
#print axioms QBPToolcheck.MF17.dirty
