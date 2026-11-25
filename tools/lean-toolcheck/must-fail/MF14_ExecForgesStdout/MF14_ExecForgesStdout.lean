/-
TOOLCHECK MF14 — MUST-FAIL control: code RUN during elaboration forges Lean's `--json`
stdout and then exits before Lean prints the real report (Red Team 1(b) on PR #824).

The `#eval` opens `/dev/stdout` in append mode, writes a forged `information` message
"'…dirty' does not depend on any axioms" positioned EXACTLY at the `#print axioms` site
below, and calls `IO.Process.exit 0`. Lean never elaborates the `#print axioms`, so its real
report (`cheat`) is never printed, the exit code is 0, there is one report at the site and
nothing unpositioned: every stdout-based rule is satisfied by the forgery. No stdout audit can
be sound on a file that runs code, so the grader refuses code-executing constructs in a pass
file (the pass-file subset); `selftest_grader.py` replays this file as a pass-labelled attack. The
audit cannot see `cheat` here — the subset refusal is the only detector.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/

namespace QBPToolcheck.MF14

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF14

#eval show IO Unit from do
  let h ← IO.FS.Handle.mk "/dev/stdout" .append
  h.putStrLn (String.ofList (List.replicate 8000 ' '))
  h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":34,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF14.dirty' does not depend on any axioms\"\x7D"
  h.flush
  IO.Process.exit 0

#print axioms QBPToolcheck.MF14.dirty
