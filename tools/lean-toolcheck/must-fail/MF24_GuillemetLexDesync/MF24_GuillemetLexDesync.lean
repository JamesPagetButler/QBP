/-
TOOLCHECK MF24 — MUST-FAIL control (Red Team r5 T90 on PR #824): a LEXER DESYNC through
guillemet identifiers. Two definitions are named with guillemets around the block-comment opener
and closer (see the code below). To Lean they are plain identifiers. The Python lexer of `67a214b`
read the opener inside the first name as a block comment, closed by the second name, so the
indented `simproc_pattern%` between them was blanked: rule H never saw it, and the file graded
PASS with a forged `.olean` (MF21's payload, S1).

Now refused twice: rule R (any guillemet in a pass file) and the Lean-parser layer
(`LeanSubsetParse.lean` sees the `simproc_pattern%` command kind, which is not allowlisted).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/
import Lean
open Lean Meta Simp

namespace QBPToolcheck.MF24

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
    IO.FS.writeFile src "theorem QBPToolcheck.MF24.bogus : (1 : Nat) = 1 := rfl\n"
    let _ ← IO.Process.output { cmd := "lean", args := #["-R", root.toString, "-o", out, src.toString] }
    IO.Process.exit 0
  | _ =>
    let h ← IO.FS.Handle.mk "/dev/stdout" .append
    h.putStrLn (String.ofList (List.replicate 8000 ' '))
    h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":51,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF24.bogus' does not depend on any axioms\"\x7D"
    h.flush
    IO.Process.exit 0

def «/-» : Nat := 0
  simproc_pattern% Nat.succ _ => QBPToolcheck.MF24.go
def «-/» : Nat := 0

theorem trig : Nat.succ 0 = 1 := by simp only [go]

theorem bogus : (1 : Nat) = 2 := rfl

end QBPToolcheck.MF24

#print axioms QBPToolcheck.MF24.bogus
