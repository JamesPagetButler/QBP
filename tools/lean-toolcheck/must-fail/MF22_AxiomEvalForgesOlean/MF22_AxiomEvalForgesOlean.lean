/-
TOOLCHECK MF22 — MUST-FAIL control (Red Team r4 T86 on PR #824): a REAL user `axiom cheat`
that the structural audit cannot see, because an `#eval` forges the `.olean` it audits.

`dirty` rests on `cheat`. The `#eval` reads its own `/proc/self/cmdline`. In the FRESH COMPILE
(`lean -o PATH`) it compiles a CLEAN module of the same name to PATH in a child `lean` and exits
0, so the PR #829 auditor audits the substituted `.olean` and reports no non-standard axiom
(#829's stated limit S1, QBP#836: the compile is not sandboxed). In the `--json` run it forges a
clean report at the `#print axioms` site and exits 0, as MF14 does.

This is the strongest S1 case: unlike MF21 the file has a genuine non-standard axiom, and the
audit alone still passes it. Only the pass-file SUBSET (rules A/H/D: `axiom`; rule B: `#eval`)
catches it, so the subset is the PRECONDITION for the structural verdict until QBP#836 adds a
sandbox. `selftest_grader.py` replays this file with every subset rule off, where the audit is
EXPECTED to be fooled (it documents S1, replacing the old "auditor alone" claim).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/

namespace QBPToolcheck.MF22

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF22

#eval show IO Unit from do
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
    IO.FS.writeFile src "theorem QBPToolcheck.MF22.dirty : (1 : Nat) = 1 := rfl\n"
    let _ ← IO.Process.output { cmd := "lean", args := #["-R", root.toString, "-o", out, src.toString] }
    IO.Process.exit 0
  | _ =>
    let h ← IO.FS.Handle.mk "/dev/stdout" .append
    h.putStrLn (String.ofList (List.replicate 8000 ' '))
    h.putStrLn "\x7B\"severity\":\"information\",\"pos\":\x7B\"line\":51,\"column\":0\x7D,\"data\":\"'QBPToolcheck.MF22.dirty' does not depend on any axioms\"\x7D"
    h.flush
    IO.Process.exit 0

#print axioms QBPToolcheck.MF22.dirty
