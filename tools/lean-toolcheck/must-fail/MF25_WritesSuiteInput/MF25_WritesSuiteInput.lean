/-
TOOLCHECK MF25 — MUST-FAIL control (Red Team r6 concern 1 on PR #824): a file that WRITES A
SUITE INPUT while it runs. Must-fail and known-limit files run user code by design, so an effect
could persist into the next run (a rewritten grader, allowlist or test).

The `#eval` appends a newline to `../../subset_kinds.json`, relative to its working directory,
which is the directory of the file being compiled. `run.sh` now runs every file's code-running
Lean processes in a THROWAWAY COPY of the suite (cwd inside the copy), so the write lands in the
copy's allowlist, never the real one. The copy is hashed before and after the file, so the write is
attributed to this file (`suite_copy_writes`), and any file that writes without expecting it FAILS.
The real tree is covered separately: `run.sh` hashes every input before the first Lean process
and verifies it after the last one, so an absolute-path write makes the run INVALID.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
TOOLCHECK-EXPECT: writes-detected
-/

namespace QBPToolcheck.MF25

theorem fine : (1 : Nat) = 1 := rfl

end QBPToolcheck.MF25

#eval show IO Unit from do
  let p : System.FilePath := "../../subset_kinds.json"
  if ← p.pathExists then
    let s ← IO.FS.readFile p
    IO.FS.writeFile p (s ++ "\n")

#print axioms QBPToolcheck.MF25.fine
