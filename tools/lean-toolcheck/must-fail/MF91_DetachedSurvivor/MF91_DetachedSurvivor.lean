/-
TOOLCHECK MF91 — MUST-FAIL control (Red Team r7, its MF91 on PR #824): a file that starts a
DETACHED process (`setsid`) meant to OUTLIVE its Lean process. The Red Team's version waited for
the post-run verification and then rewrote the real grader, and a `sorry` pass file graded GREEN.

This control's daemon writes a heartbeat into its working directory every 100 ms for 60 s, and
after about 2 s appends a line to `../../toolcheck.py`. Its working directory is inside the
throwaway suite copy (or the throwaway audit area), so it never touches the real tree.

Guards that must hold:
1. Every Lean process runs as PID 1 of its own PID namespace (`unshare --fork --pid
   --kill-child`). When it exits, the kernel kills the daemon too.
2. Second layer: `run.sh` re-hashes the throwaway area 1.2 s after the file's last Lean process.
   A surviving daemon keeps writing, the survivor check reports it (`late_writes`), and the run
   is INVALID. The selftest shows this by replaying a namespace-off run.

The heartbeats written while the `--json` run is alive are expected (`writes-detected`).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
TOOLCHECK-EXPECT: writes-detected
-/

namespace QBPToolcheck.MF91

theorem fine : (1 : Nat) = 1 := rfl

end QBPToolcheck.MF91

#eval show IO Unit from do
  let script := "for i in $(seq 1 600); do date +%s%N > .mf91-alive; if [ $i -eq 20 ] && [ -f ../../toolcheck.py ]; then echo '# MF91 survivor was here' >> ../../toolcheck.py; fi; sleep 0.1; done"
  let _ ← IO.Process.spawn
    { cmd := "setsid", args := #["bash", "-c", script],
      stdin := .null, stdout := .null, stderr := .null }
  IO.sleep 500

#print axioms QBPToolcheck.MF91.fine
