/-
TOOLCHECK MF93a — DECOY for MF93b (Red Team r8, its MF93 on PR #824). This file's theorem is
FALSE (`2 + 2 = 5` by `decide`), so its real run fails. MF93b, which runs right after it, rewrites
this file's raw records in the REAL run directory while MF93b's own Lean process is still alive:
`lean_exit` forced to 0 and the log emptied, so that a stale grader would see a clean run.

The guard: `run.sh` seals every file's raw records in its own memory as soon as they are
complete, and re-checks every seal before grading. This file EXPECTS its seal to break, and is
graded on the seal alone (its records are untrusted once tampered). Any OTHER file whose seal
breaks FAILS and makes the run INVALID. If MF93b's write did not happen or was not caught, this
file FAILS ("expected … tampered with, but its seal held").

TOOLCHECK-EXPECT: records-tampered
-/

namespace QBPToolcheck.MF93a

theorem bad : (2 : Nat) + 2 = 5 := by decide

end QBPToolcheck.MF93a

#print axioms QBPToolcheck.MF93a.bad
