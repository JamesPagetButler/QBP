/-
TOOLCHECK T96 — DEMONSTRATION FILE ONLY (Red Team r9 on PR #824). Never part of the suite:
`demos/T96_MF95/run_demo.sh` copies it into a scratch suite copy as tests/T96_PassDecoy.lean.

A PASS-labelled tool file with a FALSE theorem that also lists the decoy exemption. At `df2b03e`
the exemption was not restricted to must-fails, so once MF95 (a later file) rewrote this file's
records, it graded PASS and the run was GREEN. Now `records-tampered` is allowed only for a
must-fail decoy (never with `pass`): this file FAILS, and `run.sh` makes the run INVALID.

TOOLCHECK-EXPECT: pass
TOOLCHECK-EXPECT: records-tampered
-/

namespace QBPToolcheck.T96

theorem bad : (2 : Nat) + 2 = 5 := by decide

end QBPToolcheck.T96

#print axioms QBPToolcheck.T96.bad
