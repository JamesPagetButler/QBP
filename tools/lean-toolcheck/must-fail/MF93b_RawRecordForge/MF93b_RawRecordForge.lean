/-
TOOLCHECK MF93b — MUST-FAIL control (Red Team r8, its MF93 on PR #824): a file that rewrites an
EARLIER file's raw records in the REAL run directory DURING its own Lean process. This is not a
survivor, so the PID namespace is no defence, and it writes outside the throwaway area.

The `#eval` finds the repository through `LEAN_PATH` (its `proofs/.lake/build` entry), takes the
newest `results/runs/*/raw`, and rewrites the records of the decoy MF93a, which ran just before
it: `lean_exit` forced to 0 in its meta, and its log emptied.

The guard is the raw-record SEAL in `run.sh` (memory-held hashes, re-checked before grading). The
decoy expects its seal to break. This file itself is caught by the subset (`#eval`).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/

namespace QBPToolcheck.MF93b

theorem fine : (1 : Nat) = 1 := rfl

end QBPToolcheck.MF93b

#eval show IO Unit from do
  let script := "for e in $(echo \"$LEAN_PATH\" | tr ':' ' '); do case $e in */proofs/.lake/build/lib/lean) R=$(echo \"$e\" | sed 's#/proofs/.lake/build/lib/lean$##');; esac; done; [ -n \"$R\" ] || exit 0; d=$(ls -td \"$R\"/tools/lean-toolcheck/results/runs/*/raw 2>/dev/null | head -1); m=\"$d/MF93a_SealDecoy.meta.json\"; [ -f \"$m\" ] || exit 0; sed -i 's/\"lean_exit\": [0-9]*/\"lean_exit\": 0/' \"$m\"; : > \"$d/MF93a_SealDecoy.log\""
  let _ ← IO.Process.output { cmd := "bash", args := #["-c", script] }

#print axioms QBPToolcheck.MF93b.fine
