/-
  Producer for the fanoTableF4 cross-repo snapshot (#59 / qbp-cu #65).
  NOT part of the QBP.Foundations aggregator — run deliberately:
    lake env lean FanoSnapshotGen.lean        (from the proofs/ project root)
  Emits to stdout: 64 lines `i j sign index` from the KERNEL-PROVEN `fanoTableF4`,
  a marker, then the axiom attestation for the two provenance theorems.
-/
import QBP.Foundations.FanoOrientationF3
import QBP.Foundations.CDAlg
open QBP.Foundations.FanoOrientationF3

def snapLines : String :=
  String.intercalate "\n" <|
    (List.finRange 8).flatMap fun i =>
      (List.finRange 8).map fun j =>
        let c := fanoTableF4 i j
        s!"{i.val} {j.val} {c.1} {c.2.val}"

#eval IO.println "===SNAPSHOT==="
#eval IO.println snapLines
#eval IO.println "===AXIOMS==="
#print axioms fanoTableF4_eq_cayleyDickson
#print axioms QBP.Foundations.CDAlg.mulCoeff_three_eq_fano
