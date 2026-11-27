/-
TOOLCHECK T10 — Mathlib's `Quaternion` / `QuaternionAlgebra` API: the `ℍ[ℝ]` notation,
component projections (`re`, `imI`, `imJ`, `imK`), `Quaternion.ext`, `star` (conjugation),
`Quaternion.normSq`, and the constructed non-commutativity witness `i*j ≠ j*i`.

Feature: QBP reuses Mathlib's quaternions for the ℍ rung of the ℝ→ℂ→ℍ→𝕆 ladder rather
than defining its own (standard §9). The ✗ cell "commutativity lost at ℍ" must be a
*constructed* witness (standard §6), proved here with `Quaternion.ext_iff` + `norm_num`.

Used by (QBP, 2026-11-20 grep, 12 files): `QBP/Foundations/TowerLaws.lean`,
`QBP/Experiments/DoubleSlit.lean`, `QBP/Foundations/CDBridge.lean`, `Exp.lean`
(`open scoped Quaternion in`), `UnitQuaternion.lean` (`star`), `Hurwitz.lean`;
imports `Mathlib.Algebra.Quaternion` (6 files), `Mathlib.Analysis.Quaternion` (5 files),
`Mathlib.Analysis.Normed.Algebra.QuaternionExponential` (`Exp.lean`).

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped Quaternion

namespace QBPToolcheck.T10

/-- Unit `i`. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
/-- Unit `j`. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
/-- Unit `k`. -/
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

/-- Hamilton's `i j = k`. -/
theorem i_mul_j : qi * qj = qk := by
  ext <;> simp [qi, qj, qk]

/-- The ✗ cell: ℍ is not commutative — `i j - j i = 2k ≠ 0`, a constructed witness. -/
theorem quaternion_not_comm : qi * qj ≠ qj * qi := by
  intro h
  -- the k-components are 1 and -1
  have hk : (qi * qj).imK = (qj * qi).imK := congrArg (fun q : ℍ[ℝ] => q.imK) h
  norm_num [qi, qj] at hk

/-- Conjugation (`star`) negates the imaginary part. -/
theorem star_qi : star qi = -qi := by
  ext <;> simp [qi]

/-- `normSq` of a general quaternion is the sum of squares. -/
theorem normSq_eq (a b c d : ℝ) : Quaternion.normSq (⟨a, b, c, d⟩ : ℍ[ℝ]) = a^2 + b^2 + c^2 + d^2 := by
  rw [Quaternion.normSq_def']

/-- `normSq` is multiplicative (Mathlib's `map_mul` on the monoid-with-zero hom). -/
theorem normSq_mul (p q : ℍ[ℝ]) :
    Quaternion.normSq (p * q) = Quaternion.normSq p * Quaternion.normSq q :=
  map_mul _ p q

end QBPToolcheck.T10

#print axioms QBPToolcheck.T10.i_mul_j
#print axioms QBPToolcheck.T10.quaternion_not_comm
#print axioms QBPToolcheck.T10.star_qi
#print axioms QBPToolcheck.T10.normSq_eq
#print axioms QBPToolcheck.T10.normSq_mul
