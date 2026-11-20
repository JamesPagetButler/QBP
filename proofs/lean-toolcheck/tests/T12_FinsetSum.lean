/-
TOOLCHECK T12 — big operators over `Fin n`: `∑ i : Fin n, f i`, `Fin.sum_univ_succ`,
`Fin.sum_univ_four`/`Fin.sum_univ_eight`, `Finset.sum_comm`, `Finset.sum_congr`,
`Finset.sum_add_distrib`, `Finset.mul_sum`.

Feature: QBP's coordinate algebras define products and bilinear forms as finite sums over
basis indices; the proofs expand or swap those sums with these lemma names. Lemma *names*
are the migration risk (Mathlib renames and deprecates big-operator lemmas regularly),
so each is used by name here.

Used by (QBP, 2026-11-20 grep, 23 files): `QBP/Foundations/Alternator.lean` (136 sums,
`Finset.sum_comm`, `Finset.sum_congr`), `CDAlg.lean`, `CDLifting.lean`,
`G2Transitivity.lean`; `Fin.sum_univ_four`: `SeamSpectrum.lean`, `SeamKernel.lean`;
`Fin.sum_univ_eight`: `SeamSpectrum.lean`; import
`Mathlib.Algebra.BigOperators.Group.Finset.Basic` (2 files).

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace QBPToolcheck.T12

/-- Expanding a 4-term sum by name. -/
theorem sum_four (f : Fin 4 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_four]

/-- Expanding an 8-term sum by name (octonion coordinate count). -/
theorem sum_eight (f : Fin 8 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  rw [Fin.sum_univ_eight]

/-- `Fin.sum_univ_succ` peeling the first term. -/
theorem sum_succ (f : Fin 3 → ℤ) : ∑ i, f i = f 0 + ∑ i : Fin 2, f i.succ := by
  rw [Fin.sum_univ_succ]

/-- Swapping a double sum (`Finset.sum_comm`). -/
theorem sum_swap (a : Fin 3 → Fin 4 → ℝ) : ∑ i, ∑ j, a i j = ∑ j, ∑ i, a i j :=
  Finset.sum_comm

/-- `Finset.sum_add_distrib` and `Finset.mul_sum`. -/
theorem sum_lin (c : ℝ) (f g : Fin 5 → ℝ) :
    c * ∑ i, (f i + g i) = ∑ i, c * f i + ∑ i, c * g i := by
  rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]

/-- `Finset.sum_congr` rewriting the summand pointwise. -/
theorem sum_congr_use (f : Fin 6 → ℝ) : ∑ i, (f i + f i) = ∑ i, 2 * f i := by
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- A closed integer sum evaluated by kernel `decide` (structured enumeration). -/
theorem sum_closed : ∑ i : Fin 10, (i.val : ℤ) = 45 := by decide

end QBPToolcheck.T12

#print axioms QBPToolcheck.T12.sum_four
#print axioms QBPToolcheck.T12.sum_eight
#print axioms QBPToolcheck.T12.sum_succ
#print axioms QBPToolcheck.T12.sum_swap
#print axioms QBPToolcheck.T12.sum_lin
#print axioms QBPToolcheck.T12.sum_congr_use
#print axioms QBPToolcheck.T12.sum_closed
