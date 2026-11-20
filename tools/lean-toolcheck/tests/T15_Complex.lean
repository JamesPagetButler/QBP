/-
TOOLCHECK T15 — Mathlib `Complex` (`ℂ`): `Complex.ext_iff`, `Complex.I_sq`,
`Complex.normSq`, real/imag parts of products, conjugation (`starRingEnd`), and the
algebra map ℝ → ℂ.

Feature: the ℂ rung of the tower (order is lost at ℂ). QBP proves tower laws on ℂ and
bridges ℂ ↪ ℍ.

Used by (QBP, 2026-11-20 grep, 3 files): `QBP/Foundations/TowerLaws.lean` (40 hits),
`Hurwitz.lean`, `Breakdown.lean`; imports `Mathlib.Data.Complex.Basic` (2 files),
`Mathlib.Analysis.SpecialFunctions.Complex.Log`, `Mathlib.LinearAlgebra.Complex.FiniteDimensional`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace QBPToolcheck.T15

/-- `I² = -1`. -/
theorem I_sq : Complex.I ^ 2 = -1 := Complex.I_sq

/-- Multiplication in coordinates, via `Complex.ext_iff`. -/
theorem mul_coords (a b c d : ℝ) :
    (⟨a, b⟩ : ℂ) * ⟨c, d⟩ = ⟨a * c - b * d, a * d + b * c⟩ := by
  apply Complex.ext <;> simp

/-- `normSq` is the sum of squares. -/
theorem normSq_coords (a b : ℝ) : Complex.normSq ⟨a, b⟩ = a * a + b * b := by
  rw [Complex.normSq_mk]

/-- Conjugation negates the imaginary part. -/
theorem conj_im (z : ℂ) : (starRingEnd ℂ z).im = -z.im := Complex.conj_im z

/-- The ✗ cell "order lost at ℂ": there is no `x` with `x * x = -1` in ℝ, but `I` is one in ℂ. -/
theorem no_real_sqrt_neg_one : ¬ ∃ x : ℝ, x * x = -1 := by
  rintro ⟨x, hx⟩
  nlinarith [mul_self_nonneg x]

end QBPToolcheck.T15

#print axioms QBPToolcheck.T15.I_sq
#print axioms QBPToolcheck.T15.mul_coords
#print axioms QBPToolcheck.T15.normSq_coords
#print axioms QBPToolcheck.T15.conj_im
#print axioms QBPToolcheck.T15.no_real_sqrt_neg_one
