/-
  QBP.Foundations.CPPhase — δ_CP = arctan(√7) trigonometric anchor (#466 item 5)
  ==============================================================================

  Anchor `PRED-ckm-cp-phase-arctan-sqrt7` (paper §XI.A / §XIII.A): the CKM CP
  phase is the angle of the right triangle with legs √7 : 1 and hypotenuse √8,
  δ_CP := arctan(√7).  The explicit trigonometric link:

      tan δ_CP = √7,   sin² δ_CP = 7/8 = dim(Im 𝕆)/dim 𝕆,   cos² δ_CP = 1/8 = 1/dim 𝕆

  Relocated to `Foundations/` (from the untracked `QBP/Cosmo/AlgebraicIdentities.lean`,
  where `cp_phase_{sin,cos}_squared` record the rational 7/8 · 1/8 decomposition) so the
  anchor terminates at a committed, CI-built theorem rather than an untracked file.
  Self-contained (Mathlib `Real.arctan` only). Zero sorry / native_decide.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace QBP.Foundations.CPPhase

/-- The QBP CP phase: δ_CP = arctan(√7). -/
noncomputable def delta_CP : ℝ := Real.arctan (Real.sqrt 7)

/-- `tan(arctan √7) = √7`: the defining property of the √7 : 1 : √8 right-triangle angle. -/
theorem tan_delta_CP : Real.tan delta_CP = Real.sqrt 7 := by
  unfold delta_CP
  exact Real.tan_arctan _

/-- `sin²(arctan √7) = 7/8 = dim(Im 𝕆)/dim 𝕆`.  Opposite leg √7 over hypotenuse √8, squared. -/
theorem sin_sq_delta_CP : Real.sin delta_CP ^ 2 = 7 / 8 := by
  unfold delta_CP
  rw [Real.sin_sq_arctan]
  rw [Real.sq_sqrt (by norm_num : (7:ℝ) ≥ 0)]
  norm_num

/-- `cos²(arctan √7) = 1/8 = 1/dim 𝕆`.  Adjacent leg 1 over hypotenuse √8, squared. -/
theorem cos_sq_delta_CP : Real.cos delta_CP ^ 2 = 1 / 8 := by
  unfold delta_CP
  rw [Real.cos_sq_arctan]
  rw [Real.sq_sqrt (by norm_num : (7:ℝ) ≥ 0)]
  norm_num

/-- Consistency: the two squares sum to 1 (Pythagoras on the √7:1:√8 triangle). -/
theorem sin_sq_add_cos_sq_delta_CP :
    Real.sin delta_CP ^ 2 + Real.cos delta_CP ^ 2 = 1 := by
  rw [sin_sq_delta_CP, cos_sq_delta_CP]; norm_num

/-- The sin²/cos² ratio equals tan² = 7. -/
theorem tan_sq_delta_CP :
    Real.sin delta_CP ^ 2 / Real.cos delta_CP ^ 2 = 7 := by
  rw [sin_sq_delta_CP, cos_sq_delta_CP]; norm_num

end QBP.Foundations.CPPhase
