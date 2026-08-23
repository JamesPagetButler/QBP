/-
  QBP.Foundations.Hurwitz — the ℝ, ℂ, ℍ, 𝕆 normed-division tower: EXISTENCE + TERMINATION
  =======================================================================================

  Anchor for #466 item 6 (paper §I.1). The real normed division algebras are ℝ, ℂ, ℍ, 𝕆,
  of dimensions 1, 2, 4, 8, and the Cayley–Dickson tower terminates at 𝕆 (𝕊 is not a
  composition algebra).

  ── RETIREMENT NOTE (#589, 2026-08-22): the general Hurwitz UNIQUENESS axiom is GONE ──
  This file PREVIOUSLY stated the general Hurwitz/Albert *classification* — "ℝ,ℂ,ℍ,𝕆 are
  the ONLY finite-dim normed division algebras over ℝ" — as an external `axiom`
  (`hurwitz_classification`), the sole non-{propext, Classical.choice, Quot.sound} axiom in
  Foundations. A systematic literature review (#589) established that **uniqueness is NOT
  deductively load-bearing** in any division-algebra physics program (Furey, Dixon, the F₄
  exceptional-Jordan gauge-group result): every construction uses only the EXISTENCE and
  specific multiplication structure of ℝ,ℂ,ℍ,𝕆 — never "nothing else exists." (Tell: if a
  non-normed division algebra were exhibited, none of those constructions would change.)

  So the axiom is **RETIRED**. This file now anchors ONLY the existence + termination that
  QBP has actually PROVEN, and is fully axiom-clean (⊆ {propext, Classical.choice, Quot.sound}).
  The uniqueness / "closed-menu" claim is demoted to:
    * a published EXTERNAL result cited, not axiomatized — Hurwitz, Nachr. Ges. Wiss.
      Göttingen (1898) [composition]; Zorn (1930s) [alternative]; Bott–Milnor–Kervaire,
      Ann. of Math. (1958) [division — but DIMENSION-ONLY and NON-unique: many
      non-isomorphic real division algebras exist in dims 2,4,8], and
    * an OPEN QBP question — **#589**: is the substrate menu CLOSED at 4 (normed-division
      required) or OPEN past 𝕆 (division optional — the branch QBP's own 𝕊/𝕋 zero-divisor
      work commits to)? The axiom silently pre-decided "closed"; QBP has not, so it should
      not stand as foundational truth.
-/
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import QBP.Foundations.OctonionLaws
import QBP.Foundations.Breakdown
import QBP.Foundations.CDDimension

namespace QBP.Foundations.Hurwitz

open Module QBP.Foundations.CDAlg

/-! ## 1. Existence: ℝ, ℂ, ℍ, 𝕆 ARE normed division algebras of dims 1, 2, 4, 8 -/

/-- ℝ: multiplicative norm, dimension 1. -/
theorem real_case :
    (∀ x y : ℝ, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ finrank ℝ ℝ = 1 :=
  ⟨fun x y => norm_mul x y, finrank_self ℝ⟩

/-- ℂ: multiplicative norm, dimension 2. -/
theorem complex_case :
    (∀ x y : ℂ, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ finrank ℝ ℂ = 2 :=
  ⟨fun x y => norm_mul x y, Complex.finrank_real_complex⟩

/-- ℍ: multiplicative norm, dimension 4. -/
theorem quaternion_case :
    (∀ x y : Quaternion ℝ, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ finrank ℝ (Quaternion ℝ) = 4 :=
  ⟨fun x y => norm_mul x y, Quaternion.finrank_eq_four⟩

/-- 𝕆 = `CDAlg ℝ 3`: the norm form `N` is MULTIPLICATIVE — 𝕆 is a composition algebra.
    (Re-exports `OctonionLaws.octonion_norm_composition`, kernel-proved.) -/
theorem octonion_norm_multiplicative (x y : CDAlg ℝ 3) : N (x * y) = N x * N y :=
  octonion_norm_composition x y

/-- 𝕆 has dimension 8 = 2³ (from `CDDimension.finrank_cdAlg`). -/
theorem octonion_dim_eight : finrank ℝ (CDAlg ℝ 3) = 8 := by
  rw [CDDimension.finrank_cdAlg]; norm_num

/-! ## 2. Termination: the tower stops at 𝕆 — 𝕊 is NOT a composition algebra -/

/-- 𝕊 = `CDAlg ℝ 4` (dim 16): its norm form is NOT multiplicative — there are `x, y`
    with `N (x*y) ≠ N x · N y`. So 𝕊 is not a normed division algebra; the tower
    terminates at 𝕆. (Re-exports `Breakdown.sedenion_norm_not_multiplicative`, which is
    backed by an explicit zero-divisor witness; and see the `42` in `Breakdown`.) -/
theorem sedenion_not_composition : ∃ x y : CDAlg ℝ 4, N (x * y) ≠ N x * N y :=
  QBP.Foundations.Breakdown.sedenion_norm_not_multiplicative

/-- 𝕊 has dimension 16 = 2⁴. -/
theorem sedenion_dim_sixteen : finrank ℝ (CDAlg ℝ 4) = 16 := by
  rw [CDDimension.finrank_cdAlg]; norm_num

/-! ## 3. The four normed-division dimensions land in {1, 2, 4, 8} -/

/-- The dimensions of the four real normed division algebras ℝ, ℂ, ℍ, 𝕆 are exactly
    the Hurwitz set {1, 2, 4, 8}. (Existence direction — NOT the uniqueness converse,
    which is the external/#589 open question above.) -/
theorem tower_dims_in_1248 :
    (finrank ℝ ℝ ∈ ({1, 2, 4, 8} : Set ℕ)) ∧
    (finrank ℝ ℂ ∈ ({1, 2, 4, 8} : Set ℕ)) ∧
    (finrank ℝ (Quaternion ℝ) ∈ ({1, 2, 4, 8} : Set ℕ)) ∧
    (finrank ℝ (CDAlg ℝ 3) ∈ ({1, 2, 4, 8} : Set ℕ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [finrank_self]; simp
  · rw [Complex.finrank_real_complex]; simp
  · rw [Quaternion.finrank_eq_four]; simp
  · rw [octonion_dim_eight]; simp

/-! ## Completeness audit — `#print axioms` (now fully clean; the axiom is retired) -/

#print axioms real_case
#print axioms complex_case
#print axioms quaternion_case
#print axioms octonion_norm_multiplicative
#print axioms octonion_dim_eight
#print axioms sedenion_not_composition
#print axioms sedenion_dim_sixteen
#print axioms tower_dims_in_1248

end QBP.Foundations.Hurwitz
