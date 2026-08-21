/-
  QBP.Foundations.UnitQuaternion — ψ ∈ Sp(1): unit-quaternion state necessity
  ==========================================================================

  Anchor for #466 item 4 (paper Theorem 1): a fundamental particle state is a
  unit quaternion, i.e. an element of

      Sp(1) = { q : ℍ // ‖q‖ = 1 },

  and Sp(1) is a group under quaternion multiplication.

  Content proved here (all against Mathlib's `Quaternion ℝ` with its
  `NormedDivisionRing` structure, in which `‖p * q‖ = ‖p‖ * ‖q‖` holds exactly):

  1. `Sp1` — the unit sphere `Metric.sphere (0 : ℍ[ℝ]) 1`, which Mathlib
     equips with a `Group` instance (`Metric.unitSphere.instGroup`).
  2. `mem_Sp1_iff_norm` — membership is exactly `‖q‖ = 1` (so `Sp1` IS the
     subtype `{q : ℍ // ‖q‖ = 1}` of the statement; `sp1EquivSubtype` makes
     the identification an explicit `Equiv`).
  3. Closure/identity/inverse at the carrier level: `norm_mul_of_unit`,
     `norm_one_quat`, `norm_inv_of_unit`, and `star_mul_self_of_unit`
     (the inverse of a unit quaternion is its conjugate).
  4. **Necessity** (`norm_preserving_iff_unit`): left multiplication by `q`
     preserves the norm of EVERY state iff `‖q‖ = 1`.  This is the
     Theorem-1 content: probability conservation forces evolution operators
     into Sp(1), and normalised states live on the same sphere.

  `LieAlgebraIso.lean` (𝔰𝔲(2) ≅ Im ℍ) is the tangent-space companion of this
  file: Sp(1) here is the group, Im ℍ there is its Lie algebra.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Normed.Field.UnitBall

namespace QBP.Foundations.UnitQuaternion

open Quaternion

/-- Real quaternions (matches the `Q` abbreviation in `LieAlgebraIso.lean`). -/
abbrev Q := Quaternion ℝ

/-- **Sp(1)**: the unit quaternions, as the unit sphere in ℍ.  Mathlib's
    `Metric.unitSphere.instGroup` makes this a group under quaternion
    multiplication (because ℍ is a `NormedDivisionRing`: the norm is exactly
    multiplicative). -/
noncomputable def Sp1 := Metric.sphere (0 : Q) 1

/-- Membership in Sp(1) is exactly the unit-norm condition `‖q‖ = 1`. -/
theorem mem_Sp1_iff_norm (q : Q) : q ∈ Metric.sphere (0 : Q) 1 ↔ ‖q‖ = 1 :=
  mem_sphere_zero_iff_norm

/-- Sp(1) IS the subtype `{q : ℍ // ‖q‖ = 1}` of the paper statement:
    the identification is an explicit `Equiv`. -/
noncomputable def sp1EquivSubtype :
    Metric.sphere (0 : Q) 1 ≃ { q : Q // ‖q‖ = 1 } where
  toFun x := ⟨x.val, (mem_Sp1_iff_norm x.val).mp x.property⟩
  invFun x := ⟨x.val, (mem_Sp1_iff_norm x.val).mpr x.property⟩

/-- Closure: the product of two unit quaternions is a unit quaternion.
    (ℍ is a composition algebra: `‖p q‖ = ‖p‖ ‖q‖` exactly.) -/
theorem norm_mul_of_unit {p q : Q} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ‖p * q‖ = 1 := by
  rw [norm_mul, hp, hq, mul_one]

/-- Identity: `1 : ℍ` is a unit quaternion. -/
theorem norm_one_quat : ‖(1 : Q)‖ = 1 := norm_one

/-- Inverses: the inverse of a unit quaternion is a unit quaternion. -/
theorem norm_inv_of_unit {q : Q} (hq : ‖q‖ = 1) : ‖q⁻¹‖ = 1 := by
  rw [norm_inv, hq, inv_one]

/-- The inverse of a unit quaternion is its conjugate: `q* · q = 1` when
    `‖q‖ = 1` (so Sp(1)-inversion is quaternion conjugation). -/
theorem star_mul_self_of_unit {q : Q} (hq : ‖q‖ = 1) : star q * q = 1 := by
  have hns : normSq q = 1 := by
    have := Quaternion.normSq_eq_norm_mul_self q
    rw [hq, mul_one] at this
    simpa using this
  have h := Quaternion.star_mul_self q
  rw [h, hns]
  simp

/-- `q · q* = 1` when `‖q‖ = 1` (two-sided inverse). -/
theorem mul_star_self_of_unit {q : Q} (hq : ‖q‖ = 1) : q * star q = 1 := by
  have hns : normSq q = 1 := by
    have := Quaternion.normSq_eq_norm_mul_self q
    rw [hq, mul_one] at this
    simpa using this
  have h := Quaternion.self_mul_star q
  rw [h, hns]
  simp

/-- Sp(1) is a group: witnessed by Mathlib's instance on the unit sphere of a
    normed division ring.  (Stated as a definition so downstream files can
    name the group structure; the instance itself is found by class search.) -/
@[reducible] noncomputable def sp1Group : Group (Metric.sphere (0 : Q) 1) := inferInstance

/-- **Necessity (paper Theorem 1 content).**  Left multiplication by `q`
    preserves the norm of every state ψ iff `q` is a unit quaternion:

        (∀ ψ, ‖q ψ‖ = ‖ψ‖)  ↔  ‖q‖ = 1.

    Forward: evaluate at ψ = 1.  Backward: the norm on ℍ is multiplicative.
    Probability conservation therefore forces evolution operators — and, by
    acting on the reference state 1, normalised states themselves — into
    Sp(1). -/
theorem norm_preserving_iff_unit (q : Q) :
    (∀ ψ : Q, ‖q * ψ‖ = ‖ψ‖) ↔ ‖q‖ = 1 := by
  constructor
  · intro h
    have h1 := h 1
    rwa [mul_one, norm_one] at h1
  · intro hq ψ
    rw [norm_mul, hq, one_mul]

/-! ## Completeness audit — `#print axioms` -/

#print axioms mem_Sp1_iff_norm
#print axioms norm_mul_of_unit
#print axioms norm_inv_of_unit
#print axioms star_mul_self_of_unit
#print axioms mul_star_self_of_unit
#print axioms norm_preserving_iff_unit

end QBP.Foundations.UnitQuaternion
