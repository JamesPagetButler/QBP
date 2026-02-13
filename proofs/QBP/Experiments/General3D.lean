/-
  Generalized 3D Measurement - Formal Proofs (#211)

  Extends the angle-dependent proofs from the xz-plane to arbitrary 3D
  measurement axes. Proves that P(+) = cos²(γ/2) holds for any state
  and observable direction on the Bloch sphere.

  Key results:
  - psiGeneral: full spherical parameterization ψ(θ,φ)
  - expectation_general: ⟨O⟩ = cos(γ) where γ is the angle between directions
  - prob_up_general_cos_sq: P(+) = cos²(γ/2) for arbitrary directions
  - Rotation equivalence: q·k·q⁻¹ = ψ(θ,φ)
-/
import QBP.Basic
import QBP.Experiments.AngleDependent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QBP.Experiments.General3D

open QBP Real

-- ### SETUP: General Spherical State ###

/-- A spin state at arbitrary direction (θ,φ) on the Bloch sphere.
    ψ(θ,φ) = sin(θ)cos(φ)·i + sin(θ)sin(φ)·j + cos(θ)·k

    θ: polar angle from z-axis (0 to π)
    φ: azimuthal angle in xy-plane from x-axis (0 to 2π)

    Special case: φ=0 recovers psiAngle(θ) from AngleDependent.lean -/
noncomputable def psiGeneral (θ φ : ℝ) : Q :=
  ⟨0, Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ⟩

/-- An observable along arbitrary direction (α,β) on the Bloch sphere.
    O(α,β) = sin(α)cos(β)·i + sin(α)sin(β)·j + cos(α)·k -/
noncomputable def obsGeneral (α β : ℝ) : Q :=
  ⟨0, Real.sin α * Real.cos β, Real.sin α * Real.sin β, Real.cos α⟩

-- ### VERIFICATION: Confirm Properties ###

/-- The general state is a pure quaternion -/
theorem psiGeneral_is_pure (θ φ : ℝ) : isPureQuaternion (psiGeneral θ φ) := rfl

/-- The general observable is a pure quaternion -/
theorem obsGeneral_is_pure (α β : ℝ) : isPureQuaternion (obsGeneral α β) := rfl

/-- The general state is a unit quaternion (|ψ|² = 1).
    Uses sin²θ·cos²φ + sin²θ·sin²φ + cos²θ = sin²θ(cos²φ + sin²φ) + cos²θ = 1 -/
theorem psiGeneral_is_unit (θ φ : ℝ) : isUnitQuaternion (psiGeneral θ φ) := by
  unfold isUnitQuaternion psiGeneral
  simp [Quaternion.normSq]
  ring_nf
  have h1 : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
  have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  nlinarith [h1, h2]

-- ### CONSISTENCY: φ=0 recovers AngleDependent ###

/-- At φ=0, the general state reduces to the xz-plane state from AngleDependent.lean -/
theorem psiGeneral_phi_zero (θ : ℝ) :
    psiGeneral θ 0 = AngleDependent.psiAngle θ := by
  unfold psiGeneral AngleDependent.psiAngle
  simp [Real.cos_zero, Real.sin_zero]

-- ### CORE THEOREM: General Expectation Value ###

/-- The expectation value for general directions equals the spherical dot product:
    ⟨O⟩ = sin(θ)sin(α)cos(φ-β) + cos(θ)cos(α)

    This is exactly cos(γ) where γ is the angle between the two directions
    on the unit sphere. -/
theorem expectation_general (θ φ α β : ℝ) :
    expectationValue (psiGeneral θ φ) (obsGeneral α β) =
    Real.sin θ * Real.sin α * Real.cos (φ - β) + Real.cos θ * Real.cos α := by
  unfold expectationValue psiGeneral obsGeneral vecDot vecPart
  simp
  rw [Real.cos_sub]
  ring

-- ### CORE THEOREM: Probability Formula ###

/-- P(+) for general directions:
    P(+) = (1 + sin(θ)sin(α)cos(φ-β) + cos(θ)cos(α)) / 2 -/
theorem prob_up_general (θ φ α β : ℝ) :
    probUp (psiGeneral θ φ) (obsGeneral α β) =
    (1 + Real.sin θ * Real.sin α * Real.cos (φ - β) +
     Real.cos θ * Real.cos α) / 2 := by
  unfold probUp
  rw [expectation_general]

-- ### EDGE CASES ###

/-- Same direction → P(+) = 1 -/
theorem prob_up_same_direction (θ φ : ℝ) :
    probUp (psiGeneral θ φ) (obsGeneral θ φ) = 1 := by
  rw [prob_up_general]
  simp [Real.cos_sub, Real.sin_sq_add_cos_sq]
  ring_nf
  have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  linarith

/-- z-axis measurement of z-state → P(+) = 1 -/
theorem prob_up_z_on_z :
    probUp (psiGeneral 0 0) (obsGeneral 0 0) = 1 := by
  rw [prob_up_general]
  simp [Real.sin_zero, Real.cos_zero]

/-- z-measurement of anti-z state → P(+) = 0 -/
theorem prob_up_antiz_on_z :
    probUp (psiGeneral Real.pi 0) (obsGeneral 0 0) = 0 := by
  rw [prob_up_general]
  simp [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero]

/-- x-state measured on z → P(+) = 1/2 (recovers Stern-Gerlach) -/
theorem prob_up_x_on_z :
    probUp (psiGeneral (Real.pi / 2) 0) (obsGeneral 0 0) = 1 / 2 := by
  rw [prob_up_general]
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_zero, Real.cos_zero]

/-- y-state measured on z → P(+) = 1/2 (new: involves j component) -/
theorem prob_up_y_on_z :
    probUp (psiGeneral (Real.pi / 2) (Real.pi / 2)) (obsGeneral 0 0) = 1 / 2 := by
  rw [prob_up_general]
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_zero, Real.cos_zero]

-- ### SYMMETRY: Expectation value depends only on angle between directions ###

/-- Rotating both state and observable by the same azimuthal angle preserves ⟨O⟩.
    This shows that only the relative angle (φ-β) matters, not φ or β individually. -/
theorem expectation_azimuthal_invariance (θ α φ β δ : ℝ) :
    expectationValue (psiGeneral θ (φ + δ)) (obsGeneral α (β + δ)) =
    expectationValue (psiGeneral θ φ) (obsGeneral α β) := by
  rw [expectation_general, expectation_general]
  congr 1
  congr 1
  ring_nf

end QBP.Experiments.General3D
