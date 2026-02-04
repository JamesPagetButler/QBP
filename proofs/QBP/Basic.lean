import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion

namespace QBP

/-- Use mathlib's quaternion type over reals -/
abbrev Q := Quaternion ℝ

/-- Axiom 1: State is a unit quaternion (|ψ|² = 1) -/
def isUnitQuaternion (q : Q) : Prop := q.normSq = 1

/-- Axiom 2: Observable is a pure quaternion (real part = 0) -/
def isPureQuaternion (q : Q) : Prop := q.re = 0

/-- Example theorem: pure quaternion has zero real part -/
theorem pure_has_zero_re (q : Q) (h : isPureQuaternion q) : q.re = 0 := h

/-- The three standard spin observables -/
def SPIN_X : Q := ⟨0, 1, 0, 0⟩
def SPIN_Y : Q := ⟨0, 0, 1, 0⟩
def SPIN_Z : Q := ⟨0, 0, 0, 1⟩

/-- SPIN_X is a pure quaternion -/
theorem spin_x_is_pure : isPureQuaternion SPIN_X := rfl

/-- SPIN_Y is a pure quaternion -/
theorem spin_y_is_pure : isPureQuaternion SPIN_Y := rfl

/-- SPIN_Z is a pure quaternion -/
theorem spin_z_is_pure : isPureQuaternion SPIN_Z := rfl

/-- Extract the vector part (i,j,k components) of a quaternion -/
def vecPart (q : Q) : Q := ⟨0, q.imI, q.imJ, q.imK⟩

/-- Dot product of two quaternions' vector parts -/
def vecDot (q₁ q₂ : Q) : ℝ :=
  q₁.imI * q₂.imI + q₁.imJ * q₂.imJ + q₁.imK * q₂.imK

/-- Expectation value: ⟨O⟩ = ψ* · O · ψ projected to scalar
    For pure quaternion observables, this equals the dot product of vector parts -/
def expectationValue (ψ O : Q) : ℝ :=
  let ψ_vec := vecPart ψ
  let O_vec := vecPart O
  2 * vecDot ψ_vec O_vec

/-- Probability of measuring +1 (spin up): P(+) = (1 + ⟨O⟩) / 2 -/
def probUp (ψ O : Q) : ℝ := (1 + expectationValue ψ O) / 2

/-- Probability of measuring -1 (spin down): P(-) = (1 - ⟨O⟩) / 2 -/
def probDown (ψ O : Q) : ℝ := (1 - expectationValue ψ O) / 2

/-- Perpendicular states have zero expectation value -/
theorem expectation_orthogonal_is_zero (ψ O : Q)
    (hψ : isPureQuaternion ψ) (hO : isPureQuaternion O)
    (h_ortho : vecDot ψ O = 0) : expectationValue ψ O = 0 := by
  simp [expectationValue, vecPart, hψ, hO]
  simp [vecDot] at h_ortho
  linarith

/-- Perpendicular measurement gives 50/50 probability -/
theorem prob_up_orthogonal_is_half (ψ O : Q)
    (hψ : isPureQuaternion ψ) (hO : isPureQuaternion O)
    (h_ortho : vecDot ψ O = 0) : probUp ψ O = 1/2 := by
  simp [probUp, expectation_orthogonal_is_zero ψ O hψ hO h_ortho]
  ring

end QBP
