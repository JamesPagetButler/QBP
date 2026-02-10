/-
  Angle-Dependent Measurement (Experiment 01b) - Formal Proofs

  This file contains the formal verification for the angle-dependent measurement
  experiment. It proves that the QBP framework correctly predicts the probability
  formula P(+) = cos²(θ/2) for a state at angle θ from the measurement axis.

  Ground Truth: research/01b_angle_dependent_expected_results.md
  Analysis: analysis/01b_angle_dependent/
-/
import QBP.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QBP.Experiments.AngleDependent

open QBP Real

-- ### SETUP: Define the Angle-Dependent State ###

/-- A spin state at angle θ from the z-axis in the xz-plane.
    ψ(θ) = sin(θ)·i + cos(θ)·k
    At θ=0: ψ = k (spin-z up)
    At θ=π/2: ψ = i (spin-x)
    At θ=π: ψ = -k (spin-z down) -/
noncomputable def psiAngle (θ : ℝ) : Q := ⟨0, Real.sin θ, 0, Real.cos θ⟩

/-- The measurement axis: spin along z (the k quaternion) -/
def spinZObservable : Q := SPIN_Z

-- ### VERIFICATION: Confirm Properties ###

/-- The angle-dependent state is a pure quaternion (real part = 0) -/
theorem psiAngle_is_pure (θ : ℝ) : isPureQuaternion (psiAngle θ) := rfl

/-- The spin-z observable is a pure quaternion -/
theorem spinZObservable_is_pure : isPureQuaternion spinZObservable := spin_z_is_pure

/-- The angle-dependent state is a unit quaternion (|ψ|² = 1) -/
theorem psiAngle_is_unit (θ : ℝ) : isUnitQuaternion (psiAngle θ) := by
  unfold isUnitQuaternion psiAngle
  simp [Quaternion.normSq]
  ring_nf
  exact Real.sin_sq_add_cos_sq θ

-- ### CORE THEOREM: Expectation Value ###

/-- **Physical Principle:** The expectation value equals cos(θ).
    For a state ψ(θ) = sin(θ)·i + cos(θ)·k measured on the z-axis,
    ⟨O⟩ = vecDot(ψ, O) = sin(θ)·0 + 0·0 + cos(θ)·1 = cos(θ)

    This is the projection of the state onto the measurement axis. -/
theorem expectation_angle (θ : ℝ) :
    expectationValue (psiAngle θ) spinZObservable = Real.cos θ := by
  unfold expectationValue psiAngle spinZObservable vecDot vecPart SPIN_Z
  simp

-- ### CORE THEOREM: Probability Formula ###

/-- **Physical Principle:** P(+) = (1 + cos θ)/2 = cos²(θ/2)
    This is the fundamental probability formula for angle-dependent measurement.
    The equality (1 + cos θ)/2 = cos²(θ/2) is the half-angle identity. -/
theorem prob_up_angle (θ : ℝ) :
    probUp (psiAngle θ) spinZObservable = (1 + Real.cos θ) / 2 := by
  unfold probUp
  rw [expectation_angle]

/-- **Alternative form:** P(+) = cos²(θ/2)
    Uses the half-angle identity: cos²(θ/2) = (1 + cos θ)/2 -/
theorem prob_up_angle_cos_sq (θ : ℝ) :
    probUp (psiAngle θ) spinZObservable = Real.cos (θ / 2) ^ 2 := by
  rw [prob_up_angle]
  rw [Real.cos_sq]
  ring_nf

/-- P(-) = (1 - cos θ)/2 -/
theorem prob_down_angle (θ : ℝ) :
    probDown (psiAngle θ) spinZObservable = (1 - Real.cos θ) / 2 := by
  unfold probDown
  rw [expectation_angle]

/-- **Alternative form:** P(-) = sin²(θ/2)
    Uses the half-angle identity: sin²(θ/2) = (1 - cos θ)/2 -/
theorem prob_down_angle_sin_sq (θ : ℝ) :
    probDown (psiAngle θ) spinZObservable = Real.sin (θ / 2) ^ 2 := by
  rw [prob_down_angle]
  have h : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have h1 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [h1, Real.cos_two_mul, Real.sin_sq]
    ring
  rw [h]

-- ### EDGE CASES: Verify Known Results ###

/-- At θ=0, the state is aligned with measurement: P(+) = 1 -/
theorem prob_up_theta_zero : probUp (psiAngle 0) spinZObservable = 1 := by
  rw [prob_up_angle]
  simp [Real.cos_zero]

/-- At θ=π, the state is anti-aligned: P(+) = 0 -/
theorem prob_up_theta_pi : probUp (psiAngle Real.pi) spinZObservable = 0 := by
  rw [prob_up_angle]
  simp [Real.cos_pi]

/-- At θ=π/2, the state is perpendicular: P(+) = 1/2
    This matches the Stern-Gerlach result (spin-x measured on z). -/
theorem prob_up_theta_pi_div_two :
    probUp (psiAngle (Real.pi / 2)) spinZObservable = 1 / 2 := by
  rw [prob_up_angle]
  simp [Real.cos_pi_div_two]

-- ### CONSISTENCY: Match Stern-Gerlach at θ=π/2 ###

/-- The angle-dependent formula recovers the Stern-Gerlach result.
    At θ=π/2, ψ = i = SPIN_X, and we get P(+) = 1/2. -/
theorem angle_consistent_with_stern_gerlach :
    psiAngle (Real.pi / 2) = SPIN_X := by
  unfold psiAngle SPIN_X
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two]

end QBP.Experiments.AngleDependent
