/-
  Stern-Gerlach Experiment (Experiment 1) - Formal Proofs

  This file contains the formal verification for the Stern-Gerlach experiment.
  It proves that the QBP framework correctly predicts a 50/50 probability
  split for a spin-x state measured on the z-axis, aligning with foundational
  quantum mechanical principles and the empirical results from our Phase 3 analysis.

  Ground Truth: research/01_stern_gerlach_expected_results.md
  Analysis: analysis/01_stern_gerlach/
-/
import QBP.Basic

namespace QBP.Experiments.SternGerlach

open QBP

-- ### SETUP: Define the State and Observable ###

/-- The initial state: a particle with spin oriented along the +x axis.
    This is represented by the pure quaternion `i`. -/
def spinXState : Q := SPIN_X

/-- The measurement: spin along the z-axis.
    This is represented by the observable quaternion `k`. -/
def spinZObservable : Q := SPIN_Z

-- ### VERIFICATION: Confirm Properties of State and Observable ###

/-- The spin-x state is a valid pure quaternion as required by the axioms. -/
theorem spinXState_is_pure : isPureQuaternion spinXState := spin_x_is_pure

/-- The spin-z observable is a valid pure quaternion as required by the axioms. -/
theorem spinZObservable_is_pure : isPureQuaternion spinZObservable := spin_z_is_pure

-- ### CORE THEOREMS: Deriving the Experimental Outcome ###

/-- **Physical Principle:** The preparation (spin-x) is orthogonal to the measurement (spin-z).
    **Formal Proof:** This theorem demonstrates that the vector parts of the state and
    observable quaternions have a dot product of zero. This is the mathematical
    foundation for the 50/50 probability split. -/
theorem x_z_orthogonal : vecDot spinXState spinZObservable = 0 := by
  simp [vecDot, spinXState, spinZObservable, SPIN_X, SPIN_Z]

/-- **Physical Principle:** The average measurement outcome for an x-spin state
    measured on the z-axis is zero. This occurs because the particle is equally
    likely to be measured as spin-up or spin-down.
    **Formal Proof:** This is the main theorem for Experiment 1. It applies the general
    lemma `expectation_orthogonal_is_zero` to our specific state and observable,
    proving that their orthogonality necessarily leads to a zero expectation value.
    This result was empirically validated in our Phase 3 analysis. -/
theorem expectation_x_measured_z_is_zero :
    expectationValue spinXState spinZObservable = 0 :=
  expectation_orthogonal_is_zero spinXState spinZObservable
    spinXState_is_pure spinZObservable_is_pure x_z_orthogonal

/-- **Physical Principle:** The probability of measuring "spin-up" (+1) for an
    x-spin state on the z-axis is exactly 1/2.
    **Formal Proof:** This corollary directly follows from the zero expectation value.
    It provides the formal verification for the 50% probability observed in the
    real-world Stern-Gerlach experiment and our synthetic simulation. -/
theorem prob_up_x_measured_z_is_half :
    probUp spinXState spinZObservable = 1/2 :=
  prob_up_orthogonal_is_half spinXState spinZObservable
    spinXState_is_pure spinZObservable_is_pure x_z_orthogonal

/-- **Physical Principle:** The probability of measuring "spin-down" (-1) for an
    x-spin state on the z-axis is also exactly 1/2.
    **Formal Proof:** A simple corollary demonstrating the symmetric outcome,
    derived from the zero expectation value. -/
theorem prob_down_x_measured_z_is_half :
    probDown spinXState spinZObservable = 1/2 := by
  simp [probDown, expectation_x_measured_z_is_zero]

end QBP.Experiments.SternGerlach
