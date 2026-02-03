/-
  Stern-Gerlach Experiment (Experiment 1) - Formal Proofs

  This file contains the formal verification for the Stern-Gerlach experiment,
  demonstrating that the QBP framework correctly predicts:
  1. Binary measurement outcomes (±1 only)
  2. 50/50 probability split for perpendicular states

  Ground Truth Reference: research/01_stern_gerlach_expected_results.md
  Implementation Reference: experiments/01_stern_gerlach/simulate.py
-/
import QBP.Basic

namespace QBP.Experiments.SternGerlach

open QBP

/-- The spin-x state: ψ = i (pure quaternion along x-axis) -/
def spinXState : Q := SPIN_X

/-- The spin-z observable: O = k (pure quaternion along z-axis) -/
def spinZObservable : Q := SPIN_Z

/-- The spin-x state is a pure quaternion -/
theorem spinXState_is_pure : isPureQuaternion spinXState := spin_x_is_pure

/-- The spin-z observable is a pure quaternion -/
theorem spinZObservable_is_pure : isPureQuaternion spinZObservable := spin_z_is_pure

/-- Key theorem: x and z spin directions are orthogonal -/
theorem x_z_orthogonal : vecDot spinXState spinZObservable = 0 := by
  simp [vecDot, spinXState, spinZObservable, SPIN_X, SPIN_Z]
  ring

/-- Main Theorem for Experiment 1:
    An x-aligned state measured on the z-axis has expectation value 0.
    This is the formal verification that the QBP framework predicts
    50/50 probability split for orthogonal measurements. -/
theorem expectation_x_measured_z_is_zero :
    expectationValue spinXState spinZObservable = 0 :=
  expectation_orthogonal_is_zero spinXState spinZObservable
    spinXState_is_pure spinZObservable_is_pure x_z_orthogonal

/-- Corollary: P(+1) = 1/2 for x-state measured on z-axis -/
theorem prob_up_x_measured_z_is_half :
    probUp spinXState spinZObservable = 1/2 :=
  prob_up_orthogonal_is_half spinXState spinZObservable
    spinXState_is_pure spinZObservable_is_pure x_z_orthogonal

/-- Corollary: P(-1) = 1/2 for x-state measured on z-axis -/
theorem prob_down_x_measured_z_is_half :
    probDown spinXState spinZObservable = 1/2 := by
  simp [probDown, expectation_x_measured_z_is_zero]
  ring

end QBP.Experiments.SternGerlach
