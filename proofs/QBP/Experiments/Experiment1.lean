-- This file contains the formal proofs for the Stern-Gerlach experiment (Experiment 1).
import QBP.Basic

open Quaternion

-- We define the spin state along the x-axis, which corresponds to our `ψ = i` state.
def spin_x_state : Quaternion ℝ := ⟨0, 1, 0, 0⟩

-- We define the observable for a z-axis measurement, which is `O = k`.
def spin_z_observable : Quaternion ℝ := ⟨0, 0, 0, 1⟩

-- We prove that the spin_x_state is a valid unit quaternion (fulfills Axiom 1).
theorem spin_x_is_unit : isUnitQuaternion spin_x_state := by
  simp [isUnitQuaternion, spin_x_state]

-- We prove that the spin_z_observable is a valid pure quaternion (fulfills Axiom 2).
theorem spin_z_is_pure : isPureQuaternion spin_z_observable := by
  simp [isPureQuaternion, spin_z_observable]

-- The Main Theorem for Experiment 1
-- This theorem proves that the expectation value of an x-aligned state
-- measured on the z-axis is 0. This is the formal verification of the
-- result that leads to the 50/50 probability split.
theorem expectation_value_of_orthogonal_states_is_zero :
  expectation_value spin_x_state spin_z_observable = 0 := by
  simp [expectation_value, get_state_vector, spin_x_state, spin_z_observable, star]
  simp [vec, dot_product]
  norm_num

-- End of formal proof for Experiment 1.
