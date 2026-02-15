/-
  QBP SI Constants and BPM Code Parameters

  This module defines physical constants and BPM natural-unit parameters
  as the formal source of truth for all unit conversions.

  Physical constants use exact 2019 SI redefinition values.
  BPM code parameters are rational by construction.

  Layer 1: Standard BPM natural units <-> SI (ESTABLISHED)
  Layer 2: Quaternionic derived quantities (MODEL-DEPENDENT)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QBP.Units

/-! ## 2019 SI Exact Constants

The 2019 SI redefinition fixes h, e, k_B, N_A as exact decimal numbers.
We represent these as exact rationals in Lean (numerator / 10^n).
-/

/-- Planck constant: h = 6.62607015 × 10⁻³⁴ J⋅s (exact, 2019 SI) -/
noncomputable def h_SI : ℝ := (662607015 : ℝ) / (10 ^ 42 : ℝ)

/-- Elementary charge: e = 1.602176634 × 10⁻¹⁹ C (exact, 2019 SI) -/
noncomputable def e_SI : ℝ := (1602176634 : ℝ) / (10 ^ 28 : ℝ)

/-- Speed of light: c = 299792458 m/s (exact, defines the metre) -/
def c_SI : ℕ := 299792458

/-- Reduced Planck constant: ℏ = h / (2π) -/
noncomputable def hbar_SI : ℝ := h_SI / (2 * Real.pi)

/-- eV in joules: 1 eV = e × 1 V = 1.602176634 × 10⁻¹⁹ J (exact)
    Same value as e_SI because 1 eV = 1 elementary charge × 1 volt. -/
noncomputable def eV_in_J : ℝ := (1602176634 : ℝ) / (10 ^ 28 : ℝ)

/-! ## BPM Code Parameters

Standard natural unit convention for the Beam Propagation Method.
All are exact rationals.
-/

/-- BPM ℏ_code = 1 (natural units) -/
noncomputable def hbar_code : ℝ := 1

/-- BPM effective mass m_code = 1/2 (standard BPM convention) -/
noncomputable def m_code : ℝ := 1 / 2

/-- BPM reference wavenumber k₀_code = 20 -/
noncomputable def k0_code : ℝ := 20

/-! ## Structural Invariant: V_Z_CODE

The velocity v_z in code units is the Jacobian of the time→space
propagation transformation. This value is absorbed into every
potential term in the BPM split-step algorithm.

If this invariant breaks, the BPM violates unitarity.
-/

/-- v_z in code units: ℏ_code × k₀_code / m_code -/
noncomputable def v_z_code : ℝ := hbar_code * k0_code / m_code

/-- **Theorem:** V_Z_CODE = 40 exactly. -/
theorem v_z_code_eq_40 : v_z_code = 40 := by
  simp [v_z_code, hbar_code, m_code, k0_code]
  norm_num

/-- **Theorem:** V_Z_CODE is positive. -/
theorem v_z_code_pos : v_z_code > 0 := by
  rw [v_z_code_eq_40]
  norm_num

/-! ## Positivity of SI Constants

These are needed for downstream proofs about scale factor positivity.
-/

/-- h_SI is positive. -/
theorem h_SI_pos : h_SI > 0 := by
  unfold h_SI
  positivity

/-- e_SI is positive. -/
theorem e_SI_pos : e_SI > 0 := by
  unfold e_SI
  positivity

/-- eV_in_J is positive. -/
theorem eV_in_J_pos : eV_in_J > 0 := by
  unfold eV_in_J
  positivity

/-- hbar_code is positive. -/
theorem hbar_code_pos : hbar_code > 0 := by
  norm_num [hbar_code]

/-- m_code is positive. -/
theorem m_code_pos : m_code > 0 := by
  norm_num [m_code]

/-- k0_code is positive. -/
theorem k0_code_pos : k0_code > 0 := by
  norm_num [k0_code]

/-- ℏ_SI is positive: h/(2π) > 0 since h > 0 and π > 0. -/
theorem hbar_SI_pos : hbar_SI > 0 := by
  simp [hbar_SI]
  exact div_pos h_SI_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos)

end QBP.Units
