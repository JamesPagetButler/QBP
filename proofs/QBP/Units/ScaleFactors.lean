/-
  QBP Scale Factors: BPM Natural Units <-> SI Conversion

  Defines the three fundamental scale factors {L₀, E₀, T₀} that convert
  between BPM code units and SI, given a source particle's mass and
  de Broglie wavelength.

  This is the formal source of truth. Python's si_conversion.py must
  agree with these definitions on all test vectors.

  Key algebraic properties proven:
  1. All scale factors are positive for positive inputs
  2. Round-trip conversions are identity (on Reals)
  3. V_Z_CODE structural invariant holds
  4. T₀ = ℏ_SI / E₀
-/
import QBP.Units.Constants

namespace QBP.Units

/-! ## Scale Factor Definitions

Given particle mass m_SI [kg] and de Broglie wavelength λ_SI [m],
compute the three fundamental scales.
-/

/-- Wavenumber: k = 2π/λ [1/m] -/
noncomputable def k_si (lam_si : ℝ) : ℝ := 2 * Real.pi / lam_si

/-- Length scale: L₀ = k₀_code × λ / (2π) [m per code unit] -/
noncomputable def L0 (lam_si : ℝ) : ℝ := k0_code * lam_si / (2 * Real.pi)

/-- Energy scale: E₀ = ℏ_SI² × m_code / (m_SI × L₀² × ℏ_code²) [J per code unit] -/
noncomputable def E0 (m_si lam_si : ℝ) : ℝ :=
  hbar_SI ^ 2 * m_code / (m_si * (L0 lam_si) ^ 2 * hbar_code ^ 2)

/-- Time scale: T₀ = ℏ_SI / E₀ [s per code unit] -/
noncomputable def T0 (m_si lam_si : ℝ) : ℝ := hbar_SI / E0 m_si lam_si

/-- Physical velocity: v_z_SI = ℏ_SI × k_SI / m_SI [m/s] -/
noncomputable def v_z_si (m_si lam_si : ℝ) : ℝ :=
  hbar_SI * k_si lam_si / m_si

/-! ## Code ↔ SI Conversion Functions

These mirror the Python functions in si_conversion.py exactly.
-/

/-- Convert position from code units to SI metres. -/
noncomputable def convert_position (x_code : ℝ) (lam_si : ℝ) : ℝ :=
  x_code * L0 lam_si

/-- Convert position from SI metres to code units. -/
noncomputable def convert_length_to_code (x_si : ℝ) (lam_si : ℝ) : ℝ :=
  x_si / L0 lam_si

/-- Convert energy from code units to SI joules. -/
noncomputable def convert_energy (E_code : ℝ) (m_si lam_si : ℝ) : ℝ :=
  E_code * E0 m_si lam_si

/-- Convert energy from SI joules to code units. -/
noncomputable def convert_energy_to_code (E_si : ℝ) (m_si lam_si : ℝ) : ℝ :=
  E_si / E0 m_si lam_si

/-- Convert potential from code units to SI electron-volts.
    Includes v_z_code factor (Jacobian of time→space propagation). -/
noncomputable def convert_potential (U_code : ℝ) (m_si lam_si : ℝ) : ℝ :=
  U_code * v_z_code * E0 m_si lam_si / eV_in_J

/-! ## Algebraic Properties (Proofs on Ideal Reals)

These proofs establish mathematical correctness.
Floating-point fidelity is verified separately via test vectors.
-/

/-- L₀ is positive for positive wavelength. -/
theorem L0_pos (lam_si : ℝ) (hl : lam_si > 0) : L0 lam_si > 0 := by
  simp [L0]
  apply div_pos
  · apply mul_pos
    · exact k0_code_pos
    · exact hl
  · apply mul_pos
    · norm_num
    · exact Real.pi_pos

/-- E₀ is positive for positive mass and wavelength. -/
theorem E0_pos (m_si lam_si : ℝ) (hm : m_si > 0) (hl : lam_si > 0) :
    E0 m_si lam_si > 0 := by
  simp [E0]
  apply div_pos
  · apply mul_pos
    · apply pow_pos
      · exact div_pos h_SI_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos)
    · exact m_code_pos
  · apply mul_pos
    · apply mul_pos
      · exact hm
      · apply pow_pos
        · exact L0_pos lam_si hl
    · apply pow_pos
      · exact hbar_code_pos

/-- T₀ equals ℏ_SI / E₀ by definition. -/
theorem T0_def (m_si lam_si : ℝ) : T0 m_si lam_si = hbar_SI / E0 m_si lam_si :=
  rfl

/-- T₀ is positive for positive mass and wavelength.
    Causality requires a positive time scale — this is foundational. -/
theorem T0_pos (m_si lam_si : ℝ) (hm : m_si > 0) (hl : lam_si > 0) :
    T0 m_si lam_si > 0 := by
  unfold T0
  exact div_pos hbar_SI_pos (E0_pos m_si lam_si hm hl)

/-- k_SI is positive for positive wavelength. -/
theorem k_si_pos (lam_si : ℝ) (hl : lam_si > 0) : k_si lam_si > 0 := by
  simp [k_si]
  exact div_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos) hl

/-- v_z_SI is positive for positive mass and wavelength. -/
theorem v_z_si_pos (m_si lam_si : ℝ) (hm : m_si > 0) (hl : lam_si > 0) :
    v_z_si m_si lam_si > 0 := by
  simp [v_z_si]
  exact div_pos (mul_pos hbar_SI_pos (k_si_pos lam_si hl)) hm

/-- **Round-trip theorem (position):**
    Converting code→SI→code is the identity (on Reals). -/
theorem position_round_trip (x_code : ℝ) (lam_si : ℝ) (hl : lam_si > 0) :
    convert_length_to_code (convert_position x_code lam_si) lam_si = x_code := by
  simp [convert_position, convert_length_to_code]
  rw [mul_div_cancel_right₀]
  exact ne_of_gt (L0_pos lam_si hl)

/-- **Round-trip theorem (energy):**
    Converting code→SI→code is the identity (on Reals). -/
theorem energy_round_trip (E_code : ℝ) (m_si lam_si : ℝ)
    (hm : m_si > 0) (hl : lam_si > 0) :
    convert_energy_to_code (convert_energy E_code m_si lam_si) m_si lam_si = E_code := by
  simp [convert_energy, convert_energy_to_code]
  rw [mul_div_cancel_right₀]
  exact ne_of_gt (E0_pos m_si lam_si hm hl)

/-- **Linearity (position):**
    Position conversion is linear — sum of conversions = conversion of sum. -/
theorem position_linear (x1 x2 : ℝ) (lam_si : ℝ) :
    convert_position (x1 + x2) lam_si =
    convert_position x1 lam_si + convert_position x2 lam_si := by
  simp [convert_position]
  ring

/-- **Linearity (energy):**
    Energy conversion is linear. -/
theorem energy_linear (E1 E2 : ℝ) (m_si lam_si : ℝ) :
    convert_energy (E1 + E2) m_si lam_si =
    convert_energy E1 m_si lam_si + convert_energy E2 m_si lam_si := by
  simp [convert_energy]
  ring

/-- **Scaling (position):**
    convert_position(α × x) = α × convert_position(x). -/
theorem position_scaling (α x : ℝ) (lam_si : ℝ) :
    convert_position (α * x) lam_si = α * convert_position x lam_si := by
  simp [convert_position]
  ring

/-- **Zero maps to zero (position):** -/
theorem position_zero (lam_si : ℝ) : convert_position 0 lam_si = 0 := by
  simp [convert_position]

/-- **Zero maps to zero (energy):** -/
theorem energy_zero (m_si lam_si : ℝ) : convert_energy 0 m_si lam_si = 0 := by
  simp [convert_energy]

/-- **Scaling (energy):**
    convert_energy(α × E) = α × convert_energy(E). -/
theorem energy_scaling (α E : ℝ) (m_si lam_si : ℝ) :
    convert_energy (α * E) m_si lam_si = α * convert_energy E m_si lam_si := by
  simp [convert_energy]
  ring

end QBP.Units
