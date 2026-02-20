/-
  Standard Optics: Fraunhofer Far-Field Diffraction

  Standard wave optics results for double-slit Fraunhofer diffraction.
  These are NOT QBP-specific — they are classical results that follow from
  the Schrödinger equation via Fourier optics.

  Separated from the QBP experiment proofs because:
  1. They are standard physics, not quaternionic predictions
  2. The QBP proof chain (DoubleSlit.lean §1→§9) does not depend on them
  3. They will be consumed by the Gap Theorem (Sprint 8): once we prove
     QBP → Standard QM, these formulas follow automatically

  The Float oracle (QBP.Oracle.FloatCompute) maintains independent
  computable mirrors of these definitions for differential testing.

  Ground Truth: research/03_double_slit_expected_results.md (Section 5)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QBP.Optics.Fraunhofer

open Real

/-- Fraunhofer intensity at position x with slit separation d, wavelength λ,
    propagation distance L, and peak intensity I₀.
    I(x) = I₀ · cos²(π·d·x / (λ·L)) -/
noncomputable def fraunhoferIntensity (I₀ d wl L x : ℝ) : ℝ :=
  I₀ * (Real.cos (Real.pi * d * x / (wl * L))) ^ 2

/-- Fringe spacing: Δx = λ·L / d -/
noncomputable def fringeSpacing (wl L d : ℝ) : ℝ := wl * L / d

/-- At a maximum (x = n·λ·L/d for integer n), cos(nπ)² = 1, so I = I₀ -/
theorem intensity_at_maximum (I₀ d wl L : ℝ) (n : ℤ)
    (hwlL : wl * L ≠ 0) (hd : d ≠ 0) :
    fraunhoferIntensity I₀ d wl L (n * (wl * L / d)) = I₀ := by
  unfold fraunhoferIntensity
  have hwl : wl ≠ 0 := left_ne_zero_of_mul hwlL
  have hL : L ≠ 0 := right_ne_zero_of_mul hwlL
  have h : Real.pi * d * (↑n * (wl * L / d)) / (wl * L) = ↑n * Real.pi := by
    field_simp
  rw [h]
  have hcos2 : Real.cos (↑n * Real.pi) ^ 2 = 1 := by
    have h1 := Real.sin_sq_add_cos_sq (↑n * Real.pi)
    have h2 : Real.sin (↑n * Real.pi) = 0 := Real.sin_int_mul_pi n
    nlinarith [sq_nonneg (Real.sin (↑n * Real.pi))]
  rw [hcos2]; ring

/-- At a minimum (x = (n + 1/2)·λ·L/d), cos((n+1/2)π)² = 0, so I = 0 -/
theorem intensity_at_minimum (I₀ d wl L : ℝ) (n : ℤ)
    (hwlL : wl * L ≠ 0) (hd : d ≠ 0) :
    fraunhoferIntensity I₀ d wl L ((n + 1/2) * (wl * L / d)) = 0 := by
  unfold fraunhoferIntensity
  have hwl : wl ≠ 0 := left_ne_zero_of_mul hwlL
  have hL : L ≠ 0 := right_ne_zero_of_mul hwlL
  have h : Real.pi * d * ((↑n + 1 / 2) * (wl * L / d)) / (wl * L) =
           (↑n + 1 / 2) * Real.pi := by
    field_simp
  rw [h]
  have hcos : Real.cos ((↑n + 1 / 2) * Real.pi) = 0 := by
    rw [show (↑n + 1 / 2) * Real.pi = ↑n * Real.pi + Real.pi / 2 by ring]
    rw [Real.cos_add]
    have h1 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    have h2 : Real.sin (↑n * Real.pi) = 0 := Real.sin_int_mul_pi n
    rw [h1, h2]; ring
  rw [hcos]; simp

/-- Fringe spacing scales linearly with wavelength -/
theorem fringeSpacing_linear_lambda (L d c : ℝ) (wl : ℝ) :
    fringeSpacing (c * wl) L d = c * fringeSpacing wl L d := by
  unfold fringeSpacing; ring

/-- Fringe spacing scales linearly with propagation distance -/
theorem fringeSpacing_linear_L (wl d c : ℝ) (L : ℝ) :
    fringeSpacing wl (c * L) d = c * fringeSpacing wl L d := by
  unfold fringeSpacing; ring

/-- Fringe spacing scales inversely with slit separation -/
theorem fringeSpacing_inverse_d (wl L d : ℝ) (hd : d ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    fringeSpacing wl L (c * d) = fringeSpacing wl L d / c := by
  unfold fringeSpacing
  field_simp

end QBP.Optics.Fraunhofer
