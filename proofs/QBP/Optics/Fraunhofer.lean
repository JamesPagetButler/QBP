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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

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

/-! ## Single-slit diffraction envelope (sinc²)

The intensity formula `fraunhoferIntensity` above models only the two-slit
*interference* term `cos²(πdx/λL)`, valid in the limit of infinitely narrow
slits. For slits of finite width `a`, each slit also produces a single-slit
*diffraction* envelope `sinc²(πax/λL)` that modulates the fringe pattern,
suppressing fringes at large off-axis angles. The full Fraunhofer intensity is
the product of the two:

  I(x) = I₀ · cos²(πdx/λL) · sinc²(πax/λL)

We reuse Mathlib's `Real.sinc x = sin x / x` (with the removable singularity
filled as `sinc 0 = 1`), so the envelope is well-defined at `x = 0` where the
naive `sin/x` would be `0/0`. Issue #374. -/

/-- Full Fraunhofer double-slit intensity for slits of finite width `a`:
    the interference term `cos²(πdx/λL)` modulated by the single-slit
    diffraction envelope `sinc²(πax/λL)`.

    I(x) = I₀ · cos²(π·d·x / (λ·L)) · sinc²(π·a·x / (λ·L))

    `a` is the slit width, `d` the slit separation, `wl` the wavelength,
    `L` the propagation distance, `I₀` the peak intensity. -/
noncomputable def fraunhoferIntensityFull (I₀ d a wl L x : ℝ) : ℝ :=
  I₀ * (Real.cos (Real.pi * d * x / (wl * L))) ^ 2
     * (Real.sinc (Real.pi * a * x / (wl * L))) ^ 2

/-- The full intensity factorises as the narrow-slit interference intensity
    `fraunhoferIntensity` times the single-slit envelope `sinc²(πax/λL)`.
    This is the precise sense in which the new definition *extends* the old
    one without changing it: dropping the envelope (or setting it to 1)
    recovers `fraunhoferIntensity`. -/
theorem fraunhoferIntensityFull_factor (I₀ d a wl L x : ℝ) :
    fraunhoferIntensityFull I₀ d a wl L x =
      fraunhoferIntensity I₀ d wl L x *
        (Real.sinc (Real.pi * a * x / (wl * L))) ^ 2 := by
  unfold fraunhoferIntensityFull fraunhoferIntensity
  ring

/-- On-axis (`x = 0`) the diffraction envelope is `sinc²(0) = 1`, so the full
    intensity reduces exactly to the interference-only intensity, which is the
    peak `I₀`. This is the limiting consistency check between the two models. -/
theorem fraunhoferIntensityFull_at_zero (I₀ d a wl L : ℝ) :
    fraunhoferIntensityFull I₀ d a wl L 0 = fraunhoferIntensity I₀ d wl L 0 := by
  rw [fraunhoferIntensityFull_factor]
  have hsinc : Real.pi * a * 0 / (wl * L) = 0 := by ring
  rw [hsinc, Real.sinc_zero]
  ring

/-- When the slit width `a = 0` (idealised infinitely narrow slits), the
    envelope argument is identically zero, `sinc²(0) = 1`, and the full model
    collapses to the original narrow-slit `fraunhoferIntensity` for every `x`.
    This recovers the exact pre-existing definition as the `a → 0` limit. -/
theorem fraunhoferIntensityFull_slit_width_zero (I₀ d wl L x : ℝ) :
    fraunhoferIntensityFull I₀ d 0 wl L x = fraunhoferIntensity I₀ d wl L x := by
  rw [fraunhoferIntensityFull_factor]
  have hsinc : Real.pi * 0 * x / (wl * L) = 0 := by ring
  rw [hsinc, Real.sinc_zero]
  ring

/-- The single-slit envelope only attenuates: for non-negative peak intensity
    `I₀ ≥ 0`, the full intensity never exceeds the interference-only intensity,
    because `0 ≤ sinc² ≤ 1` and `cos² ≥ 0`. Physically, finite slit width can
    only suppress fringe brightness off-axis, never amplify it. -/
theorem fraunhoferIntensityFull_le (I₀ d a wl L x : ℝ) (hI₀ : 0 ≤ I₀) :
    fraunhoferIntensityFull I₀ d a wl L x ≤ fraunhoferIntensity I₀ d wl L x := by
  rw [fraunhoferIntensityFull_factor]
  have hbase : 0 ≤ fraunhoferIntensity I₀ d wl L x := by
    unfold fraunhoferIntensity
    exact mul_nonneg hI₀ (sq_nonneg _)
  have hsinc_le : (Real.sinc (Real.pi * a * x / (wl * L))) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨Real.neg_one_le_sinc _, Real.sinc_le_one _⟩
  calc fraunhoferIntensity I₀ d wl L x *
          (Real.sinc (Real.pi * a * x / (wl * L))) ^ 2
        ≤ fraunhoferIntensity I₀ d wl L x * 1 := by
          exact mul_le_mul_of_nonneg_left hsinc_le hbase
    _ = fraunhoferIntensity I₀ d wl L x := mul_one _

/-- The full Fraunhofer intensity is non-negative for non-negative peak
    intensity `I₀ ≥ 0` (it is a product of `I₀ ≥ 0`, `cos² ≥ 0`, `sinc² ≥ 0`). -/
theorem fraunhoferIntensityFull_nonneg (I₀ d a wl L x : ℝ) (hI₀ : 0 ≤ I₀) :
    0 ≤ fraunhoferIntensityFull I₀ d a wl L x := by
  unfold fraunhoferIntensityFull
  exact mul_nonneg (mul_nonneg hI₀ (sq_nonneg _)) (sq_nonneg _)

end QBP.Optics.Fraunhofer
