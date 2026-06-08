/-
  QBP.Foundations.NormForm
  ========================

  The bilinear-form / norm-form row of the operations-complete property matrix
  (#474), at the 𝕆 / 𝕊 levels (`CDAlg ℝ 3`, `CDAlg ℝ 4`).  The ℝ/ℂ/ℍ cells live
  in `TowerLaws` on the Mathlib types (`ℝ`, `ℂ`, `ℍ[ℝ]`); this file discharges the
  two Cayley–Dickson-carrier columns and adds the cross-level guardrail.

  Scope (this file):
    * the polar bilinear form `bil x y = ∑ᵢ coordᵢ(x)·coordᵢ(y)` (reused from
      `OctonionLaws`, where it was introduced as the polar form of `N`):
      bilinearity, symmetry, and `N x = bil x x`.
    * **Two definitions agree.**  The coordinate form `bil x y` and the algebraic
      "conjugate" form `Re(x · x̄)` agree:  `bil x y = reCoord (x * conj y)` for
      EVERY `CDAlg R n` (general `n`, any `CommRing R`) — `bil_eq_reCoord_mul_conj`.
      This ties the matrix's `⟨x,y⟩ = Re(x·ȳ)` row (the convention used for ℝ/ℂ/ℍ
      in `TowerLaws`) to the sum-of-products form, and is restated explicitly at
      `n = 3` (𝕆) and `n = 4` (𝕊) over ℝ as the matrix cells.
    * **Positive-definiteness over ℝ:** `bil x x = N x = ∑ xᵢ² ≥ 0`, and
      `N x = 0 ↔ x = 0` (`N_eq_zero_iff`) — the form is a genuine Euclidean inner
      product on the `2^n`-dimensional real space.
    * **Norm composition cells:** ✓ at 𝕆 (`octonion_norm_form_composition`, cited
      from `OctonionLaws.octonion_norm_composition`), ✗ at 𝕊
      (`sedenion_norm_form_not_composition`, cited from
      `Breakdown.sedenion_norm_not_multiplicative`).

  ------------------------------------------------------------------------------
  D10 NON-IDENTIFICATION GUARDRAIL (scope-deliberation 2026-05-31 §5, guardrail 1;
  same convention as the `TowerLaws` `*_bilinear_form` / `*_norm_form` cells):

      `N` is the POSITIVE-DEFINITE ALGEBRAIC norm form of the composition algebra
      (sum of squares of coordinates, `bil x x`).  It is a EUCLIDEAN form —
      `N x ≥ 0` with equality iff `x = 0`.  It is **NOT** a spacetime metric and
      carries **no** Lorentzian / split signature.  No physical-metric, energy, or
      crystallisation semantics attach to `N` or `bil` here; any such identification
      is a separate, later, and explicitly-flagged modelling step.  The
      positive-definiteness theorem `N_eq_zero_iff` is the machine-checked witness
      that this form is Euclidean, not indefinite.
  ------------------------------------------------------------------------------

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom — every result depends only on
  `{propext, Classical.choice, Quot.sound}`.
-/
import QBP.Foundations.OctonionLaws
import QBP.Foundations.Breakdown

namespace QBP.Foundations.NormForm

open QBP.Foundations.CDAlg

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ## 1. The bilinear form: symmetry (bilinearity & `N = bil ·· ` are in `OctonionLaws`)

`bil`, `bil_def`, `N_eq_bil`, `bil_add_left/right`, `bil_smul_left/right`, `bil_e`
are all defined in `QBP.Foundations.CDAlg` (introduced in `OctonionLaws`).  We add
symmetry here and re-export the inner-product facts under stable matrix-cell names. -/

/-- **Symmetry of the bilinear form:** `⟨x,y⟩ = ⟨y,x⟩`. -/
theorem bil_symm (x y : CDAlg R n) : bil x y = bil y x := by
  simp only [bil_def]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The norm form is the diagonal of the bilinear form: `N x = ⟨x,x⟩`.  (Re-export
    of `CDAlg.N_eq_bil` under the matrix-cell name.) -/
theorem norm_form_eq_bil_diag (x : CDAlg R n) : N x = bil x x := N_eq_bil x

/-! ## 2. The two forms agree:  `⟨x,y⟩ = Re(x · x̄)`

This is the bridge between the coordinate sum-of-products definition of `bil` and
the algebraic conjugate form `Re(x·ȳ)` that the ℝ/ℂ/ℍ cells in `TowerLaws` use.
It holds for EVERY level `n` over any `CommRing` — a structural consequence of the
Cayley–Dickson sign data (`mulCoeff n i i = ±1`, `conj` flips imaginary signs),
not a numeric coincidence. -/

/-- **The coordinate form equals the conjugate form (general `n`).**
    `⟨x,y⟩ = ∑ᵢ xᵢyᵢ = (x · ȳ).coord 0 = Re(x · ȳ)`.

    Proof sketch: by `mul_coord_single` the real coordinate of `x·ȳ` is
    `∑ᵢ mulCoeff n i i · xᵢ · (ȳ)ᵢ`; since `mulCoeff n i i = +1` at `i=0` and `−1`
    otherwise, while `(ȳ)ᵢ = +yᵢ` at `i=0` and `−yᵢ` otherwise, every term collapses
    to `+xᵢyᵢ`. -/
theorem bil_eq_reCoord_mul_conj (x y : CDAlg R n) :
    bil x y = reCoord (x * conj y) := by
  rw [reCoord, mul_coord_single]
  simp only [xor_zero_right, bil_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulCoeff_self, conj_coord]
  by_cases hi : i.val = 0
  · -- real coordinate: mulCoeff = 1, conj fixes the coordinate
    simp only [hi, if_true]; push_cast; ring
  · -- imaginary coordinate: (−1) · xᵢ · (−yᵢ) = xᵢ yᵢ
    simp only [hi, if_false]; push_cast; ring

/-- **𝕆 cell — the bilinear form as `Re(x·x̄)`.**  At `n = 3` over ℝ, the octonion
    inner product `⟨x,y⟩ = ∑ᵢ xᵢyᵢ` equals `Re(x · x̄)` (the convention the ℝ/ℂ/ℍ
    `TowerLaws` cells use).  Algebraic norm form, NOT a spacetime metric — see the
    D10 guardrail in this file's header. -/
theorem octonion_bilinear_form (x y : CDAlg ℝ 3) :
    bil x y = reCoord (x * conj y) := bil_eq_reCoord_mul_conj x y

/-- **𝕊 cell — the bilinear form as `Re(x·x̄)`.**  At `n = 4` over ℝ, the sedenion
    inner product `⟨x,y⟩ = ∑ᵢ xᵢyᵢ` equals `Re(x · x̄)`.  Positive-definite
    algebraic form, NOT a spacetime metric — see the D10 guardrail. -/
theorem sedenion_bilinear_form (x y : CDAlg ℝ 4) :
    bil x y = reCoord (x * conj y) := bil_eq_reCoord_mul_conj x y

/-! ## 3. Positive-definiteness over ℝ

`N x = ∑ᵢ xᵢ² ≥ 0`, with equality iff every coordinate is `0`, i.e. `x = 0`.  This
is the EUCLIDEAN-signature witness (the D10 guardrail's machine-checked content). -/

/-- `N x = ⟨x,x⟩ ≥ 0` over ℝ (the form is positive-semidefinite). -/
theorem N_nonneg (x : CDAlg ℝ n) : 0 ≤ N x := by
  rw [N_def]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **Positive-definiteness:** `N x = 0 ↔ x = 0` over ℝ.  The algebraic norm form is
    a genuine (positive-definite) Euclidean inner product on `ℝ^(2^n)`; in
    particular it has Euclidean — not Lorentzian — signature.  (D10 guardrail
    witness.) -/
theorem N_eq_zero_iff (x : CDAlg ℝ n) : N x = 0 ↔ x = 0 := by
  rw [N_def]
  constructor
  · intro h
    -- a sum of squares is 0 ⟹ each square is 0 ⟹ each coordinate is 0
    have hterm : ∀ i ∈ Finset.univ, (x.coord i)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp h
    ext i
    have : (x.coord i)^2 = 0 := hterm i (Finset.mem_univ i)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · rintro rfl
    simp

/-- `⟨x,x⟩ = 0 ↔ x = 0` over ℝ — positive-definiteness in inner-product form. -/
theorem bil_self_eq_zero_iff (x : CDAlg ℝ n) : bil x x = 0 ↔ x = 0 := by
  rw [← N_eq_bil]; exact N_eq_zero_iff x

/-! ## 4. Norm-composition cells (the multiplicative-norm row at 𝕆 / 𝕊)

The composition-algebra property `N(x·y) = N x · N y`.  ✓ at 𝕆 (Hurwitz), ✗ at 𝕊
(the failure that marks 𝕊 as the first non-composition level). -/

/-- **✓ norm composition at 𝕆** (Hurwitz multiplicativity).  `N(x·y) = N x · N y`
    on 𝕆 = `CDAlg ℝ 3`.  Cited from `OctonionLaws.octonion_norm_composition` (the
    quadrilinear bilinear-form polarization); restated here under the norm-form
    matrix-cell name. -/
theorem octonion_norm_form_composition (x y : CDAlg ℝ 3) : N (x * y) = N x * N y :=
  QBP.Foundations.CDAlg.octonion_norm_composition x y

/-- **✗ norm composition at 𝕊.**  `N` is NOT multiplicative on 𝕊 = `CDAlg ℝ 4`:
    `∃ x y, N(x·y) ≠ N x · N y` (a zero-divisor pair gives `N(x·y) = 0` while
    `N x · N y = 4`).  Cited from `Breakdown.sedenion_norm_not_multiplicative`.
    This is WHY the composition-algebra ladder stops at 𝕆 — and (cf.
    `CrossProduct`) why there is no 7D-style cross product at 𝕊. -/
theorem sedenion_norm_form_not_composition :
    ∃ x y : CDAlg ℝ 4, N (x * y) ≠ N x * N y :=
  QBP.Foundations.Breakdown.sedenion_norm_not_multiplicative

/-! ## 5. Completeness audit — `#print axioms` -/

#print axioms bil_symm
#print axioms bil_eq_reCoord_mul_conj
#print axioms octonion_bilinear_form
#print axioms sedenion_bilinear_form
#print axioms N_nonneg
#print axioms N_eq_zero_iff
#print axioms bil_self_eq_zero_iff
#print axioms octonion_norm_form_composition
#print axioms sedenion_norm_form_not_composition

end QBP.Foundations.NormForm
