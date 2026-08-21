/-
  QBP.Foundations.SpectralMoments — f₀/f₂/f₄ moments + the CCvS γ(−a) formula
  ===========================================================================

  Anchor for #466 item 7 (paper §VIII.B, §IX.B; PR4).  Two clusters:

  **A. Profile-function moments (§VIII.B).**  The spectral action
  `Tr f(D²/Λ²)` expands in moments of the profile function `f(u)`.  The
  provable algebraic core is the Λ-scaling: replacing `f(u)` by the dilated
  profile `f(u/Λ²)` scales the `m`-th moment `∫₀^∞ f(u)·u^m du` by `Λ^(2(m+1))`
  and leaves `f(0)` untouched.  This is exactly the claimed hierarchy
    f₄ ↔ Λ⁴  (m = 1),   f₂ ↔ Λ²  (m = 0),   f₀ = f(0) ↔ Λ⁰,
  under the standard Chamseddine–Connes moment convention
    f₄ = ∫ f(u) u du,  f₂ = ∫ f(u) du,  f₀ = f(0).

  CONVENTION NOTE (surfaced, not silently fixed): paper §VIII.B currently
  *defines* `f_k = ∫₀^∞ f(u) u^(k-1) du`, which is inconsistent with the
  paper's own scaling attribution (it would give f₂ ↔ Λ⁴) and with the CC
  convention above.  We therefore state the moments with the exponent `m`
  explicit (`profileMoment f m`), so the theorems are convention-robust; the
  k-indexing of the paper needs an erratum (see the ESCALATE item in the
  #466 report).

  **B. CCvS entropy coefficients (§IX.B).**  CCvS 2018 (arXiv:1809.02944)
  derive, for integer a ≥ 1,
      γ(−a) = (2^(2a) − 1)/(a·2^(2a)) · (2a+1)!/(a−1)! · ζ(2a+1).
  The provable arithmetic: the rational pre-factor evaluates to 9/2, 225/4,
  6615/8 at a = 1, 2, 3 (225/4 is the value CCvS print for γ(−2)), and its
  numerator `2^(2a) − 1` is EXACTLY the imaginary dimension of the level-2a
  Cayley–Dickson algebra (`CDDimension.even_tower_imDim`) — the even-tower
  confluence.  ζ is kept abstract (any assignment `zeta : ℕ → ℝ` of values to
  odd arguments); no analytic claim about ζ is made or needed for these
  identities.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import QBP.Foundations.CDDimension

namespace QBP.Foundations.SpectralMoments

open MeasureTheory Set Module

/-! ## A. Profile-function moments and their Λ-scaling -/

/-- The `m`-th moment of a profile function: `∫₀^∞ f(u) · u^m du`.
    Chamseddine–Connes dictionary (4 dimensions): `f₄ = profileMoment f 1`,
    `f₂ = profileMoment f 0`, and `f₀ = f 0` (not a moment). -/
noncomputable def profileMoment (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∫ u in Ioi (0:ℝ), f u * u ^ m

/-- **Λ-scaling of the moments.**  Dilating the profile by `c > 0`
    (`u ↦ f(u/c)`; in the spectral action `c = Λ²`) scales the `m`-th moment
    by `c^(m+1)`:
      `∫ f(u/c) u^m du = c^(m+1) · ∫ f(u) u^m du`.
    No integrability hypothesis is needed: the substitution `u = c·v` is an
    exact measure-theoretic identity (both sides vanish together in the
    non-integrable case). -/
theorem profileMoment_dilate (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    profileMoment (fun u => f (u / c)) m = c ^ (m + 1) * profileMoment f m := by
  unfold profileMoment
  have h := integral_comp_mul_left_Ioi
      (fun u => f (u / c) * u ^ m) 0 hc
  rw [mul_zero] at h
  simp only [mul_div_cancel_left₀ _ hc.ne', mul_pow] at h
  have hcomm : (fun x : ℝ => f x * (c ^ m * x ^ m))
      = fun x : ℝ => c ^ m * (f x * x ^ m) := by
    funext x; ring
  rw [hcomm, integral_const_mul, smul_eq_mul] at h
  have hint : (∫ u in Ioi (0:ℝ), f (u / c) * u ^ m)
      = c * (c ^ m * ∫ x in Ioi (0:ℝ), f x * x ^ m) := by
    have hc' : c ≠ 0 := hc.ne'
    field_simp at h ⊢
    linarith [h]
  rw [hint, pow_succ]
  ring

/-- **f₄ ↔ Λ⁴** (m = 1, c = Λ²): the cosmological-constant moment
    `∫ f(u) u du` picks up `(Λ²)² = Λ⁴` under dilation. -/
theorem f4_scaling (f : ℝ → ℝ) {Λ : ℝ} (hΛ : 0 < Λ) :
    profileMoment (fun u => f (u / Λ^2)) 1 = Λ^4 * profileMoment f 1 := by
  have h := profileMoment_dilate f (c := Λ^2) (by positivity) 1
  rw [h]
  ring_nf

/-- **f₂ ↔ Λ²** (m = 0, c = Λ²): the Einstein–Hilbert moment `∫ f(u) du`
    picks up `Λ²` under dilation. -/
theorem f2_scaling (f : ℝ → ℝ) {Λ : ℝ} (hΛ : 0 < Λ) :
    profileMoment (fun u => f (u / Λ^2)) 0 = Λ^2 * profileMoment f 0 := by
  have h := profileMoment_dilate f (c := Λ^2) (by positivity) 0
  rw [h]
  ring_nf

/-- **f₀ ↔ Λ⁰**: the gauge-coupling coefficient `f(0)` is scale-invariant —
    dilation does not move the origin. -/
theorem f0_invariant (f : ℝ → ℝ) (c : ℝ) :
    (fun u => f (u / c)) 0 = f 0 := by
  simp

/-- The scaling *hierarchy* f₄ : f₂ = Λ⁴ : Λ² — the ratio of the two moment
    scalings is itself Λ², independent of the profile. -/
theorem moment_scaling_ratio {Λ : ℝ} (hΛ : 0 < Λ) :
    (Λ^4 : ℝ) / Λ^2 = Λ^2 := by
  have h2 : (Λ:ℝ)^2 ≠ 0 := by positivity
  field_simp

/-! ## B. The CCvS γ(−a) coefficients and the even Cayley–Dickson tower -/

/-- The rational (algebraic) pre-factor of the CCvS entropy coefficient:
      `pref(a) = (2^(2a) − 1)/(a·2^(2a)) · (2a+1)!/(a−1)!`
    so that `γ(−a) = pref(a) · ζ(2a+1)`.  Meaningful for `a ≥ 1`. -/
def ccvsPrefactor (a : ℕ) : ℚ :=
  ((2^(2*a) - 1 : ℚ) / (a * 2^(2*a))) *
    ((Nat.factorial (2*a + 1) : ℚ) / (Nat.factorial (a - 1) : ℚ))

/-- a = 1 (level 2, ℍ): `pref(1) = (3/4)·3! = 9/2`, so γ(−1) = (9/2)ζ(3). -/
theorem ccvsPrefactor_one : ccvsPrefactor 1 = 9 / 2 := by
  unfold ccvsPrefactor
  norm_num [Nat.factorial]

/-- a = 2 (level 4, 𝕊): `pref(2) = (15/32)·5! = 225/4` — exactly the value
    CCvS print: γ(−2) = (225/4)ζ(5) ≈ 58.33. -/
theorem ccvsPrefactor_two : ccvsPrefactor 2 = 225 / 4 := by
  unfold ccvsPrefactor
  norm_num [Nat.factorial]

/-- a = 3 (level 6, 64-dim CD algebra): `pref(3) = (63/192)·(7!/2!) = 6615/8`,
    so γ(−3) = (6615/8)ζ(7). -/
theorem ccvsPrefactor_three : ccvsPrefactor 3 = 6615 / 8 := by
  unfold ccvsPrefactor
  norm_num [Nat.factorial]

/-- The CCvS entropy coefficient γ(−a), with the odd zeta values kept
    abstract (`zeta j` stands for ζ(j); no analytic property of ζ enters the
    algebraic identities below). -/
noncomputable def ccvsGamma (zeta : ℕ → ℝ) (a : ℕ) : ℝ :=
  (ccvsPrefactor a : ℝ) * zeta (2*a + 1)

/-- **CCvS explicit check:** γ(−2) = (225/4)·ζ(5), for any assignment of
    zeta values — the arithmetic of the formula, exactly as printed in
    CCvS 2018. -/
theorem ccvsGamma_two (zeta : ℕ → ℝ) :
    ccvsGamma zeta 2 = (225 / 4 : ℝ) * zeta 5 := by
  unfold ccvsGamma
  rw [ccvsPrefactor_two]
  norm_num

/-- γ(−1) = (9/2)·ζ(3). -/
theorem ccvsGamma_one (zeta : ℕ → ℝ) :
    ccvsGamma zeta 1 = (9 / 2 : ℝ) * zeta 3 := by
  unfold ccvsGamma
  rw [ccvsPrefactor_one]
  norm_num

/-- γ(−3) = (6615/8)·ζ(7). -/
theorem ccvsGamma_three (zeta : ℕ → ℝ) :
    ccvsGamma zeta 3 = (6615 / 8 : ℝ) * zeta 7 := by
  unfold ccvsGamma
  rw [ccvsPrefactor_three]
  norm_num

/-- **The even-tower confluence (paper §IX.B).**  The numerator `2^(2a) − 1`
    of the CCvS pre-factor is EXACTLY the imaginary dimension of the level-2a
    Cayley–Dickson algebra: the pre-factor factors as

      `pref(a) = dim(Im 𝒜_{2a}) · (2a+1)! / (a · 2^(2a) · (a−1)!)`

    with `dim(Im 𝒜_{2a})` the genuine `finrank` of the imaginary subspace of
    `CDAlg ℝ (2a)` (proved in `CDDimension.even_tower_imDim`), not a numeral
    substituted by hand. -/
theorem ccvsPrefactor_eq_imDim_mul (a : ℕ) (ha : 1 ≤ a) :
    ccvsPrefactor a =
      (finrank ℝ (CDDimension.ImSubmodule (2*a)) : ℚ) *
        ((Nat.factorial (2*a + 1) : ℚ) /
          ((a : ℚ) * 2^(2*a) * (Nat.factorial (a - 1) : ℚ))) := by
  rw [CDDimension.even_tower_imDim]
  unfold ccvsPrefactor
  have h1 : (1 : ℕ) ≤ 2^(2*a) := Nat.one_le_two_pow
  rw [Nat.cast_sub h1]
  push_cast
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp ha
  have h2 : (2:ℚ)^(2*a) ≠ 0 := by positivity
  have h3 : (Nat.factorial (a-1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (a-1)).ne'
  field_simp

/-! ## Completeness audit — `#print axioms` -/

#print axioms profileMoment_dilate
#print axioms f4_scaling
#print axioms f2_scaling
#print axioms f0_invariant
#print axioms ccvsPrefactor_one
#print axioms ccvsPrefactor_two
#print axioms ccvsPrefactor_three
#print axioms ccvsGamma_two
#print axioms ccvsPrefactor_eq_imDim_mul

end QBP.Foundations.SpectralMoments
