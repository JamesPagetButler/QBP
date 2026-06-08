/-
  QBP.Foundations.Exp
  ===================

  Full-rigor exponential / logarithm on the Cayley–Dickson tower `CDAlg ℝ n`,
  via the **quadraticity route** (no non-associative ambient power series).

  Mathematical route (refined #474 plan; beekeeper ruling: FULL RIGOR at 𝕆/𝕊).
  Every `x : CDAlg ℝ n` satisfies the Cayley–Dickson square identity
  `x·x = (2 Re x)·x − N(x)·1`  (`CDAlg.cdAlg_sq_eq`, MERGED).  Decomposing
  `x = (Re x)•1 + Im x` with `Re (Im x) = 0`, quadraticity collapses to
  `Im x · Im x = − N(Im x) • 1`  (`imPart_mul_imPart`).  Since `N(Im x) = ∑ coordᵢ²`
  is a sum of real squares it is `≥ 0`, with equality iff `Im x = 0`
  (`N_eq_zero_iff`).  Hence `span{1, x} ≅ ℂ` for non-real `x`, and we may
  define `exp` in CLOSED FORM:

  ```
  exp x := Real.exp (re x) • (Real.cos ‖Im x‖ • 1 + Real.sinc ‖Im x‖ • Im x)
  ```

  with `‖Im x‖ = Real.sqrt (N (Im x))` and `Real.sinc` from Mathlib
  (`sinc t = sin t / t`, `sinc 0 = 1`).  Everything reduces to a 2-dimensional,
  COMMUTATIVE, ASSOCIATIVE `ℂ`-like calculation inside `span{1, Im x}`; no `decide`,
  no ambient non-associativity — purely symbolic with `ring`/`module` + Mathlib trig.

  Completeness (federation Lean standard, ~/Documents/inter/lean-proof-best-practices.md):
  zero `sorry`, zero `native_decide`, zero vacuous `True`.  `#print axioms` audit at
  the bottom — every result depends only on `{propext, Classical.choice, Quot.sound}`
  (Real.exp/cos/sin/sqrt are ordinary `def`s, not axioms; they add no extra axioms).

  The 𝕆 (n = 3) and 𝕊 (n = 4) operations-complete exp/log matrix cells are the
  `n = 3, 4` INSTANCES of the generic theorems here (aliases `octonion_*` / `sedenion_*`).
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
import QBP.Foundations.CDAlg
import QBP.Foundations.CDBridge

namespace QBP.Foundations.CDAlg

open scoped Real

variable {n : ℕ}

/-! ## 0. A `sinc` arithmetic helper

`sinc t · t = sin t` for ALL `t` (the `t = 0` case is `1·0 = 0 = sin 0`).  This is
exactly what makes the `sinc`-extension seamless at the imaginary-norm zero. -/

/-- `Real.sinc t * t = Real.sin t` for all `t`. -/
theorem sinc_mul_self (t : ℝ) : Real.sinc t * t = Real.sin t := by
  by_cases h : t = 0
  · subst h; simp [Real.sinc_zero]
  · rw [Real.sinc_of_ne_zero h, div_mul_cancel₀ _ h]

/-! ## 1. Real part, imaginary part, and the imaginary norm

For analysis we specialise to `R = ℝ`.  `re x` is the `e₀` coefficient; `imPart x`
is the imaginary projection `x − (re x)•1`. -/

/-- Real (scalar) part of `x : CDAlg ℝ n`: the `e₀` coordinate. -/
def re (x : CDAlg ℝ n) : ℝ := x.coord 0

@[simp] theorem re_def (x : CDAlg ℝ n) : re x = x.coord 0 := rfl

/-- Imaginary part: `x − (re x)•1`.  Lives entirely in the span of the imaginary
    basis units (its `e₀` coordinate is `0`, see `re_imPart`). -/
def imPart (x : CDAlg ℝ n) : CDAlg ℝ n := x - (re x) • 1

@[simp] theorem imPart_coord (x : CDAlg ℝ n) (i : Fin (2^n)) :
    (imPart x).coord i = x.coord i - (re x) * (if i = 0 then 1 else 0) := by
  simp only [imPart, sub_coord, smul_coord, one_coord]

/-- The decomposition `x = (re x)•1 + imPart x`. -/
theorem re_smul_one_add_imPart (x : CDAlg ℝ n) : (re x) • 1 + imPart x = x := by
  simp only [imPart]; abel

/-- The `e₀` coordinate of `imPart x` is `0`: the imaginary part is "purely
    imaginary". -/
@[simp] theorem re_imPart (x : CDAlg ℝ n) : re (imPart x) = 0 := by
  simp only [re_def, imPart_coord]; norm_num

/-- The imaginary part of a purely-imaginary element (one with `re = 0`) is itself. -/
theorem imPart_of_re_zero (x : CDAlg ℝ n) (h : re x = 0) : imPart x = x := by
  ext i; simp only [imPart_coord, h, zero_mul, sub_zero]

/-- `imPart` is idempotent. -/
@[simp] theorem imPart_imPart (x : CDAlg ℝ n) : imPart (imPart x) = imPart x :=
  imPart_of_re_zero _ (re_imPart x)

/-- The sum-of-squares norm form `N x = ∑ coordᵢ²` is `≥ 0` over ℝ. -/
theorem N_nonneg (x : CDAlg ℝ n) : 0 ≤ N x := by
  rw [N_def]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- `N x = 0 ↔ x = 0` over ℝ (positive-definiteness of the sum-of-squares norm
    form). -/
theorem N_eq_zero_iff (x : CDAlg ℝ n) : N x = 0 ↔ x = 0 := by
  rw [N_def]
  constructor
  · intro h
    ext i
    have hzero : ∀ i ∈ Finset.univ, (x.coord i)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp h
    have := hzero i (Finset.mem_univ i)
    simpa using pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this
  · rintro rfl; simp

/-- The imaginary norm `‖Im x‖ := √(N (imPart x))`. -/
noncomputable def imNorm (x : CDAlg ℝ n) : ℝ := Real.sqrt (N (imPart x))

theorem imNorm_nonneg (x : CDAlg ℝ n) : 0 ≤ imNorm x := Real.sqrt_nonneg _

/-- `‖Im x‖ = 0 ↔ Im x = 0`: positive-definiteness of the imaginary norm. -/
theorem imNorm_eq_zero_iff (x : CDAlg ℝ n) : imNorm x = 0 ↔ imPart x = 0 := by
  rw [imNorm, Real.sqrt_eq_zero (N_nonneg _), N_eq_zero_iff]

/-- `(‖Im x‖)² = N (imPart x)`. -/
theorem imNorm_sq (x : CDAlg ℝ n) : (imNorm x)^2 = N (imPart x) :=
  Real.sq_sqrt (N_nonneg _)

/-- `N (r • x) = r² · N x` (the norm form is degree-2 homogeneous). -/
theorem N_smul (r : ℝ) (x : CDAlg ℝ n) : N (r • x) = r^2 * N x := by
  rw [N_def, N_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [smul_coord]; ring

/-! ## 2. The square of an imaginary element

From quadraticity (`cdAlg_sq_eq`) applied to a purely-imaginary element, the linear
term drops out: `(Im x)² = − N(Im x) • 1`.  This is the single fact that makes
`span{1, Im x}` a commutative associative `ℂ`-like subalgebra. -/

/-- **Imaginary square.**  For purely-imaginary `v` (`re v = 0`),
    `v · v = − N(v) • 1`. -/
theorem imag_mul_self {v : CDAlg ℝ n} (hv : re v = 0) : v * v = - (N v) • 1 := by
  have hq := cdAlg_sq_eq v
  rw [show v.coord 0 = re v from rfl, hv] at hq
  rw [hq]; simp [neg_smul]

/-- **`(Im x)² = − N(Im x) • 1`.** -/
theorem imPart_mul_imPart (x : CDAlg ℝ n) :
    imPart x * imPart x = - (N (imPart x)) • 1 :=
  imag_mul_self (re_imPart x)

/-! ## 3. The exponential (closed form)

`exp x := Real.exp (re x) • (cos ‖Im x‖ • 1 + sinc ‖Im x‖ • Im x)`.
The `sinc` extension (`sinc 0 = 1`) makes the real case `exp (r•1)` seamless. -/

/-- **Cayley–Dickson exponential**, closed form via quadraticity.  Matches
    Mathlib's `Quaternion.exp_eq` at `n = 2` (see `exp_eq_quaternion`). -/
noncomputable def exp (x : CDAlg ℝ n) : CDAlg ℝ n :=
  Real.exp (re x) • (Real.cos (imNorm x) • 1 + Real.sinc (imNorm x) • imPart x)

theorem exp_def (x : CDAlg ℝ n) :
    exp x = Real.exp (re x) • (Real.cos (imNorm x) • 1 + Real.sinc (imNorm x) • imPart x) :=
  rfl

/-! ## 4. Basic well-definedness and the real case -/

/-- **Well-definedness at `Im x = 0`.**  For a real element `r•1`,
    `exp (r•1) = (Real.exp r) • 1`.  The `sinc`-extension makes the imaginary term
    vanish (`sinc 0 • 0 = 0`), so the real exponential agrees seamlessly. -/
theorem exp_re_smul_one (r : ℝ) : exp ((r : ℝ) • (1 : CDAlg ℝ n)) = (Real.exp r) • 1 := by
  have hre : re ((r : ℝ) • (1 : CDAlg ℝ n)) = r := by
    simp only [re_def, smul_coord, one_coord]; norm_num
  have him : imPart ((r : ℝ) • (1 : CDAlg ℝ n)) = 0 := by
    ext i; simp only [imPart_coord, hre, smul_coord, one_coord, zero_coord]
    by_cases h : i = 0 <;> simp [h]
  have hNz : N (imPart ((r : ℝ) • (1 : CDAlg ℝ n))) = 0 := (N_eq_zero_iff _).mpr him
  rw [exp_def, hre, him]
  simp only [smul_zero, add_zero, imNorm, hNz, Real.sqrt_zero,
    Real.cos_zero, one_smul]

/-- `exp 0 = 1`. -/
@[simp] theorem exp_zero : exp (0 : CDAlg ℝ n) = 1 := by
  have h0 : (0 : CDAlg ℝ n) = (0 : ℝ) • (1 : CDAlg ℝ n) := by rw [zero_smul]
  rw [h0, exp_re_smul_one, Real.exp_zero, one_smul]

/-- A purely-imaginary element exponentiates to `cos ‖v‖ • 1 + sinc ‖v‖ • v`. -/
theorem exp_of_re_zero {v : CDAlg ℝ n} (hv : re v = 0) :
    exp v = Real.cos (imNorm v) • 1 + Real.sinc (imNorm v) • v := by
  rw [exp_def, hv, Real.exp_zero, one_smul, imPart_of_re_zero v hv]

/-! ## 5. Algebra inside `span{1, v}`

For purely-imaginary `v`, `a•1 + b•v` multiply via `v·v = −N(v)•1`. -/

/-- Multiplication of two elements of `span{1, v}` for purely-imaginary `v`:
    `(a•1+b•v)(c•1+d•v) = (ac − bd·N(v))•1 + (ad+bc)•v`.  Commutative & associative
    inside this 2-dim subalgebra even though the ambient algebra need not be. -/
theorem span_mul {v : CDAlg ℝ n} (hv : re v = 0) (a b c d : ℝ) :
    (a • (1 : CDAlg ℝ n) + b • v) * (c • 1 + d • v)
      = (a * c - b * d * N v) • 1 + (a * d + b * c) • v := by
  have hvv : v * v = - (N v) • 1 := imag_mul_self hv
  have h11 : (1 : CDAlg ℝ n) * 1 = 1 := cdAlg_one_mul 1
  have h1v : (1 : CDAlg ℝ n) * v = v := cdAlg_one_mul v
  have hv1 : v * (1 : CDAlg ℝ n) = v := cdAlg_mul_one v
  rw [mul_add_left, mul_add_right, mul_add_right,
      mul_smul_left, mul_smul_left, mul_smul_left, mul_smul_left,
      mul_smul_right, mul_smul_right, mul_smul_right, mul_smul_right,
      h11, h1v, hv1, hvv]
  module

/-- For a **unit imaginary** `u` (`re u = 0`, `N u = 1`), elements `a•1+b•u`
    multiply exactly as complex numbers `(a+bi)`:
    `(a•1+b•u)(c•1+d•u) = (ac−bd)•1 + (ad+bc)•u`. -/
theorem unit_span_mul {u : CDAlg ℝ n} (hu : re u = 0) (hN : N u = 1) (a b c d : ℝ) :
    (a • (1 : CDAlg ℝ n) + b • u) * (c • 1 + d • u)
      = (a * c - b * d) • 1 + (a * d + b * c) • u := by
  rw [span_mul hu, hN, mul_one]

/-! ## 6. Rotors: the clean complex group law on a unit imaginary axis

For a unit imaginary `u`, `cos α•1 + sin α•u` is a "rotor"; rotors multiply by
adding angles (Mathlib `Real.cos_add`/`Real.sin_add`).  This is the genuine
`span{1,u} ≅ ℂ` one-parameter group, with no `sqrt`/`abs`. -/

/-- **Rotor product = angle addition.**  `(cos α•1+sin α•u)(cos β•1+sin β•u)
    = cos(α+β)•1 + sin(α+β)•u` for a unit imaginary `u`. -/
theorem rotor_mul {u : CDAlg ℝ n} (hu : re u = 0) (hN : N u = 1) (α β : ℝ) :
    (Real.cos α • (1 : CDAlg ℝ n) + Real.sin α • u) * (Real.cos β • 1 + Real.sin β • u)
      = Real.cos (α + β) • 1 + Real.sin (α + β) • u := by
  rw [unit_span_mul hu hN, Real.cos_add, Real.sin_add]
  congr 2
  ring

/-! ## 7. The exponential along a unit imaginary axis, and the one-parameter group law -/

/-- `re (r•1 + v) = r` when `re v = 0`. -/
theorem re_real_add_imag {v : CDAlg ℝ n} (hv : re v = 0) (r : ℝ) :
    re (r • (1 : CDAlg ℝ n) + v) = r := by
  simp only [re_def, add_coord, smul_coord, one_coord]
  simp only [re_def] at hv
  rw [hv]; norm_num

/-- `imPart (r•1 + v) = v` when `re v = 0`. -/
theorem imPart_real_add_imag {v : CDAlg ℝ n} (hv : re v = 0) (r : ℝ) :
    imPart (r • (1 : CDAlg ℝ n) + v) = v := by
  ext i
  rw [imPart_coord, re_real_add_imag hv]
  simp only [add_coord, smul_coord, one_coord]
  by_cases h : i = 0
  · subst h
    simp only [re_def] at hv; rw [hv]; simp
  · simp [h]

/-- **`exp` on a unit imaginary axis.**  `exp (r•1 + θ•u) = exp r • (cos θ•1 + sin θ•u)`
    for a unit imaginary `u` and `θ ≥ 0`.  This is the normal form the group law uses. -/
theorem exp_unit_axis {u : CDAlg ℝ n} (hu : re u = 0) (hN : N u = 1) (r θ : ℝ) (hθ : 0 ≤ θ) :
    exp (r • (1 : CDAlg ℝ n) + θ • u) = Real.exp r • (Real.cos θ • 1 + Real.sin θ • u) := by
  have hθu : re (θ • u) = 0 := by
    simp only [re_def, smul_coord]; simp only [re_def] at hu; rw [hu]; ring
  have hre : re (r • (1 : CDAlg ℝ n) + θ • u) = r := re_real_add_imag hθu r
  have him : imPart (r • (1 : CDAlg ℝ n) + θ • u) = θ • u := imPart_real_add_imag hθu r
  have hin : imNorm (r • (1 : CDAlg ℝ n) + θ • u) = θ := by
    rw [imNorm, him, N_smul, hN, mul_one, Real.sqrt_sq hθ]
  rw [exp_def, hre, him, hin, smul_smul, sinc_mul_self]

/-- **One-parameter group law along a unit imaginary axis.**  Scaled rotors compose:
    `exp(r•1 + s•u) * exp(r'•1 + t•u) = exp((r+r')•1 + (s+t)•u)` for a unit imaginary
    `u` and `s, t ≥ 0`. -/
theorem exp_unit_axis_add {u : CDAlg ℝ n} (hu : re u = 0) (hN : N u = 1)
    (r r' s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 ≤ s + t) :
    exp (r • (1 : CDAlg ℝ n) + s • u) * exp (r' • 1 + t • u)
      = exp ((r + r') • 1 + (s + t) • u) := by
  rw [exp_unit_axis hu hN r s hs, exp_unit_axis hu hN r' t ht,
      exp_unit_axis hu hN (r + r') (s + t) hst,
      mul_smul_left, mul_smul_right, smul_smul, ← Real.exp_add]
  congr 1
  rw [rotor_mul hu hN]

/-! ## 8. The fully-general one-parameter group law `exp((s+t)•x) = exp(s•x)*exp(t•x)`

We reduce to the unit-axis law.  Write `x = (re x)•1 + Im x`; for `s, t ≥ 0`,
`s•x` and `t•x` lie on the same imaginary axis `Im x / ‖Im x‖`. -/

/-- `re (s • x) = s · re x`. -/
theorem re_smul (s : ℝ) (x : CDAlg ℝ n) : re (s • x) = s * re x := by
  simp only [re_def, smul_coord]

/-- `imPart (s • x) = s • imPart x`. -/
theorem imPart_smul (s : ℝ) (x : CDAlg ℝ n) : imPart (s • x) = s • imPart x := by
  ext i; simp only [imPart_coord, smul_coord, re_smul]; ring

/-- **One-parameter group law (general), nonnegative parameters.**  For `s, t ≥ 0`
    and any `x : CDAlg ℝ n`, `exp((s+t)•x) = exp(s•x) * exp(t•x)`.

    Proof: the real case (`Im x = 0`) is the scalar `Real.exp_add`; otherwise let
    `u = Im x / ‖Im x‖` be the unit imaginary axis, write each `q•x = (q re x)•1 +
    (q ‖Im x‖)•u`, and apply `exp_unit_axis_add`. -/
theorem exp_smul_add {x : CDAlg ℝ n} (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    exp ((s + t) • x) = exp (s • x) * exp (t • x) := by
  by_cases hx : imPart x = 0
  · -- real case: x = (re x)•1
    have hxr : x = (re x) • (1 : CDAlg ℝ n) := by
      have := re_smul_one_add_imPart x; rw [hx, add_zero] at this; exact this.symm
    rw [hxr,
        show (s + t) • ((re x) • (1 : CDAlg ℝ n)) = ((s + t) * re x) • 1 from by rw [smul_smul],
        show s • ((re x) • (1 : CDAlg ℝ n)) = (s * re x) • 1 from by rw [smul_smul],
        show t • ((re x) • (1 : CDAlg ℝ n)) = (t * re x) • 1 from by rw [smul_smul],
        exp_re_smul_one, exp_re_smul_one, exp_re_smul_one,
        mul_smul_left, mul_smul_right, smul_smul, ← Real.exp_add, cdAlg_one_mul]
    congr 2; ring
  · -- non-real case: build the unit axis
    set m : ℝ := imNorm x with hm
    have hmpos : 0 < m := by
      rw [hm, imNorm, Real.sqrt_pos]
      exact lt_of_le_of_ne (N_nonneg _) (fun h => hx ((N_eq_zero_iff _).mp h.symm))
    set u : CDAlg ℝ n := m⁻¹ • imPart x with hu_def
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have hu_re : re u = 0 := by rw [hu_def, re_smul, re_imPart, mul_zero]
    have hu_N : N u = 1 := by
      rw [hu_def, N_smul, ← imNorm_sq x, ← hm]; field_simp
    have hdecomp : ∀ q : ℝ, q • x = (q * re x) • (1 : CDAlg ℝ n) + (q * m) • u := by
      intro q
      rw [hu_def, smul_smul, show q * m * m⁻¹ = q from by field_simp,
          ← smul_smul, ← imPart_smul]
      conv_lhs => rw [← re_smul_one_add_imPart x]
      rw [smul_add, smul_smul, imPart_smul]
    rw [hdecomp (s + t), hdecomp s, hdecomp t]
    have hsm : 0 ≤ s * m := mul_nonneg hs (le_of_lt hmpos)
    have htm : 0 ≤ t * m := mul_nonneg ht (le_of_lt hmpos)
    rw [show (s + t) * re x = s * re x + t * re x from by ring,
        show (s + t) * m = s * m + t * m from by ring]
    exact (exp_unit_axis_add hu_re hu_N (s * re x) (t * re x) (s * m) (t * m) hsm htm
      (by rw [← add_mul]; exact mul_nonneg (by linarith) (le_of_lt hmpos))).symm

/-! ## 9. `exp(-x) * exp(x) = 1` and the norm of the exponential -/

/-- `re (-x) = - re x`. -/
theorem re_neg (x : CDAlg ℝ n) : re (-x) = - re x := by simp only [re_def, neg_coord]

/-- `imPart (-x) = - imPart x`. -/
theorem imPart_neg (x : CDAlg ℝ n) : imPart (-x) = - imPart x := by
  ext i; simp only [imPart_coord, re_neg, neg_coord]; ring

/-- `imNorm (-x) = imNorm x`. -/
theorem imNorm_neg (x : CDAlg ℝ n) : imNorm (-x) = imNorm x := by
  rw [imNorm, imNorm, imPart_neg]
  congr 1
  rw [N_def, N_def]
  exact Finset.sum_congr rfl (fun i _ => by simp only [neg_coord]; ring)

/-- **`exp(-x) * exp(x) = 1`.**  The exponential is invertible in the `span{1,Im x}`
    subalgebra (where inversion is honest even though 𝕊 has zero divisors globally).
    Direct from the closed form and `Im x · Im x = −m²•1`, giving
    `(cos²m + sin²m)•1 = 1`. -/
theorem exp_neg_mul_exp (x : CDAlg ℝ n) : exp (-x) * exp x = 1 := by
  set m : ℝ := imNorm x with hm
  set v : CDAlg ℝ n := imPart x with hv
  have hvre : re v = 0 := re_imPart x
  have hexpx : exp x = Real.exp (re x) • (Real.cos m • 1 + Real.sinc m • v) := by
    rw [exp_def]
  have hexpnegx : exp (-x) = Real.exp (-(re x)) • (Real.cos m • 1 + Real.sinc m • (-v)) := by
    rw [exp_def, re_neg, imNorm_neg, imPart_neg]
  rw [hexpx, hexpnegx,
      mul_smul_left, mul_smul_right, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_smul,
      show (Real.sinc m • (-v)) = (-(Real.sinc m)) • v from by rw [smul_neg, neg_smul],
      span_mul hvre]
  have hNv : N v = m^2 := by rw [hm, hv, imNorm_sq]
  rw [hNv]
  have hsincm : (-(Real.sinc m)) * Real.sinc m * m^2 = -(Real.sin m)^2 := by
    have h := sinc_mul_self m
    calc (-(Real.sinc m)) * Real.sinc m * m^2 = -((Real.sinc m * m)^2) := by ring
      _ = -(Real.sin m)^2 := by rw [h]
  rw [show Real.cos m * Real.cos m - (-(Real.sinc m)) * Real.sinc m * m ^ 2
        = Real.cos m ^ 2 + Real.sin m ^ 2 from by rw [hsincm]; ring,
      Real.cos_sq_add_sin_sq,
      show Real.cos m * Real.sinc m + (-(Real.sinc m)) * Real.cos m = 0 from by ring,
      zero_smul, add_zero, one_smul]

/-- **`N (exp x) = Real.exp (2 · re x)`.**  Norm of the exponential.  Inside the
    `span{1,Im x}` subalgebra the closed form gives
    `N (cos m•1 + sinc m•Im x) = cos²m + sin²m = 1`, scaled by `(exp (re x))²`. -/
theorem N_exp (x : CDAlg ℝ n) : N (exp x) = Real.exp (2 * re x) := by
  set m : ℝ := imNorm x with hm
  set v : CDAlg ℝ n := imPart x with hv
  have hvre : re v = 0 := re_imPart x
  rw [exp_def, ← hm, ← hv, N_smul]
  have hN1 : N (Real.cos m • (1 : CDAlg ℝ n) + Real.sinc m • v)
      = (Real.cos m)^2 + (Real.sinc m)^2 * N v := by
    rw [N_def, N_def, Finset.mul_sum]
    -- coordinatewise the summand splits into a `cos²m`-at-0 term and a `sinc²m·vᵢ²` term
    have hsplit : ∀ i : Fin (2^n),
        ((Real.cos m • (1 : CDAlg ℝ n) + Real.sinc m • v).coord i)^2
          = (if i = 0 then (Real.cos m)^2 else 0) + (Real.sinc m)^2 * (v.coord i)^2 := by
      intro i
      simp only [add_coord, smul_coord, one_coord]
      by_cases h : i = 0
      · subst h
        have hv0 : v.coord 0 = 0 := hvre
        rw [hv0]; simp
      · simp only [if_neg h, mul_zero]; ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (2^n)) (fun _ => (Real.cos m)^2)]
    simp
  rw [hN1]
  have hNv : N v = m^2 := by rw [hm, hv, imNorm_sq]
  rw [hNv]
  have hsincm : (Real.sinc m)^2 * m^2 = (Real.sin m)^2 := by
    have h := sinc_mul_self m
    calc (Real.sinc m)^2 * m^2 = (Real.sinc m * m)^2 := by ring
      _ = (Real.sin m)^2 := by rw [h]
  rw [hsincm, Real.cos_sq_add_sin_sq, mul_one,
      show (2 : ℝ) * re x = re x + re x from by ring, Real.exp_add]
  ring

/-! ## 10. Agreement with Mathlib's quaternion exponential at `n = 2`

`cdAlg2EquivQuaternion : CDAlg ℝ 2 ≃ₐ[ℝ] ℍ[ℝ]` is the merged bridge.  We transport
our `exp` through it and show it equals `NormedSpace.exp ℝ` (Mathlib's quaternion
exponential), whose closed form `Quaternion.exp_eq` matches ours term-for-term. -/

open scoped Quaternion in
/-- The bridge sends our real part to the quaternion real part: both are `x.coord 0`. -/
theorem cdAlg2Equiv_re (x : CDAlg ℝ 2) : (cdAlg2EquivQuaternion x).re = re x := by
  rfl

open scoped Quaternion in
/-- The bridge's coordinate read: the three imaginary quaternion components are the
    coordinates `1, 2, 3` of `x` (the bridge is the orientation-preserving identity). -/
theorem cdAlg2Equiv_imI (x : CDAlg ℝ 2) :
    (cdAlg2EquivQuaternion x).imI = x.coord ⟨1, by norm_num⟩ := rfl

open scoped Quaternion in
theorem cdAlg2Equiv_imJ (x : CDAlg ℝ 2) :
    (cdAlg2EquivQuaternion x).imJ = x.coord ⟨2, by norm_num⟩ := rfl

open scoped Quaternion in
theorem cdAlg2Equiv_imK (x : CDAlg ℝ 2) :
    (cdAlg2EquivQuaternion x).imK = x.coord ⟨3, by norm_num⟩ := rfl

open scoped Quaternion in
/-- **The bridge intertwines imaginary parts.**  `Φ (Im x) = (Φ x).im`, where
    `Φ = cdAlg2EquivQuaternion`.  Both equal `Φ x − ↑(re x)`. -/
theorem cdAlg2Equiv_imPart (x : CDAlg ℝ 2) :
    cdAlg2EquivQuaternion (imPart x) = (cdAlg2EquivQuaternion x).im := by
  -- both sides have re = 0 and share imaginary components; check componentwise
  apply Quaternion.ext
  · rw [Quaternion.re_im]; exact cdAlg2Equiv_re (imPart x) ▸ re_imPart x
  · rw [cdAlg2Equiv_imI, Quaternion.imI_im, cdAlg2Equiv_imI, imPart_coord]; norm_num
  · rw [cdAlg2Equiv_imJ, Quaternion.imJ_im, cdAlg2Equiv_imJ, imPart_coord]; norm_num
  · rw [cdAlg2Equiv_imK, Quaternion.imK_im, cdAlg2Equiv_imK, imPart_coord]; norm_num

open scoped Quaternion in
/-- **The bridge preserves the imaginary norm.**  `‖(Φ x).im‖ = imNorm x`.  Both are
    `√(coord₁² + coord₂² + coord₃²)` (the `e₀` coordinate drops out on each side). -/
theorem cdAlg2Equiv_imNorm (x : CDAlg ℝ 2) :
    ‖(cdAlg2EquivQuaternion x).im‖ = imNorm x := by
  have hnsq : N (imPart x) = Quaternion.normSq ((cdAlg2EquivQuaternion x).im) := by
    rw [Quaternion.normSq_def', N_def]
    rw [show (∑ i, (imPart x).coord i ^ 2)
          = ∑ i : Fin 4, (imPart x).coord i ^ 2 from rfl, Fin.sum_univ_four]
    simp only [Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im,
      cdAlg2Equiv_imI, cdAlg2Equiv_imJ, cdAlg2Equiv_imK]
    have h0 : (imPart x).coord (0 : Fin (2^2)) = 0 := by
      have := re_imPart x; simp only [re_def] at this; exact this
    have h1 : (imPart x).coord (1 : Fin (2^2)) = x.coord ⟨1, by norm_num⟩ := by
      rw [imPart_coord, if_neg (by decide)]; simp
    have h2 : (imPart x).coord (2 : Fin (2^2)) = x.coord ⟨2, by norm_num⟩ := by
      rw [imPart_coord, if_neg (by decide)]; simp
    have h3 : (imPart x).coord (3 : Fin (2^2)) = x.coord ⟨3, by norm_num⟩ := by
      rw [imPart_coord, if_neg (by decide)]; simp
    rw [h1, h2, h3, h0]
  rw [imNorm, hnsq, Quaternion.normSq_eq_norm_mul_self,
      Real.sqrt_mul_self (norm_nonneg _)]

open scoped Quaternion in
/-- **n = 2 transport: our `exp` agrees with Mathlib's quaternion exponential.**
    `Φ (exp x) = NormedSpace.exp ℝ (Φ x)` where `Φ = cdAlg2EquivQuaternion`.  Both sides
    are the same closed form: ours is `exp(re)•(cos‖Im‖•1 + sinc‖Im‖•Im)`, Mathlib's
    `Quaternion.exp_eq` is `exp(re)•(↑cos‖im‖ + (sin‖im‖/‖im‖)•im)`; the bridge lemmas
    `cdAlg2Equiv_re`, `cdAlg2Equiv_imPart`, `cdAlg2Equiv_imNorm` make them identical
    (and `sinc t = sin t / t`). -/
theorem exp_eq_quaternion (x : CDAlg ℝ 2) :
    cdAlg2EquivQuaternion (exp x) = NormedSpace.exp (cdAlg2EquivQuaternion x) := by
  rw [Quaternion.exp_eq, exp_def, map_smul, map_add, map_smul, map_smul, map_one]
  rw [cdAlg2Equiv_re, cdAlg2Equiv_imPart, cdAlg2Equiv_imNorm]
  -- LHS scalar `Real.exp (re x)`, RHS scalar `NormedSpace.exp (re x)` ; relate
  rw [show NormedSpace.exp (re x : ℝ) = Real.exp (re x) from
        congrFun Real.exp_eq_exp_ℝ.symm (re x)]
  congr 1
  -- cos m • 1 + sinc m • im = ↑(cos m) + (sin m / m) • im over ℍ
  have hcoe : Real.cos (imNorm x) • (1 : ℍ[ℝ]) = ↑(Real.cos (imNorm x)) := by
    rw [← Quaternion.coe_one, ← Quaternion.coe_smul, smul_eq_mul, mul_one]
  rw [Real.sinc]
  by_cases hm : imNorm x = 0
  · have him0 : (cdAlg2EquivQuaternion x).im = 0 := by
      rw [← norm_eq_zero, cdAlg2Equiv_imNorm]; exact hm
    rw [him0]
    simp only [smul_zero, add_zero, hcoe]
  · rw [if_neg hm, hcoe]

/-! ## 11. Principal logarithm and its right-inverse property

`log` is defined on the honest domain `{x | 0 < N x}` via the principal branch:
`log x := (½ log (N x))•1 + (θ/‖Im x‖)•Im x` with `θ = arccos (re x / √(N x)) ∈ [0,π]`.
We prove `exp (log x) = x` on `{x | 0 < N x ∧ imPart x ≠ 0}` (the principal interior,
where the imaginary axis is well-defined). -/

/-- **Pythagorean norm decomposition.**  `N x = (re x)² + N (imPart x)`: the squared
    norm splits into the real-part square plus the imaginary norm-square. -/
theorem N_eq_re_sq_add_N_imPart (x : CDAlg ℝ n) : N x = (re x)^2 + N (imPart x) := by
  rw [N_def, N_def]
  -- split off the i = 0 term on both sides; imPart kills the real coordinate
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : Fin (2^n))),
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : Fin (2^n)))]
  have hi0 : (imPart x).coord 0 = 0 := by
    have := re_imPart x; simp only [re_def] at this; exact this
  rw [hi0]
  have hsum : (∑ i ∈ Finset.univ.erase (0 : Fin (2^n)), (x.coord i)^2)
      = ∑ i ∈ Finset.univ.erase (0 : Fin (2^n)), ((imPart x).coord i)^2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hine : i ≠ 0 := Finset.ne_of_mem_erase hi
    rw [imPart_coord]; simp [hine]
  rw [hsum]; simp [re_def]; ring

/-- The principal logarithm angle `θ = arccos (re x / √(N x)) ∈ [0, π]`. -/
noncomputable def logAngle (x : CDAlg ℝ n) : ℝ := Real.arccos (re x / Real.sqrt (N x))

/-- **Principal logarithm.**  `log x = (½ log (N x))•1 + (θ/‖Im x‖)•Im x`. -/
noncomputable def log (x : CDAlg ℝ n) : CDAlg ℝ n :=
  ((1/2) * Real.log (N x)) • 1 + (logAngle x / imNorm x) • imPart x

theorem log_def (x : CDAlg ℝ n) :
    log x = ((1/2) * Real.log (N x)) • 1 + (logAngle x / imNorm x) • imPart x := rfl

/-- **Right-inverse property of the principal logarithm.**  On the domain
    `0 < N x ∧ imPart x ≠ 0` (non-real, nonzero), `exp (log x) = x`.

    Sketch: `N x = re² + ‖Im x‖²`; set `ρ = √(N x) > 0`, `θ = arccos(re/ρ) ∈ [0,π]`.
    `log x` has `re = ½ log (N x) = log ρ` and imaginary axis `u = Im x/‖Im x‖`
    (unit imaginary) with coefficient `θ`.  By `exp_unit_axis`, `exp (log x)
    = ρ • (cos θ • 1 + sin θ • u)`.  Now `ρ cos θ = ρ·(re/ρ) = re` and `ρ sin θ • u
    = ρ sin θ /‖Im x‖ • Im x`; with `sin θ = √(1−(re/ρ)²) = ‖Im x‖/ρ` (since θ∈[0,π],
    sin θ ≥ 0), this is `Im x`.  So `exp (log x) = re•1 + Im x = x`. -/
theorem exp_log {x : CDAlg ℝ n} (hN : 0 < N x) (him : imPart x ≠ 0) : exp (log x) = x := by
  -- abbreviations
  set ρ : ℝ := Real.sqrt (N x) with hρ
  have hρpos : 0 < ρ := by rw [hρ, Real.sqrt_pos]; exact hN
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρsq : ρ^2 = N x := by rw [hρ]; exact Real.sq_sqrt (le_of_lt hN)
  -- imaginary norm and the unit axis
  set mIm : ℝ := imNorm x with hmIm
  have hmImpos : 0 < mIm := by
    rw [hmIm, imNorm, Real.sqrt_pos]
    exact lt_of_le_of_ne (N_nonneg _) (fun h => him ((N_eq_zero_iff _).mp h.symm))
  have hmImne : mIm ≠ 0 := ne_of_gt hmImpos
  set u : CDAlg ℝ n := mIm⁻¹ • imPart x with hu_def
  have hu_re : re u = 0 := by rw [hu_def, re_smul, re_imPart, mul_zero]
  have hu_N : N u = 1 := by
    rw [hu_def, N_smul, ← imNorm_sq x, ← hmIm]; field_simp
  -- θ = logAngle x ; r = ½ log (N x)
  set θ : ℝ := logAngle x with hθ
  have hθnn : 0 ≤ θ := by rw [hθ, logAngle]; exact Real.arccos_nonneg _
  -- log x written on the unit axis: log x = (½ log N x)•1 + θ•u
  have hlog_axis : log x = ((1/2) * Real.log (N x)) • (1 : CDAlg ℝ n) + θ • u := by
    rw [log_def, hu_def, smul_smul, hθ]
    rw [show logAngle x / mIm = logAngle x * mIm⁻¹ from div_eq_mul_inv _ _]
  -- exp of that, via the unit-axis closed form
  rw [hlog_axis, exp_unit_axis hu_re hu_N _ θ hθnn]
  -- exp (½ log N x) = ρ
  have hexpr : Real.exp ((1/2) * Real.log (N x)) = ρ := by
    rw [hρ, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN]
    congr 1; ring
  rw [hexpr]
  -- |re x| ≤ ρ since (re x)² ≤ N x = ρ²
  have hre_sq_le : (re x)^2 ≤ ρ^2 := by
    rw [hρsq, N_eq_re_sq_add_N_imPart x]; nlinarith [N_nonneg (imPart x)]
  have habs : |re x| ≤ ρ := by
    rw [← Real.sqrt_sq (le_of_lt hρpos), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hre_sq_le
  have hbound1 : -1 ≤ re x / ρ := by
    rw [le_div_iff₀ hρpos]; have := (abs_le.mp habs).1; linarith
  have hbound2 : re x / ρ ≤ 1 := by
    rw [div_le_iff₀ hρpos]; have := (abs_le.mp habs).2; linarith
  have hcos : Real.cos θ = re x / ρ := by
    rw [hθ, logAngle, ← hρ, Real.cos_arccos hbound1 hbound2]
  have hsin : Real.sin θ = mIm / ρ := by
    rw [hθ, logAngle, ← hρ, Real.sin_arccos]
    -- √(1 - (re x/ρ)²) = mIm/ρ  ;  1 - (re/ρ)² = N(imPart x)/N x = mIm²/ρ²
    rw [show 1 - (re x / ρ)^2 = (mIm/ρ)^2 from by
      rw [div_pow, div_pow,
          show (mIm)^2 = N (imPart x) from by rw [hmIm, imNorm_sq],
          show (ρ)^2 = N x from hρsq]
      have hpyth : N x = (re x)^2 + N (imPart x) := N_eq_re_sq_add_N_imPart x
      field_simp
      linarith [hpyth]]
    exact Real.sqrt_sq (by positivity)
  rw [hcos, hsin]
  -- ρ • ((re x/ρ)•1 + (mIm/ρ)•u) = re x • 1 + mIm • u = re x • 1 + imPart x
  rw [smul_add, smul_smul, smul_smul]
  rw [show ρ * (re x / ρ) = re x from by field_simp,
      show ρ * (mIm / ρ) = mIm from by field_simp]
  -- mIm • u = imPart x
  rw [hu_def, smul_smul, show mIm * mIm⁻¹ = 1 from by field_simp, one_smul]
  exact re_smul_one_add_imPart x

/-! ## 12. The 𝕆 (n = 3) and 𝕊 (n = 4) operations-complete matrix cells

The exp/log cells of the operations-complete matrix at the octonion and sedenion
levels are exactly the `n = 3` and `n = 4` INSTANCES of the generic theorems above.
The cells assert: exp/log exist as well-defined operations (via power-associativity /
the `span{1,v} ≅ ℂ` subalgebra) — discharged here by the closed-form `exp`, its
group law `exp_smul_add`, invertibility `exp_neg_mul_exp`, norm law `N_exp`, and the
principal-log right-inverse `exp_log`.  The aliases below name those instances. -/

/-- **𝕆 exp/log cell.**  Octonion (`n = 3`) one-parameter group law:
    `exp((s+t)•x) = exp(s•x)·exp(t•x)` for `s,t ≥ 0`. -/
theorem octonion_exp_smul_add (x : CDAlg ℝ 3) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    exp ((s + t) • x) = exp (s • x) * exp (t • x) := exp_smul_add s t hs ht

/-- **𝕆 exp invertibility cell.** `exp(−x)·exp(x) = 1` on octonions. -/
theorem octonion_exp_neg_mul_exp (x : CDAlg ℝ 3) : exp (-x) * exp x = 1 := exp_neg_mul_exp x

/-- **𝕆 exp norm cell.** `N(exp x) = exp(2 Re x)` on octonions. -/
theorem octonion_N_exp (x : CDAlg ℝ 3) : N (exp x) = Real.exp (2 * re x) := N_exp x

/-- **𝕆 log right-inverse cell.** `exp(log x) = x` for non-real `x` with `0 < N x`. -/
theorem octonion_exp_log {x : CDAlg ℝ 3} (hN : 0 < N x) (him : imPart x ≠ 0) :
    exp (log x) = x := exp_log hN him

/-- **𝕊 exp/log cell.**  Sedenion (`n = 4`) one-parameter group law.  Note 𝕊 has
    zero divisors globally, but `exp` lands in the commutative-associative
    `span{1, Im x} ≅ ℂ` subalgebra where the group/inverse laws are honest. -/
theorem sedenion_exp_smul_add (x : CDAlg ℝ 4) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    exp ((s + t) • x) = exp (s • x) * exp (t • x) := exp_smul_add s t hs ht

/-- **𝕊 exp invertibility cell.** `exp(−x)·exp(x) = 1` on sedenions (honest in the
    ℂ-like subalgebra despite global zero divisors). -/
theorem sedenion_exp_neg_mul_exp (x : CDAlg ℝ 4) : exp (-x) * exp x = 1 := exp_neg_mul_exp x

/-- **𝕊 exp norm cell.** `N(exp x) = exp(2 Re x)` on sedenions. -/
theorem sedenion_N_exp (x : CDAlg ℝ 4) : N (exp x) = Real.exp (2 * re x) := N_exp x

/-- **𝕊 log right-inverse cell.** `exp(log x) = x` for non-real `x` with `0 < N x`. -/
theorem sedenion_exp_log {x : CDAlg ℝ 4} (hN : 0 < N x) (him : imPart x ≠ 0) :
    exp (log x) = x := exp_log hN him

/-! ## 13. Completeness audit — `#print axioms`

Every theorem below must show ONLY `{propext, Classical.choice, Quot.sound}`.  The
real-analysis content (Real.exp/cos/sin/sqrt/arccos, Mathlib `Quaternion` exp) is
built from ordinary `def`s and contributes no extra axioms. -/

#print axioms imag_mul_self
#print axioms imPart_mul_imPart
#print axioms exp_zero
#print axioms exp_re_smul_one
#print axioms span_mul
#print axioms rotor_mul
#print axioms exp_unit_axis
#print axioms exp_unit_axis_add
#print axioms exp_smul_add
#print axioms exp_neg_mul_exp
#print axioms N_exp
#print axioms N_eq_re_sq_add_N_imPart
#print axioms exp_log
#print axioms cdAlg2Equiv_imPart
#print axioms cdAlg2Equiv_imNorm
#print axioms exp_eq_quaternion
#print axioms octonion_exp_smul_add
#print axioms sedenion_exp_log

end QBP.Foundations.CDAlg
