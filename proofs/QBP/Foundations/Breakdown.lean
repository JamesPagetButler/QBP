/-
  QBP.Foundations.Breakdown
  =========================

  The structure-loss ladder of the Cayley–Dickson tower ℝ→ℂ→ℍ→𝕆→𝕊, with EVERY
  ✗ cell of the operations-complete matrix realised as a WITNESSED counterexample
  (a concrete Lean term whose defining inequality is closed by kernel `decide` /
  `norm_num` / structural `ring` — never a named witness in a comment, never a
  vacuous `True` stub).  This is the clean replacement for the deleted #471
  `Breakdown.lean` skeleton (480-B ruling; inventory + dispositions in issue #503).

  The matrix rows realised here (cell naming `<level>_<row>`):

    * ORDER       — ℂ, ℍ, 𝕆, 𝕊 carry no compatible total order.
        ℂ/ℍ are Mathlib `Ring`s: the one general lemma
        `no_linear_strict_order_of_sq_eq_neg_one` (an element `u` with `u·u = −1`
        ⟹ no `LinearOrder` whose induced order is an `IsStrictOrderedRing`) kills
        both via `Complex.I` and the quaternion `i`.
        𝕆/𝕊 = `CDAlg ℝ 3/4` are NOT `Ring`s (non-associative / non-alternative),
        so the Mathlib ordered-ring route does not apply.  Route chosen: (b) —
        state order-impossibility directly over `CDAlg ℝ n` from the concrete fact
        `e₁·e₁ = −1` (`e_imaginary_sq_eq_neg_one`), against the genuine
        ordered-additive-group compatibility (`IsOrderedAddMonoid` translation
        invariance) + squares-nonneg + `0 < 1`.  Reported in the module header.

    * COMMUTATIVITY ✗ at ℍ, 𝕆, 𝕊 — `quaternion_not_commutative` (Mathlib `i,j`),
        `octonion_not_commutative`, `sedenion_not_commutative` (CDAlg basis pairs,
        differing coordinate by `decide` on `mulCoeff`).

    * ASSOCIATIVITY ✗ at 𝕆, 𝕊 — `octonion_not_associative`,
        `sedenion_not_associative`: the basis triple (e₁,e₂,e₄) has associator
        coefficient 2 ≠ 0 (`decide` on `assocCoeffZ`) at index 7.

    * ALTERNATIVITY ✗ at 𝕊 — `sedenion_not_alternative` (wraps the existing
        witnessed result from `CDLifting`; cited, not duplicated).

    * NORM-COMPOSITION ✗ at 𝕊 — `sedenion_norm_not_multiplicative`: a zero-divisor
        pair `x,y` has `N(x·y) = 0` while `N x · N y = 4`.

    * DIVISION / ZERO-DIVISORS ✗ at 𝕊 — `sedenion_zero_divisors`: a constructed
        pair of nonzero sedenions with zero product (both coordinates by `decide`).

    * THE 42 STRUCTURE — `sedenion_basis_zero_divisor_plane_count_eq_42`: exactly
        42 of the basis planes {eₐ, e_b} (a ∈ 1..7, b ∈ 9..15) are LEFT
        zero-divisor planes (∃ partner & signs with vanishing product), computed
        by kernel `decide` over the sedenion product.  This is the genuine
        Moreno-grid count (cross-checked in Python: 7×7 − 7 = 42, and equal to the
        combinatorial `b ≠ a+8` count), tying "42" to the actual zero-divisor
        property rather than a lattice-point tally.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom — every result depends only on a subset of
  `{propext, Classical.choice, Quot.sound}`.
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Complex.Basic
import QBP.Foundations.CDLifting
import QBP.Foundations.SedenionOctonionCount

namespace QBP.Foundations.Breakdown

open QBP.Foundations.CDAlg

/-! ## 1. The order row — one lemma, four columns

In any `Ring A` carrying an element `u` with `u·u = −1`, there is no `LinearOrder`
whose induced partial order makes `A` an `IsStrictOrderedRing` (a linearly ordered
domain).  Proof: squares are nonneg, so `0 ≤ u·u = −1`, forcing `1 ≤ 0`, against
`0 < 1`.  The `IsStrictOrderedRing` is taken w.r.t. the EXISTENTIALLY-bound order's
`toPartialOrder`, so the claim is not vacuously weakened by any ambient order
instance already in scope (this matters for ℂ, which carries `Complex.partialOrder`
— the componentwise, non-linear `ComplexOrder`). -/

/-- **Order row (general).**  A `Ring` with `u·u = −1` admits no compatible total
    order: no `LinearOrder` whose induced order is an `IsStrictOrderedRing`. -/
theorem no_linear_strict_order_of_sq_eq_neg_one
    {A : Type*} [Ring A] (u : A) (hu : u * u = -1) :
    ¬ ∃ lo : LinearOrder A, @IsStrictOrderedRing A _ lo.toPartialOrder := by
  rintro ⟨lo, hsor⟩
  letI := lo
  letI := hsor
  have h1 : (0 : A) ≤ u * u := mul_self_nonneg u
  rw [hu] at h1
  have h1' : (1 : A) ≤ 0 := by have := neg_nonneg.mp h1; simpa using this
  exact absurd zero_lt_one (not_lt.mpr h1')

/-- **✗ order at ℂ** (`complex_order`).  ℂ carries no compatible total order
    (witnessed by `Complex.I`, `I·I = −1`). -/
theorem complex_no_linear_order :
    ¬ ∃ lo : LinearOrder ℂ, @IsStrictOrderedRing ℂ _ lo.toPartialOrder :=
  no_linear_strict_order_of_sq_eq_neg_one Complex.I Complex.I_mul_I

/-- **✗ order at ℍ** (`quaternion_order`).  ℍ carries no compatible total order
    (witnessed by the quaternion `i = ⟨0,1,0,0⟩`, `i·i = −1`). -/
theorem quaternion_no_linear_order :
    ¬ ∃ lo : LinearOrder (Quaternion ℝ),
      @IsStrictOrderedRing (Quaternion ℝ) _ lo.toPartialOrder := by
  apply no_linear_strict_order_of_sq_eq_neg_one (⟨0, 1, 0, 0⟩ : Quaternion ℝ)
  ext <;> simp

/-- An imaginary basis unit of `CDAlg ℝ n` squares to `−1`: `eᵢ·eᵢ = −1` for
    `i ≠ 0`.  Direct corollary of the Cayley–Dickson quadraticity identity
    `cdAlg_sq_eq` (Re eᵢ = 0, N eᵢ = 1). -/
theorem e_imaginary_sq_eq_neg_one (n : ℕ) (i : Fin (2^n)) (hi : i.val ≠ 0) :
    (e i * e i : CDAlg ℝ n) = -1 := by
  rw [cdAlg_sq_eq]
  have hc0 : (e i : CDAlg ℝ n).coord 0 = 0 := by
    simp only [e_coord]; rw [if_neg]
    intro h; apply hi; rw [← h]; rfl
  have hN : N (e i : CDAlg ℝ n) = 1 := by
    simp only [N_def, e_coord]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hc0, hN]; simp

/-- **Order row for the non-associative levels (𝕆/𝕊).**  Since `CDAlg ℝ n` is not
    a `Ring`, the Mathlib `IsStrictOrderedRing` route is unavailable; we state the
    genuine ordered-ring compatibility directly: there is no `LinearOrder` making
    `CDAlg ℝ n` a translation-invariant ordered additive group (`IsOrderedAddMonoid`)
    in which every square is nonneg and `0 < 1`, as soon as it has an imaginary
    basis unit.  The contradiction is `0 ≤ eᵢ·eᵢ = −1`. -/
theorem cdAlg_no_order (n : ℕ) (i : Fin (2^n)) (hi : i.val ≠ 0)
    (lo : LinearOrder (CDAlg ℝ n))
    (_ : @IsOrderedAddMonoid (CDAlg ℝ n) _ lo.toPartialOrder.toPreorder)
    (hsq : ∀ x : CDAlg ℝ n, lo.le 0 (x * x))
    (hpos : lo.lt 0 1) : False := by
  letI := lo
  letI := ‹IsOrderedAddMonoid (CDAlg ℝ n)›
  have h1 : (0 : CDAlg ℝ n) ≤ e i * e i := hsq (e i)
  rw [e_imaginary_sq_eq_neg_one n i hi] at h1
  have h1' : (1 : CDAlg ℝ n) ≤ 0 := by have := neg_nonneg.mp h1; simpa using this
  exact absurd (show (0 : CDAlg ℝ n) < 1 from hpos) (not_lt.mpr h1')

/-- **✗ order at 𝕆** (`octonion_order`).  𝕆 = `CDAlg ℝ 3` carries no compatible
    total order: instantiate `cdAlg_no_order` at the imaginary unit `e₁`. -/
theorem octonion_no_order
    (lo : LinearOrder (CDAlg ℝ 3))
    (hmon : @IsOrderedAddMonoid (CDAlg ℝ 3) _ lo.toPartialOrder.toPreorder)
    (hsq : ∀ x : CDAlg ℝ 3, lo.le 0 (x * x))
    (hpos : lo.lt 0 1) : False :=
  cdAlg_no_order 3 ⟨1, by norm_num⟩ (by norm_num) lo hmon hsq hpos

/-- **✗ order at 𝕊** (`sedenion_order`).  𝕊 = `CDAlg ℝ 4` carries no compatible
    total order: instantiate `cdAlg_no_order` at the imaginary unit `e₁`. -/
theorem sedenion_no_order
    (lo : LinearOrder (CDAlg ℝ 4))
    (hmon : @IsOrderedAddMonoid (CDAlg ℝ 4) _ lo.toPartialOrder.toPreorder)
    (hsq : ∀ x : CDAlg ℝ 4, lo.le 0 (x * x))
    (hpos : lo.lt 0 1) : False :=
  cdAlg_no_order 4 ⟨1, by norm_num⟩ (by norm_num) lo hmon hsq hpos

/-! ## 2. Commutativity ✗ at ℍ, 𝕆, 𝕊 -/

/-- **✗ commutativity at ℍ** (`quaternion_commutator`).  ℍ is non-commutative:
    `i·j ≠ j·i` (their `imK` components are `+1` and `−1`). -/
theorem quaternion_not_commutative :
    ∃ x y : Quaternion ℝ, x * y ≠ y * x := by
  refine ⟨⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ?_⟩
  intro h
  have hk := congrArg QuaternionAlgebra.imK h
  simp only [QuaternionAlgebra.mk_mul_mk] at hk
  norm_num at hk

/-- Generic CDAlg basis-pair non-commutativity, driven by a `decide`d coefficient
    inequality at the product index `i ⊕ j`.  Used for 𝕆 and 𝕊 below. -/
theorem cdAlg_basis_not_commute {n : ℕ} (i j k : Fin (2^n))
    (hk : (i ^^^ j) = k) (hk' : (j ^^^ i) = k)
    (hne : mulCoeff n i j ≠ mulCoeff n j i) :
    (e i * e j : CDAlg ℝ n) ≠ e j * e i := by
  intro h
  have hco := congrArg (fun z => z.coord k) h
  simp only [e_mul_e, smul_coord, e_coord, hk, hk', if_true, mul_one] at hco
  exact hne (by exact_mod_cast hco)

/-- **✗ commutativity at 𝕆** (`octonion_commutator`).  𝕆 = `CDAlg ℝ 3` is
    non-commutative: `e₁·e₂ ≠ e₂·e₁` (coefficients `+1` vs `−1` at index 3). -/
theorem octonion_not_commutative :
    ∃ x y : CDAlg ℝ 3, x * y ≠ y * x :=
  ⟨e ⟨1, by norm_num⟩, e ⟨2, by norm_num⟩,
    cdAlg_basis_not_commute ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ ⟨3, by norm_num⟩
      (by decide) (by decide) (by decide)⟩

/-- **✗ commutativity at 𝕊** (`sedenion_commutator`).  𝕊 = `CDAlg ℝ 4` is
    non-commutative: `e₁·e₂ ≠ e₂·e₁` (coefficients `+1` vs `−1` at index 3). -/
theorem sedenion_not_commutative :
    ∃ x y : CDAlg ℝ 4, x * y ≠ y * x :=
  ⟨e ⟨1, by norm_num⟩, e ⟨2, by norm_num⟩,
    cdAlg_basis_not_commute ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ ⟨3, by norm_num⟩
      (by decide) (by decide) (by decide)⟩

/-! ## 3. Associativity ✗ at 𝕆, 𝕊

The basis triple (e₁, e₂, e₄) has associator coefficient `assocCoeffZ = 2 ≠ 0`
(kernel `decide`) at index `1 ⊕ 2 ⊕ 4 = 7`, so `(e₁·e₂)·e₄ ≠ e₁·(e₂·e₄)`. -/

/-- Generic CDAlg basis-triple non-associativity from a `decide`d nonzero
    associator coefficient. -/
theorem cdAlg_basis_not_associate {n : ℕ} (i j k : Fin (2^n))
    (hc : assocCoeffZ n i j k ≠ 0) :
    (e i * e j : CDAlg ℝ n) * e k ≠ e i * (e j * e k) := by
  intro h
  have hzero : assoc (e i) (e j) (e k) = (0 : CDAlg ℝ n) := by
    rw [assoc, h, sub_self]
  have hco := congrArg (fun z => z.coord (i ^^^ j ^^^ k)) hzero
  simp only [assoc_e, smul_coord, e_coord, if_true, mul_one, zero_coord] at hco
  exact hc (by exact_mod_cast hco)

/-- **✗ associativity at 𝕆** (`octonion_associator`).  𝕆 = `CDAlg ℝ 3` is
    non-associative: `(e₁·e₂)·e₄ ≠ e₁·(e₂·e₄)` (associator coefficient 2 ≠ 0). -/
theorem octonion_not_associative :
    ∃ x y z : CDAlg ℝ 3, (x * y) * z ≠ x * (y * z) :=
  ⟨e ⟨1, by norm_num⟩, e ⟨2, by norm_num⟩, e ⟨4, by norm_num⟩,
    cdAlg_basis_not_associate ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ ⟨4, by norm_num⟩
      (by decide)⟩

/-- **✗ associativity at 𝕊** (`sedenion_associator`).  𝕊 = `CDAlg ℝ 4` is
    non-associative: `(e₁·e₂)·e₄ ≠ e₁·(e₂·e₄)` (associator coefficient 2 ≠ 0). -/
theorem sedenion_not_associative :
    ∃ x y z : CDAlg ℝ 4, (x * y) * z ≠ x * (y * z) :=
  ⟨e ⟨1, by norm_num⟩, e ⟨2, by norm_num⟩, e ⟨4, by norm_num⟩,
    cdAlg_basis_not_associate ⟨1, by norm_num⟩ ⟨2, by norm_num⟩ ⟨4, by norm_num⟩
      (by decide)⟩

/-! ## 4. Alternativity ✗ at 𝕊 (cite the existing witnessed result) -/

/-- **✗ alternativity at 𝕊** (`sedenion_alternativity`).  𝕊 = `CDAlg ℝ 4` is NOT
    alternative: `∃ x y, (x·x)·y ≠ x·(x·y)`.  This wraps the existing witnessed
    result `CDAlg.sedenion_not_alternative` (witness `x = e₁ + e₁₀`, `y = e₄`,
    associator coordinate 2 ≠ 0 at index 15) under the matrix-cell name — cited,
    not duplicated. -/
theorem sedenion_not_alternative :
    ∃ x y : CDAlg ℝ 4, (x * x) * y ≠ x * (x * y) :=
  CDAlg.sedenion_not_alternative

/-! ## 5. Norm-composition ✗ and division/zero-divisors ✗ at 𝕊

A constructed zero-divisor pair `x = e₂ + e₉`, `y = e₄ + e₁₅` (the normal-9
witness from `SedenionOctonionCount`, re-expressed in `CDAlg ℝ 4`): both nonzero,
`x·y = 0`.  Hence `N(x·y) = N 0 = 0` while `N x · N y = 2·2 = 4`, breaking norm
composition; and `x,y` are zero divisors, breaking division. -/

/-- The first zero-divisor factor `x = e₂ + e₉ : CDAlg ℝ 4`. -/
def zdX : CDAlg ℝ 4 := e ⟨2, by norm_num⟩ + e ⟨9, by norm_num⟩
/-- The second zero-divisor factor `y = e₄ + e₁₅ : CDAlg ℝ 4`. -/
def zdY : CDAlg ℝ 4 := e ⟨4, by norm_num⟩ + e ⟨15, by norm_num⟩

/-- `x = e₂ + e₉ ≠ 0` (coordinate 2 is 1). -/
theorem zdX_ne_zero : zdX ≠ 0 := by
  intro h
  have := congrArg (fun z => z.coord ⟨2, by norm_num⟩) h
  simp only [zdX, add_coord, e_coord, zero_coord] at this
  norm_num at this

/-- `y = e₄ + e₁₅ ≠ 0` (coordinate 4 is 1). -/
theorem zdY_ne_zero : zdY ≠ 0 := by
  intro h
  have := congrArg (fun z => z.coord ⟨4, by norm_num⟩) h
  simp only [zdY, add_coord, e_coord, zero_coord] at this
  norm_num at this

/-- The product `x·y = 0` in `CDAlg ℝ 4`.  Expanded by bilinearity into the four
    basis products, whose every coordinate vanishes (`decide` on the integer
    coefficient / `mulCoeff` per coordinate). -/
theorem zdX_mul_zdY_eq_zero : zdX * zdY = (0 : CDAlg ℝ 4) := by
  have hexp : zdX * zdY
      = (e ⟨2, by norm_num⟩ * e ⟨4, by norm_num⟩
          + e ⟨2, by norm_num⟩ * e ⟨15, by norm_num⟩)
        + (e ⟨9, by norm_num⟩ * e ⟨4, by norm_num⟩
          + e ⟨9, by norm_num⟩ * e ⟨15, by norm_num⟩) := by
    rw [zdX, zdY, mul_add_left, mul_add_right, mul_add_right]
  rw [hexp]
  ext k
  simp only [e_mul_e, add_coord, smul_coord, e_coord, zero_coord]
  -- the four basis products and their indices
  have x1 : ((⟨2, by norm_num⟩ : Fin (2^4)) ^^^ ⟨4, by norm_num⟩) = ⟨6, by norm_num⟩ := by decide
  have x2 : ((⟨2, by norm_num⟩ : Fin (2^4)) ^^^ ⟨15, by norm_num⟩) = ⟨13, by norm_num⟩ := by decide
  have x3 : ((⟨9, by norm_num⟩ : Fin (2^4)) ^^^ ⟨4, by norm_num⟩) = ⟨13, by norm_num⟩ := by decide
  have x4 : ((⟨9, by norm_num⟩ : Fin (2^4)) ^^^ ⟨15, by norm_num⟩) = ⟨6, by norm_num⟩ := by decide
  rw [x1, x2, x3, x4]
  -- coefficients: index 6 pair (2,4)+(9,15) cancels; index 13 pair (2,15)+(9,4) cancels
  have c1 : (mulCoeff 4 ⟨2, by norm_num⟩ ⟨4, by norm_num⟩ : ℝ)
              = -(mulCoeff 4 ⟨9, by norm_num⟩ ⟨15, by norm_num⟩ : ℝ) := by
    have : mulCoeff 4 ⟨2, by norm_num⟩ ⟨4, by norm_num⟩
            = - mulCoeff 4 ⟨9, by norm_num⟩ ⟨15, by norm_num⟩ := by decide
    exact_mod_cast this
  have c2 : (mulCoeff 4 ⟨2, by norm_num⟩ ⟨15, by norm_num⟩ : ℝ)
              = -(mulCoeff 4 ⟨9, by norm_num⟩ ⟨4, by norm_num⟩ : ℝ) := by
    have : mulCoeff 4 ⟨2, by norm_num⟩ ⟨15, by norm_num⟩
            = - mulCoeff 4 ⟨9, by norm_num⟩ ⟨4, by norm_num⟩ := by decide
    exact_mod_cast this
  by_cases h6 : k = (⟨6, by norm_num⟩ : Fin (2^4))
  · have h13 : k ≠ (⟨13, by norm_num⟩ : Fin (2^4)) := by
      rw [h6]; decide
    rw [if_pos h6, if_neg h13, c1]; ring
  · by_cases h13 : k = (⟨13, by norm_num⟩ : Fin (2^4))
    · rw [if_neg h6, if_pos h13, c2]; ring
    · rw [if_neg h6, if_neg h13]; ring

/-- **✗ division / zero-divisors at 𝕊** (`sedenion_inverse`).  𝕊 = `CDAlg ℝ 4` has
    zero divisors: `∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ x·y = 0` (so it is not a division
    algebra).  Witness `x = e₂ + e₉`, `y = e₄ + e₁₅`. -/
theorem sedenion_zero_divisors :
    ∃ x y : CDAlg ℝ 4, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 :=
  ⟨zdX, zdY, zdX_ne_zero, zdY_ne_zero, zdX_mul_zdY_eq_zero⟩

/-- `N(eₚ + e_q) = 2` for distinct basis indices `p ≠ q` (two unit coordinates). -/
theorem N_e_add_e {n : ℕ} (p q : Fin (2^n)) (hpq : p ≠ q) :
    N (e p + e q : CDAlg ℝ n) = 2 := by
  simp only [N_def]
  rw [Finset.sum_congr rfl (g := fun i =>
        (if i = p then (1:ℝ) else 0) + (if i = q then (1:ℝ) else 0))
      (fun i _ => ?_), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ p (fun _ => (1:ℝ)),
      Finset.sum_ite_eq' Finset.univ q (fun _ => (1:ℝ))]
  · norm_num
  · simp only [add_coord, e_coord]
    by_cases hp : i = p
    · rw [if_pos hp, if_neg (by rw [hp]; exact hpq)]; ring
    · by_cases hq : i = q
      · rw [if_neg hp, if_pos hq]; ring
      · rw [if_neg hp, if_neg hq]; ring

/-- `N(e₂ + e₉) = 2`. -/
theorem N_zdX : N zdX = 2 := N_e_add_e _ _ (by decide)

/-- `N(e₄ + e₁₅) = 2`. -/
theorem N_zdY : N zdY = 2 := N_e_add_e _ _ (by decide)

/-- **✗ norm composition at 𝕊** (`sedenion_norm`).  The norm form is NOT
    multiplicative on 𝕊 = `CDAlg ℝ 4`: `∃ x y, N(x·y) ≠ N x · N y`.  For the
    zero-divisor pair `x = e₂ + e₉`, `y = e₄ + e₁₅`: `N(x·y) = N 0 = 0`, while
    `N x · N y = 2·2 = 4 ≠ 0`. -/
theorem sedenion_norm_not_multiplicative :
    ∃ x y : CDAlg ℝ 4, N (x * y) ≠ N x * N y := by
  refine ⟨zdX, zdY, ?_⟩
  rw [zdX_mul_zdY_eq_zero, N_zdX, N_zdY]
  simp only [N_def, zero_coord]
  norm_num

/-! ## 6. The 42 structure — sedenion zero-divisor planes

The genuine Moreno-grid count.  A basis plane {eₐ, e_b} with `a ∈ {1..7}`,
`b ∈ {9..15}` is a LEFT zero-divisor plane iff some `(e_a ± e_b)·(e_c ± e_d) = 0`
for partner indices `c ∈ {1..7}`, `d ∈ {9..15}` and signs in `{±1}`.  Exactly 42
of the 49 planes qualify (the 7 excluded are `b = a + 8`).  The product is
computed via the kernel-verified `SedenionOctonionCount.prodIsZero` over the CD
sedenion sign table; the count is closed by kernel `decide`.

Python cross-check (genuine semantic count, not a lattice tally):
`|{(a,b) : a∈1..7, b∈9..15, ∃ partner & signs with product 0}| = 42`, equal to
`|{(a,b) : a∈1..7, b∈9..15, b ≠ a+8}| = 7×7 − 7 = 42`. -/

open QBP.Foundations.SedenionOctonionCount in
/-- `(e_a + s_b·e_b)·(e_c + s_d·e_d) = 0` as a sedenion product (Bool), via the
    kernel-verified sparse-element product `prodIsZero`. -/
def planeProdZeroB (a b c d : Fin 16) (sb sd : Int) : Bool :=
  decide (prodIsZero [(1, a), (sb, b)] [(1, c), (sd, d)])

/-- Left index range `a ∈ {1..7}`. -/
def aRange : List (Fin 16) := [1, 2, 3, 4, 5, 6, 7]
/-- Right index range `b ∈ {9..15}`. -/
def bRange : List (Fin 16) := [9, 10, 11, 12, 13, 14, 15]
/-- The two unit signs. -/
def signs : List Int := [1, -1]

/-- `{eₐ, e_b}` (a ∈ 1..7, b ∈ 9..15) is a LEFT zero-divisor plane: some partner
    `c ∈ 1..7`, `d ∈ 9..15` and signs `s_b, s_d ∈ {±1}` give a vanishing product. -/
def isLeftZDplane (a b : Fin 16) : Bool :=
  signs.any (fun sb => signs.any (fun sd =>
    aRange.any (fun c => bRange.any (fun d =>
      planeProdZeroB a b c d sb sd))))

/-- The count of basis planes `{eₐ, e_b}` (a ∈ 1..7, b ∈ 9..15) that are left
    zero-divisor planes. -/
def zdPlaneCount : Nat :=
  (aRange.flatMap (fun a => bRange.map (fun b => (a, b)))).countP
    (fun p => isLeftZDplane p.1 p.2)

set_option maxHeartbeats 1000000 in
/-- **THE 42 STRUCTURE** (`sedenion_zero_divisor_42`).  Exactly 42 of the 49 basis
    planes `{eₐ, e_b}` (a ∈ 1..7, b ∈ 9..15) of the Cayley–Dickson sedenion frame
    are LEFT zero-divisor planes — kernel `decide` over the genuine sedenion
    product.  This is the Moreno count: the 7 non-planes are exactly those with
    `b = a + 8`. -/
theorem sedenion_basis_zero_divisor_plane_count_eq_42 : zdPlaneCount = 42 := by decide

/-! ## 7. Completeness audit — `#print axioms`

Each result must depend only on a subset of the three standard axioms
`{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no native/reduceBool
axiom).  Reported in the build log. -/

#print axioms no_linear_strict_order_of_sq_eq_neg_one
#print axioms complex_no_linear_order
#print axioms quaternion_no_linear_order
#print axioms e_imaginary_sq_eq_neg_one
#print axioms cdAlg_no_order
#print axioms octonion_no_order
#print axioms sedenion_no_order
#print axioms quaternion_not_commutative
#print axioms octonion_not_commutative
#print axioms sedenion_not_commutative
#print axioms octonion_not_associative
#print axioms sedenion_not_associative
#print axioms sedenion_not_alternative
#print axioms sedenion_zero_divisors
#print axioms sedenion_norm_not_multiplicative
#print axioms sedenion_basis_zero_divisor_plane_count_eq_42

end QBP.Foundations.Breakdown
