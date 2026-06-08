/-
  QBP.Foundations.CrossProduct
  ============================

  The cross-product row of the operations-complete property matrix (#474):
  the 3-dimensional cross product on `Im ℍ` and the 7-dimensional cross product on
  `Im 𝕆`.  The matrix row is  ℝ:— ℂ:— ℍ:✓ 𝕆:✓ 𝕊:—  — there is NO sedenion cross
  product, and this file does not invent one (see §5 docstring: the
  composition-algebra structure the cross product needs fails at 𝕊, cited from
  `Breakdown.sedenion_norm_not_multiplicative`).

  Definition chosen (reported): the **half-commutator**
      `x ×ₙ y := ½ · (x·y − y·x)`
  on the Cayley–Dickson carrier `CDAlg ℝ n`.  On pure (imaginary) elements this
  is exactly the classical cross product (the imaginary part of the product); on
  ℍ (`n = 2`) it is the 3D cross product, on 𝕆 (`n = 3`) the 7D cross product.
  Working inside `CDAlg` (rather than Mathlib `Quaternion` / `crossProduct`) keeps
  the cross product, the bilinear form `bil`, and the norm `N` on ONE carrier, so
  orthogonality and the Lagrange norm identity are stated against the same `bil`
  that `NormForm` / `OctonionLaws` use, and so 3D and 7D are the SAME definition at
  two levels.  (Connection to Mathlib `crossProduct` is therefore not used; the
  identification ℍ-half-commutator ↔ Mathlib `crossProduct` is a separate optional
  bridge, not needed for the matrix cells — reported, not built.)

  Results:
    * `cross_reCoord_zero` — the half-commutator is always pure (its real part is 0,
      for ALL x y — the commutator's `coord 0` vanishes by commutativity of `R`).
    * `cross_antisymm` — `x ×ₙ y = − (y ×ₙ x)`  (commutator antisymmetry; all n).
    * `cross_self` — `x ×ₙ x = 0`.
    * **Orthogonality** `bil (x ×ₙ y) x = 0 = bil (x ×ₙ y) y`:
      - ℍ (`n = 2`): `quaternion_cross_orthogonal_*`.
      - 𝕆 (`n = 3`): `octonion_cross_orthogonal_*`.
      via the trilinear keystone (`lift_trilinear_eq`) + a kernel-`decide`d basis
      fact (the polarized scalar identity `⟨[a,y],b⟩ + ⟨[b,y],a⟩ = 0`).
    * **Lagrange norm identity** for pure `x y`
      `N (x ×ₙ y) = N x · N y − (bil x y)²`:
      - ℍ (`n = 2`): `quaternion_cross_norm_identity`.
      - 𝕆 (`n = 3`): `octonion_cross_norm_identity`.
      Proved STRUCTURALLY (no 4-linear decide) from: the polarized Cayley–Dickson
      square identity (`CDAlg.cdAlg_sq_eq`, polarized here to `cdAlg_polar_sq`),
      the norm-composition law (`octonion_norm_composition` / quaternion analogue),
      and the additive norm-polarization `N(a−b) = N a + N b − 2⟨a,b⟩`.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom — every result depends only on
  `{propext, Classical.choice, Quot.sound}`.
-/
import QBP.Foundations.OctonionLaws
import QBP.Foundations.Breakdown

namespace QBP.Foundations.CrossProduct

-- The `crossOrthMap`/`normMap` multilinearity proofs use ONE uniform bilinearity
-- simp-list per slot; per slot some entries are genuinely unused.  Same trade-off
-- (uniform list > minimal-per-case) as `OctonionLaws`; disable the STYLE linter.
set_option linter.unusedSimpArgs false

open QBP.Foundations.CDAlg

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `bil` is additive-over-subtraction in the left slot. -/
theorem bil_sub_left (x x' y : CDAlg R n) : bil (x - x') y = bil x y - bil x' y := by
  rw [sub_eq_add_neg, bil_add_left, show (-x') = (-1 : R) • x' by rw [neg_one_smul],
    bil_smul_left]; ring

/-- `bil` is additive-over-subtraction in the right slot. -/
theorem bil_sub_right (x y y' : CDAlg R n) : bil x (y - y') = bil x y - bil x y' := by
  rw [sub_eq_add_neg, bil_add_right, show (-y') = (-1 : R) • y' by rw [neg_one_smul],
    bil_smul_right]; ring

/-! ## 0. Generic scalar identities on `CDAlg`

Two structural facts used throughout, both general (any level, any `CommRing`/ℝ):
the additive polarization of `N`, and the polarized Cayley–Dickson square. -/

/-- **Additive norm polarization:** `N (a + b) = N a + N b + 2 ⟨a,b⟩`.  (`N` is the
    quadratic form of the polar bilinear form `bil`.) -/
theorem N_add (a b : CDAlg R n) : N (a + b) = N a + N b + 2 * bil a b := by
  have h : N a + N b + 2 * bil a b
      = ∑ i, ((a.coord i)^2 + (b.coord i)^2 + 2 * (a.coord i * b.coord i)) := by
    rw [N_def, N_def, bil_def, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  rw [h, N_def]
  exact Finset.sum_congr rfl (fun i _ => by simp only [add_coord]; ring)

/-- **Norm of a difference:** `N (a − b) = N a + N b − 2 ⟨a,b⟩`. -/
theorem N_sub (a b : CDAlg R n) : N (a - b) = N a + N b - 2 * bil a b := by
  have h : N a + N b - 2 * bil a b
      = ∑ i, ((a.coord i)^2 + (b.coord i)^2 - 2 * (a.coord i * b.coord i)) := by
    rw [N_def, N_def, bil_def, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
  rw [h, N_def]
  exact Finset.sum_congr rfl (fun i _ => by simp only [sub_coord]; ring)

/-- `N (r • x) = r² · N x` (homogeneity of degree 2). -/
theorem N_smul (r : R) (x : CDAlg R n) : N (r • x) = r^2 * N x := by
  simp only [N_def, smul_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Polarized Cayley–Dickson square** (over ℝ): polarizing
    `cdAlg_sq_eq : x·x = (2 x₀)•x − N x•1` gives, for all `x y`,
    `x·y + y·x = (2 x₀)•y + (2 y₀)•x − (2 ⟨x,y⟩)•1`.  No purity, no lift — a direct
    polarization of the existing quadraticity theorem. -/
theorem cdAlg_polar_sq (x y : CDAlg ℝ n) :
    x * y + y * x = (2 * x.coord 0) • y + (2 * y.coord 0) • x - (2 * bil x y) • 1 := by
  have hxy := cdAlg_sq_eq (x + y)
  have hx := cdAlg_sq_eq x
  have hy := cdAlg_sq_eq y
  -- expand (x+y)(x+y) = xx + xy + yx + yy
  rw [mul_add_left, mul_add_right, mul_add_right] at hxy
  -- N(x+y) = N x + N y + 2⟨x,y⟩, (x+y).coord 0 = x₀ + y₀
  rw [N_add, add_coord] at hxy
  -- substitute the diagonal squares and solve for xy + yx
  rw [hx, hy] at hxy
  -- hxy now relates (… + xy + yx + …) to a smul/sub expression; isolate xy + yx
  -- bring everything to a module identity and finish with `abel`/smul algebra
  have key : x * y + y * x
      = ((2 * (x.coord 0 + y.coord 0)) • (x + y) - (N x + N y + 2 * bil x y) • 1)
        - ((2 * x.coord 0) • x - N x • 1) - ((2 * y.coord 0) • y - N y • 1) := by
    rw [← hxy]; abel
  rw [key]
  simp only [smul_add, add_smul, mul_add]
  abel

/-! ## 1. The cross product (half-commutator) -/

/-- The cross product on `CDAlg ℝ n`: the half-commutator `x ×ₙ y = ½(x·y − y·x)`.
    On pure (imaginary) elements this is the classical 3D (n=2) / 7D (n=3) cross
    product. -/
noncomputable def cross (x y : CDAlg ℝ n) : CDAlg ℝ n := (2⁻¹ : ℝ) • (x * y - y * x)

@[simp] theorem cross_def (x y : CDAlg ℝ n) :
    cross x y = (2⁻¹ : ℝ) • (x * y - y * x) := rfl

/-- The commutator's real coordinate vanishes for ALL `x y`:
    `(x·y − y·x).coord 0 = 0`.  (Both products share the same `coord 0`,
    `∑ᵢ mulCoeffᵢᵢ xᵢ yᵢ`, by commutativity of ℝ.) -/
theorem commutator_reCoord_zero (x y : CDAlg ℝ n) :
    (x * y - y * x).coord 0 = 0 := by
  rw [sub_coord, mul_coord_single, mul_coord_single]
  simp only [xor_zero_right]
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The cross product is always pure: `(x ×ₙ y).coord 0 = 0`. -/
theorem cross_reCoord_zero (x y : CDAlg ℝ n) : (cross x y).coord 0 = 0 := by
  rw [cross_def, smul_coord, commutator_reCoord_zero, mul_zero]

/-- **Antisymmetry:** `x ×ₙ y = − (y ×ₙ x)` (all `n`). -/
theorem cross_antisymm (x y : CDAlg ℝ n) : cross x y = - cross y x := by
  rw [cross_def, cross_def, ← smul_neg, neg_sub]

/-- `x ×ₙ x = 0`. -/
theorem cross_self (x : CDAlg ℝ n) : cross x x = 0 := by
  rw [cross_def, sub_self, smul_zero]

/-! ## 2. Orthogonality via the trilinear keystone

We prove the polarized scalar identity `⟨[a,y],b⟩ + ⟨[b,y],a⟩ = 0` on all basis
triples (`decide` on the integer coefficient), lift it trilinearly, and read off
`⟨[x,y],x⟩ = 0` on the diagonal `a = b = x`.  Then
`⟨x ×ₙ y, x⟩ = ½⟨[x,y],x⟩ = 0`. -/

/-- The scalar `⟨[a,y],b⟩ = ⟨a·y − y·a, b⟩`, packed into `e₀` so the CDAlg-valued
    trilinear lift applies.  `crossOrthMap a y b = (⟨[a,y],b⟩ + ⟨[b,y],a⟩) • e₀`. -/
def crossOrthMap (a y b : CDAlg R n) : CDAlg R n :=
  (bil (a * y - y * a) b + bil (b * y - y * b) a) • e 0

theorem crossOrthMap_trilinear : IsTrilinear (crossOrthMap : CDAlg R n → _ → _ → _) where
  add_left a a' y b := by
    simp only [crossOrthMap, mul_add_left, mul_add_right, bil_add_left, bil_add_right,
      bil_sub_left, bil_sub_right]
    rw [← add_smul]; congr 1; ring
  smul_left r a y b := by
    simp only [crossOrthMap, mul_smul_left, mul_smul_right, bil_smul_left,
      bil_smul_right, bil_sub_left, bil_sub_right, smul_smul]
    congr 1; ring
  add_mid a y y' b := by
    simp only [crossOrthMap, mul_add_left, mul_add_right, bil_add_left, bil_add_right,
      bil_sub_left, bil_sub_right]
    rw [← add_smul]; congr 1; ring
  smul_mid r a y b := by
    simp only [crossOrthMap, mul_smul_left, mul_smul_right, bil_smul_left,
      bil_smul_right, bil_sub_left, bil_sub_right, smul_smul]
    congr 1; ring
  add_right a y b b' := by
    simp only [crossOrthMap, mul_add_left, mul_add_right, bil_add_left, bil_add_right,
      bil_sub_left, bil_sub_right]
    rw [← add_smul]; congr 1; ring
  smul_right r a y b := by
    simp only [crossOrthMap, mul_smul_left, mul_smul_right, bil_smul_left,
      bil_smul_right, bil_sub_left, bil_sub_right, smul_smul]
    congr 1; ring

/-- Integer coefficient of `crossOrthMap` on basis triples.
    `⟨eₐ·e_y − e_y·eₐ, e_b⟩ = (mc a y − mc y a)·δ_{a⊕y, b}`, so the polarized sum is
    `(mc a y − mc y a)·δ_{a⊕y,b} + (mc b y − mc y b)·δ_{b⊕y,a}`. -/
def crossOrthCoeffZ (n : ℕ) (a y b : Fin (2^n)) : Int :=
  (mulCoeff n a y * (if (a ^^^ y) = b then 1 else 0)
    - mulCoeff n y a * (if (y ^^^ a) = b then 1 else 0))
  + (mulCoeff n b y * (if (b ^^^ y) = a then 1 else 0)
    - mulCoeff n y b * (if (y ^^^ b) = a then 1 else 0))

theorem crossOrthMap_e (a y b : Fin (2^n)) :
    (crossOrthMap (e a) (e y) (e b) : CDAlg ℝ n)
      = ((crossOrthCoeffZ n a y b : Int) : ℝ) • e 0 := by
  unfold crossOrthMap
  rw [e_mul_e, e_mul_e, e_mul_e, e_mul_e,
    bil_sub_left, bil_sub_left,
    bil_smul_left, bil_smul_left, bil_smul_left, bil_smul_left,
    bil_e, bil_e, bil_e, bil_e]
  rw [crossOrthCoeffZ]
  congr 1
  push_cast
  ring

/-- **Integer basis fact (kernel `decide`, 8³ = 512 cases).**  The polarized cross
    orthogonality coefficient vanishes on every octonion basis triple. -/
theorem octonion_crossOrthCoeffZ_zero :
    ∀ a y b : Fin (2^3), crossOrthCoeffZ 3 a y b = 0 := by decide

/-- **Integer basis fact (kernel `decide`, 4³ = 64 cases).**  …and on every
    quaternion basis triple. -/
theorem quaternion_crossOrthCoeffZ_zero :
    ∀ a y b : Fin (2^2), crossOrthCoeffZ 2 a y b = 0 := by decide

theorem octonion_crossOrthMap_basis (a y b : Fin (2^3)) :
    (crossOrthMap (e a) (e y) (e b) : CDAlg ℝ 3) = 0 := by
  rw [crossOrthMap_e, octonion_crossOrthCoeffZ_zero]; simp

theorem quaternion_crossOrthMap_basis (a y b : Fin (2^2)) :
    (crossOrthMap (e a) (e y) (e b) : CDAlg ℝ 2) = 0 := by
  rw [crossOrthMap_e, quaternion_crossOrthCoeffZ_zero]; simp

/-- Polarized cross orthogonality, lifted (𝕆): `⟨[a,y],b⟩ + ⟨[b,y],a⟩ = 0` packed in
    `e₀`, for all `a y b`. -/
theorem octonion_crossOrthMap_zero (a y b : CDAlg ℝ 3) : crossOrthMap a y b = 0 :=
  lift_trilinear_eq crossOrthMap_trilinear octonion_crossOrthMap_basis a y b

theorem quaternion_crossOrthMap_zero (a y b : CDAlg ℝ 2) : crossOrthMap a y b = 0 :=
  lift_trilinear_eq crossOrthMap_trilinear quaternion_crossOrthMap_basis a y b

/-- The scalar payoff of the lift: `⟨a·y − y·a, b⟩ + ⟨b·y − y·b, a⟩ = 0`.  (Read off
    the `e₀` coordinate of `crossOrthMap = 0`.) -/
theorem crossOrth_scalar_octonion (a y b : CDAlg ℝ 3) :
    bil (a * y - y * a) b + bil (b * y - y * b) a = 0 := by
  have h := octonion_crossOrthMap_zero a y b
  have hc : (crossOrthMap a y b).coord 0 = 0 := by rw [h]; rfl
  rw [crossOrthMap, smul_coord, e_coord, if_pos rfl, mul_one] at hc
  exact hc

theorem crossOrth_scalar_quaternion (a y b : CDAlg ℝ 2) :
    bil (a * y - y * a) b + bil (b * y - y * b) a = 0 := by
  have h := quaternion_crossOrthMap_zero a y b
  have hc : (crossOrthMap a y b).coord 0 = 0 := by rw [h]; rfl
  rw [crossOrthMap, smul_coord, e_coord, if_pos rfl, mul_one] at hc
  exact hc

/-- The diagonal `⟨[x,y],x⟩ = 0` (𝕆): set `a = b = x`, ÷2 over ℝ. -/
theorem commutator_orth_octonion (x y : CDAlg ℝ 3) : bil (x * y - y * x) x = 0 := by
  have h := crossOrth_scalar_octonion x y x
  linarith [h]

theorem commutator_orth_quaternion (x y : CDAlg ℝ 2) : bil (x * y - y * x) x = 0 := by
  have h := crossOrth_scalar_quaternion x y x
  linarith [h]

/-- **𝕆 cross orthogonality (left arg):** `⟨x ×₃ y, x⟩ = 0`. -/
theorem octonion_cross_orthogonal_left (x y : CDAlg ℝ 3) : bil (cross x y) x = 0 := by
  rw [cross_def, bil_smul_left, commutator_orth_octonion, mul_zero]

/-- **𝕆 cross orthogonality (right arg):** `⟨x ×₃ y, y⟩ = 0`. -/
theorem octonion_cross_orthogonal_right (x y : CDAlg ℝ 3) : bil (cross x y) y = 0 := by
  rw [cross_antisymm,
    show (- cross y x) = (-1 : ℝ) • cross y x by rw [neg_one_smul], bil_smul_left,
    octonion_cross_orthogonal_left]; ring

/-- **ℍ cross orthogonality (left arg):** `⟨x ×₂ y, x⟩ = 0`. -/
theorem quaternion_cross_orthogonal_left (x y : CDAlg ℝ 2) : bil (cross x y) x = 0 := by
  rw [cross_def, bil_smul_left, commutator_orth_quaternion, mul_zero]

/-- **ℍ cross orthogonality (right arg):** `⟨x ×₂ y, y⟩ = 0`. -/
theorem quaternion_cross_orthogonal_right (x y : CDAlg ℝ 2) : bil (cross x y) y = 0 := by
  rw [cross_antisymm]
  rw [show (- cross y x) = (-1 : ℝ) • cross y x by rw [neg_one_smul], bil_smul_left]
  rw [quaternion_cross_orthogonal_left]; ring

/-! ## 3. The Lagrange norm identity for pure elements

For pure `x y` (real coordinate 0):
  `N(x ×ₙ y) = N x · N y − ⟨x,y⟩²`.

Structural proof (no 4-linear decide):
  `cross x y = ½(xy − yx)`, so `N(cross x y) = ¼ N(xy − yx)`.
  `N(xy − yx) = N(xy) + N(yx) − 2⟨xy, yx⟩`  (`N_sub`).
  For pure `x y`, the polarized square `cdAlg_polar_sq` gives `xy + yx = −2⟨x,y⟩•1`,
  i.e. `yx = −2⟨x,y⟩•1 − xy`; substitute and use `N(xy) = N(yx) = N x·N y`
  (norm composition) plus the explicit `⟨xy, yx⟩` reduction. -/

/-- **The coordinate form equals the conjugate form (general `n`).**
    `⟨x,y⟩ = ∑ᵢ xᵢyᵢ = (x · ȳ).coord 0`.  (Same fact as `NormForm`'s
    `bil_eq_reCoord_mul_conj`, proved inline here to keep `CrossProduct` independent
    of `NormForm`.) -/
theorem bil_eq_coord0_mul_conj (x y : CDAlg R n) :
    bil x y = (x * conj y).coord 0 := by
  rw [mul_coord_single]
  simp only [xor_zero_right, bil_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulCoeff_self, conj_coord]
  by_cases hi : i.val = 0
  · simp only [hi, if_true]; push_cast; ring
  · simp only [hi, if_false]; push_cast; ring

/-- Real coordinate of a product of PURE elements is `−⟨x,y⟩` (𝕆/ℍ; general n over
    ℝ given purity): from `⟨x,y⟩ = (x · ȳ).coord 0` and `conj y = −y` when `y` is
    pure. -/
theorem reCoord_mul_pure (x y : CDAlg ℝ n)
    (hy : y.coord 0 = 0) : (x * y).coord 0 = - bil x y := by
  -- ⟨x,y⟩ = (x * conj y).coord 0; for pure y, conj y = - y
  have hconj : conj y = - y := by
    ext i
    rw [conj_coord, neg_coord]
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext hi
      rw [if_pos hi, this, hy]; ring
    · rw [if_neg hi]
  rw [bil_eq_coord0_mul_conj, hconj,
    show (- y) = (-1 : ℝ) • y by rw [neg_one_smul], mul_smul_right, smul_coord]
  ring

/-- **𝕆 Lagrange identity.**  For pure `x y : CDAlg ℝ 3`
    (`x.coord 0 = 0`, `y.coord 0 = 0`):
    `N (x ×₃ y) = N x · N y − ⟨x,y⟩²`. -/
theorem octonion_cross_norm_identity (x y : CDAlg ℝ 3)
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    N (cross x y) = N x * N y - (bil x y)^2 := by
  -- N(cross) = ¼ N(xy - yx)
  rw [cross_def, N_smul, N_sub]
  -- N(xy) = N x N y, N(yx) = N y N x  (norm composition)
  rw [QBP.Foundations.CDAlg.octonion_norm_composition x y,
      QBP.Foundations.CDAlg.octonion_norm_composition y x]
  -- reduce ⟨xy, yx⟩ using the polarized square: yx = -(2⟨x,y⟩)•1 - xy
  have hpolar : x * y + y * x = - ((2 * bil x y) • (1 : CDAlg ℝ 3)) := by
    rw [cdAlg_polar_sq, hx, hy]; simp
  have hyx : y * x = - ((2 * bil x y) • (1 : CDAlg ℝ 3)) - x * y := by
    rw [← hpolar]; abel
  have hbil1 : bil (x * y) (1 : CDAlg ℝ 3) = (x * y).coord 0 := by
    rw [bil_def, Finset.sum_eq_single (0 : Fin (2^3))]
    · rw [one_coord, if_pos rfl, mul_one]
    · intro b _ hb; rw [one_coord, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hbilcross : bil (x * y) (y * x) = 2 * (bil x y)^2 - N x * N y := by
    rw [hyx, bil_sub_right,
      show (- ((2 * bil x y) • (1 : CDAlg ℝ 3))) = (-(2 * bil x y)) • (1 : CDAlg ℝ 3)
        by rw [neg_smul], bil_smul_right, hbil1, reCoord_mul_pure x y hy,
      ← N_eq_bil, QBP.Foundations.CDAlg.octonion_norm_composition x y]
    ring
  rw [hbilcross]
  ring

/-! ### Level-2 (ℍ) norm composition

`OctonionLaws` only `decide`s the norm-composition polarization at `n = 3` (4096
cases).  The ℍ Lagrange identity needs the `n = 2` analogue, so we replay the same
`normMap` / `normCoeffZ` machinery here at `n = 2` (256 cases). -/

/-- `normMap` on basis 4-tuples at `n = 2` (generic-`n` proof, specialized). -/
theorem normMap_e2 (i j k l : Fin (2^2)) :
    (QBP.Foundations.CDAlg.normMap (e i) (e j) (e k) (e l) : CDAlg ℝ 2)
      = ((QBP.Foundations.CDAlg.normCoeffZ 2 i j k l : Int) : ℝ) • e 0 := by
  unfold QBP.Foundations.CDAlg.normMap
  rw [e_mul_e, e_mul_e, e_mul_e, e_mul_e,
    bil_smul_left, bil_smul_right, bil_smul_left, bil_smul_right,
    bil_e, bil_e, bil_e, bil_e, QBP.Foundations.CDAlg.normCoeffZ]
  congr 1; push_cast; ring

/-- **Integer basis fact (kernel `decide`, 4²·4² = 256 cases).**  The
    norm-composition polarization vanishes on every quaternion basis 4-tuple. -/
theorem quaternion_normCoeffZ_zero :
    ∀ i j k l : Fin (2^2), QBP.Foundations.CDAlg.normCoeffZ 2 i j k l = 0 := by decide

theorem normMap2_basis (i j k l : Fin (2^2)) :
    (QBP.Foundations.CDAlg.normMap (e i) (e j) (e k) (e l) : CDAlg ℝ 2) = 0 := by
  rw [normMap_e2, quaternion_normCoeffZ_zero]; simp

theorem cdAlg2_normMap_zero (a b c d : CDAlg ℝ 2) :
    QBP.Foundations.CDAlg.normMap a b c d = 0 :=
  lift_quadrilinear_eq QBP.Foundations.CDAlg.normMap_quadrilinear normMap2_basis a b c d

/-- **Level-2 (ℍ) norm composition** `N(x·y) = N x · N y` on `CDAlg ℝ 2`, via the
    quadrilinear bilinear-form polarization (same route as 𝕆, `decide` at `n = 2`).
    Equivalent to Mathlib's `Quaternion.normSq` multiplicativity transported across
    the `CDAlg ℝ 2 ≃ₐ ℍ[ℝ]` bridge; proved here intrinsically to keep the carrier
    uniform. -/
theorem cdAlg2_norm_composition (x y : CDAlg ℝ 2) : N (x * y) = N x * N y := by
  have hpol : (QBP.Foundations.CDAlg.normMap x x y y).coord 0 = 0 := by
    rw [cdAlg2_normMap_zero]; rfl
  have hcoord0 : (QBP.Foundations.CDAlg.normMap x x y y).coord 0
      = bil (x * y) (x * y) + bil (x * y) (x * y) - 2 * bil x x * bil y y := by
    rw [QBP.Foundations.CDAlg.normMap, smul_coord, e_coord, if_pos rfl, mul_one]
  rw [hcoord0] at hpol
  rw [← N_eq_bil, ← N_eq_bil, ← N_eq_bil] at hpol
  have hpol' : (2 : ℝ) * (N (x * y) - N x * N y) = 0 := by linear_combination hpol
  rcases mul_eq_zero.mp hpol' with hz | hz
  · exact absurd hz two_ne_zero
  · rwa [sub_eq_zero] at hz

/-- **ℍ Lagrange identity.**  For pure `x y : CDAlg ℝ 2`:
    `N (x ×₂ y) = N x · N y − ⟨x,y⟩²`.  (Same structural proof; ℍ is associative so
    the quaternion norm-composition also holds — here via the same
    `octonion`-style polarization specialized to `n = 2` using the general
    `cdAlg_polar_sq` and the level-2 norm composition.) -/
theorem quaternion_cross_norm_identity (x y : CDAlg ℝ 2)
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    N (cross x y) = N x * N y - (bil x y)^2 := by
  rw [cross_def, N_smul, N_sub,
    cdAlg2_norm_composition x y, cdAlg2_norm_composition y x]
  have hpolar : x * y + y * x = - ((2 * bil x y) • (1 : CDAlg ℝ 2)) := by
    rw [cdAlg_polar_sq, hx, hy]; simp
  have hyx : y * x = - ((2 * bil x y) • (1 : CDAlg ℝ 2)) - x * y := by
    rw [← hpolar]; abel
  have hbil1 : bil (x * y) (1 : CDAlg ℝ 2) = (x * y).coord 0 := by
    rw [bil_def, Finset.sum_eq_single (0 : Fin (2^2))]
    · rw [one_coord, if_pos rfl, mul_one]
    · intro b _ hb; rw [one_coord, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hbilcross : bil (x * y) (y * x) = 2 * (bil x y)^2 - N x * N y := by
    rw [hyx, bil_sub_right,
      show (- ((2 * bil x y) • (1 : CDAlg ℝ 2))) = (-(2 * bil x y)) • (1 : CDAlg ℝ 2)
        by rw [neg_smul], bil_smul_right, hbil1, reCoord_mul_pure x y hy,
      ← N_eq_bil, cdAlg2_norm_composition x y]
    ring
  rw [hbilcross]
  ring

/-! ## 5. Why the row stops at 𝕆 — no sedenion cross product

A cross product `×` satisfying `N(x×y) = N x·N y − ⟨x,y⟩²` (the Lagrange identity
above) forces a normed composition algebra of the ambient space: the existence of
such a vector product is equivalent to a composition algebra structure (Hurwitz),
which exists only in dimensions 1, 2, 4, 8 — i.e. only at ℝ, ℂ, ℍ, 𝕆.  At 𝕊 the
norm form is NOT multiplicative (`Breakdown.sedenion_norm_not_multiplicative`):
there are zero divisors with `N(x·y) = 0 ≠ N x · N y`, so no composition structure
and hence no 7-D-style cross product survives.  This file therefore defines NO
sedenion cross product; the matrix row is `—/—/✓/✓/—`. -/

/-- The structural OBSTRUCTION witness for "no 𝕊 cross product": the norm form fails
    to compose at 𝕊.  (Statement-level cite; the cross product needs exactly this
    composition property — see §5.) -/
theorem no_sedenion_composition_for_cross :
    ∃ x y : CDAlg ℝ 4, N (x * y) ≠ N x * N y :=
  QBP.Foundations.Breakdown.sedenion_norm_not_multiplicative

/-! ## 6. Completeness audit — `#print axioms` -/

#print axioms cdAlg_polar_sq
#print axioms cross_antisymm
#print axioms cross_reCoord_zero
#print axioms octonion_cross_orthogonal_left
#print axioms octonion_cross_orthogonal_right
#print axioms quaternion_cross_orthogonal_left
#print axioms quaternion_cross_orthogonal_right
#print axioms octonion_cross_norm_identity
#print axioms quaternion_cross_norm_identity
#print axioms no_sedenion_composition_for_cross

end QBP.Foundations.CrossProduct
