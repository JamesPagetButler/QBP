/-
  QBP.Foundations.Alternator
  ==========================

  The LEFT ALTERNATOR on the sedenions `𝕊 = CDAlg ℝ 4` (issue #473, substrate).

  `𝕊` is the first rung of the Cayley–Dickson tower that is NOT alternative
  (`CDLifting.sedenion_not_alternative`).  The failure is measured by the left
  alternator
      `T s x = (s·s)·x − s·(s·x)   ( = assoc s s x )`,
  a trilinear object in disguise: for FIXED `s` it is an ℝ-linear endomorphism of
  `𝕊`, and it is the exact obstruction to `L_s² = L_{s²}`.

  This file proves the following anchors.

  * **T1 (the kill).**  For `s = Σ_{a=1}^{15} e_a` — the sum of ALL fifteen
    imaginary units — the alternator VANISHES identically:
        `∀ x, s · (s · x) = (−15 : ℝ) • x`   and   `s · s = (−15 : ℝ) • 1`.
    So the "most generic-looking" imaginary sedenion is in fact alternator-free:
    non-alternativity of 𝕊 is emphatically NOT a property of generic-looking
    elements.  Proved by a kernel `decide` on the 16×16 INTEGER
    left-multiplication matrix (`sAllLZ`) plus a structural ℝ-linearity argument
    — no `native_decide`, no `decide` over ℝ.
    (`sAll_left_mul_sq`, `sAll_sq`, `sAll_assoc_zero`.)

  * **The octonion contraction identity.**  For all `a b : 𝕆`,
        `Σ_{i=0}^{7} e_i · [a, e_i, b] = −4 · (a·b − b·a)`.
    Full contraction of the associator against the basis returns `−4×` the
    commutator.  Bilinear, so it lifts from a 64-case ℤ-`decide`.
    (`octonion_assoc_contract`.)

  * **T2a at 𝕆.**  For imaginary `a` and any `b`: `[a, y, b] = 0 ∀y ↔ a·b = b·a`.
    `⇒` is the contraction identity; `⇐` runs through the commutant lemma
    (`a` imaginary nonzero and `[a,b] = 0` ⟹ `b ∈ span{1,a}`), which is proved
    from the polarized CD square identity + octonion norm composition + positive
    definiteness of `N` — no `decide` over ℝ anywhere.
    (`octonion_commutant`, `octonion_assoc_vanishes_iff_commute`.)

  * **T2a at 𝕊 (the landscape identity).**  For any IMAGINARY `s : 𝕊`, split in
    the Cayley–Dickson pair representation as `s = (a, b)` with `a = cdLo s`
    (low coordinate half, imaginary) and `b = cdHi s` (high half):
        `(∀ x, T s x = 0)  ↔  a · b = b · a`.
    Route: (i) `[s,s,x] = laMap (loPart s) (hiPart s) x` — both octonion copies
    `𝕆⊕0` and `0⊕𝕆` are individually alternator-flat (`decide`, 2×1024 cases);
    (ii) the **sedenion contraction identity**
        `cdHi ( Σ_t e_{8+t} · [s,s,e_{8+t}] ) = 4 · (a·b − b·a)`   (`decide`, 64 cases)
    gives `⇒`; (iii) the two kernel-checked alternator-flat rows `s = (a,1)` and
    `s = (a,a)` plus the octonion commutant give `⇐`.
    (`sedenion_alternator_contract`,
     `sedenion_alternator_vanishes_iff_components_commute`.)

  * **Non-vacuity.**  Both sides of the ↔ are realized, and 𝕊's
    non-alternativity is RE-DERIVED from the commutator criterion
    (`sedWitX_alternator_ne_zero`, `sedenion_not_alternative_via_commutator`).

  * **T2c (scalar part).**  For imaginary `s`, `s·(s·x) = −N(s)•x − [s,s,x]`,
    i.e. `−L_s² = N(s)·id + T_s` (with `T_s x := (s·s)·x − s·(s·x)`).
    (`left_mul_sq_imaginary`.)

  NOT proved here (tracked, honest gap): the cubic landscape identity
  **T2b**, `T_s³ = ‖a·b − b·a‖² · T_s`.  It reduces (see the derivation notes in
  issue #473) to the octonion operator identity `A³ = −‖[a,b]‖²·A` for
  `A y = [a,y,b]`, which is a degree-(3,3,1) polynomial identity in 23 real
  variables — far beyond `ring`, and the known structural proof needs the
  orthogonal decomposition `𝕆 = H ⊕ H^⊥` for the quaternion subalgebra
  `H = span{1,a,b,ab}` (a projection that is NOT polynomial in `a,b`).  That
  decomposition machinery does not yet exist in this corpus.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom of each section.
-/
import QBP.Foundations.CDLifting
import QBP.Foundations.OctonionLaws

namespace QBP.Foundations.CDAlg

open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ## 0. XOR helpers and the left-multiplication matrix

`mul_coord_single` (in `CDAlg`) collapses the double structure-constant sum onto
one index.  Re-indexing it by `m = i ⊕ k` exhibits multiplication as an honest
matrix acting on coordinates — the form every alternator computation below uses.
-/

/-- XOR on `Fin (2^n)` is commutative. -/
theorem xor_comm_fin (i j : Fin (2^n)) : (i ^^^ j) = (j ^^^ i) := by
  apply Fin.ext
  simp only [Fin.xor_val_of_two_pow, Nat.xor_comm]

/-- `i ⊕ j = 0` exactly when `i = j`. -/
theorem xor_eq_zero_iff (i j : Fin (2^n)) : (i ^^^ j) = 0 ↔ i = j := by
  constructor
  · intro h
    have h2 := congrArg (fun t => (t ^^^ j : Fin (2^n))) h
    simp only at h2
    rwa [xor_xor_cancel i j, xor_zero_left] at h2
  · intro h; subst h; exact xor_self_eq i

/-- Re-indexing a sum over `Fin (2^n)` along the XOR involution `i ↦ i ⊕ k`. -/
theorem sum_xor_reindex {M : Type*} [AddCommMonoid M] (k : Fin (2^n)) (g : Fin (2^n) → M) :
    (∑ i, g i) = ∑ i, g (i ^^^ k) := by
  apply Finset.sum_nbij' (fun i => i ^^^ k) (fun i => i ^^^ k) <;>
    intro a _ <;>
    first
      | exact Finset.mem_univ _
      | exact xor_xor_cancel a k
      | exact congrArg g (xor_xor_cancel a k).symm

/-- **Left multiplication as a coordinate matrix.**
    `(u · x).coord k = Σ_m L(u)_{k,m} · x.coord m` with
    `L(u)_{k,m} = mulCoeff n (m ⊕ k) m · u.coord (m ⊕ k)`. -/
theorem mul_coord_matrix (u x : CDAlg R n) (k : Fin (2^n)) :
    (u * x).coord k = ∑ m, (mulCoeff n (m ^^^ k) m : R) * u.coord (m ^^^ k) * x.coord m := by
  rw [mul_coord_single]
  rw [sum_xor_reindex k (fun i => (mulCoeff n i (i ^^^ k) : R) * u.coord i * x.coord (i ^^^ k))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [xor_xor_cancel m k]

/-- `x · 1 = x`: the CD unit is a right identity (from `mulCoeff n i 0 = 1`). -/
@[simp] theorem cd_mul_one (x : CDAlg R n) : x * (1 : CDAlg R n) = x := by
  ext k
  rw [mul_coord_matrix]
  rw [Finset.sum_eq_single (0 : Fin (2^n))]
  · rw [one_coord, if_pos rfl, mul_one, xor_zero_left, mulCoeff_zero_right]
    push_cast; ring
  · intro b _ hb
    rw [one_coord, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `1 · x = x`: the CD unit is a left identity (from `mulCoeff n 0 j = 1`). -/
@[simp] theorem cd_one_mul (x : CDAlg R n) : (1 : CDAlg R n) * x = x := by
  ext k
  rw [mul_coord_matrix]
  rw [Finset.sum_eq_single k]
  · rw [xor_self_eq, one_coord, if_pos rfl, mulCoeff_zero_left]
    push_cast; ring
  · intro b _ hb
    have hbk : (b ^^^ k : Fin (2^n)) ≠ 0 := fun h0 => hb ((xor_eq_zero_iff b k).mp h0)
    rw [one_coord, if_neg hbk, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `x · 0 = 0` (bilinearity; `CDAlg` is not a `MulZeroClass`, so this is proved
    from `mul_smul_right`). -/
@[simp] theorem alt_mul_zero (x : CDAlg R n) : x * (0 : CDAlg R n) = 0 := by
  have h := mul_smul_right (0 : R) x 0
  rwa [zero_smul, zero_smul] at h

/-- `0 · x = 0` (bilinearity). -/
@[simp] theorem alt_zero_mul (x : CDAlg R n) : (0 : CDAlg R n) * x = 0 := by
  have h := mul_smul_left (0 : R) 0 x
  rwa [zero_smul, zero_smul] at h

/-! ## 1. T1 — the sum of all fifteen imaginary units is alternator-free

`s = Σ_{a=1}^{15} e_a`.  Its left-multiplication matrix has INTEGER entries
(`sAllLZ`), so the whole claim `L_s ∘ L_s = −15 · id` is a finite ℤ statement
closed by kernel `decide`; the transfer to ℝ is pure linear algebra. -/

/-- `sAll = Σ_{a ≠ 0} e_a`, the sum of all fifteen imaginary sedenion units. -/
def sAll : CDAlg ℝ 4 := ∑ a ∈ (Finset.univ.erase (0 : Fin (2^4))), e a

/-- The coordinates of `sAll`: `0` on the real axis, `1` on every imaginary axis. -/
theorem sAll_coord (i : Fin (2^4)) : sAll.coord i = if i = 0 then 0 else 1 := by
  rw [sAll, sum_coord]
  simp only [e_coord]
  rw [Finset.sum_ite_eq (Finset.univ.erase (0 : Fin (2^4))) i (fun _ => (1 : ℝ))]
  by_cases h : i = 0
  · simp [h]
  · simp [h, Finset.mem_erase]

/-- The INTEGER left-multiplication matrix of `sAll`:
    `L(sAll)_{k,m} = mulCoeff 4 (m ⊕ k) m · [m ⊕ k ≠ 0]`. -/
def sAllLZ (k m : Fin (2^4)) : Int :=
  mulCoeff 4 (m ^^^ k) m * (if (m ^^^ k) = 0 then 0 else 1)

/-- **The finite kernel check behind T1.**  The square of the integer matrix
    `sAllLZ` is `−15` times the identity:
    `Σ_m sAllLZ k m · sAllLZ m p = −15·δ_{k,p}`.  256 × 16 integer evaluations,
    kernel `decide` (no `native_decide`). -/
theorem sAllLZ_sq :
    ∀ k p : Fin (2^4), (∑ m : Fin (2^4), sAllLZ k m * sAllLZ m p) = if k = p then -15 else 0 := by
  decide

/-- `L(sAll)` acting on coordinates, with the entries recognised as the integer
    matrix `sAllLZ`. -/
theorem sAll_mul_coord (x : CDAlg ℝ 4) (k : Fin (2^4)) :
    (sAll * x).coord k = ∑ m, ((sAllLZ k m : Int) : ℝ) * x.coord m := by
  rw [mul_coord_matrix]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [sAll_coord, sAllLZ]
  by_cases h : (m ^^^ k : Fin (2^4)) = 0
  · rw [if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]; push_cast; ring

/-- **T1 (the kill).**  For `s = Σ_{a=1}^{15} e_a` the left alternator vanishes
    identically on 𝕊: `s · (s · x) = (−15) • x` for EVERY sedenion `x`.
    Equivalently `L_s² = L_{s²} = −15·id`, even though 𝕊 is not alternative. -/
theorem sAll_left_mul_sq (x : CDAlg ℝ 4) : sAll * (sAll * x) = (-15 : ℝ) • x := by
  ext k
  rw [sAll_mul_coord, smul_coord]
  have hstep : ∀ m : Fin (2^4), ((sAllLZ k m : Int) : ℝ) * (sAll * x).coord m
      = ∑ p, (((sAllLZ k m * sAllLZ m p : Int)) : ℝ) * x.coord p := by
    intro m
    rw [sAll_mul_coord, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by push_cast; ring)
  rw [Finset.sum_congr rfl (fun m _ => hstep m), Finset.sum_comm]
  have hinner : ∀ p : Fin (2^4),
      (∑ m, (((sAllLZ k m * sAllLZ m p : Int)) : ℝ) * x.coord p)
        = (((if k = p then (-15 : Int) else 0) : Int) : ℝ) * x.coord p := by
    intro p
    rw [← Finset.sum_mul, ← Int.cast_sum, sAllLZ_sq k p]
  rw [Finset.sum_congr rfl (fun p _ => hinner p)]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]; push_cast; ring
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm)]; push_cast; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **T1, square form.**  `s · s = −15` for `s = Σ_{a=1}^{15} e_a`. -/
theorem sAll_sq : sAll * sAll = (-15 : ℝ) • (1 : CDAlg ℝ 4) := by
  have h := sAll_left_mul_sq (1 : CDAlg ℝ 4)
  rwa [cd_mul_one] at h

/-- **T1, alternator form.**  The left alternator `[s, s, x] = (s·s)·x − s·(s·x)`
    vanishes identically for `s = Σ_{a=1}^{15} e_a`, even though 𝕊 is not
    alternative. -/
theorem sAll_assoc_zero (x : CDAlg ℝ 4) : assoc sAll sAll x = 0 := by
  rw [assoc, sAll_sq, sAll_left_mul_sq, mul_smul_left, cd_one_mul, sub_self]

/-! ### T1 completeness audit -/

#print axioms sAllLZ_sq
#print axioms sAll_left_mul_sq
#print axioms sAll_sq
#print axioms sAll_assoc_zero

/-! ## 2. Positive-definiteness of the norm form and the polarized square

Two ℝ-specific structural facts the ↔ of T2a needs.  Neither is decidable — both
are proved from Mathlib's ordered-field lemmas and from `cdAlg_sq_eq`. -/

/-- `N x ≥ 0` over ℝ: the norm FORM is a sum of squares. -/
theorem alt_N_nonneg (x : CDAlg ℝ n) : 0 ≤ N x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x.coord i))

/-- `N` is positive definite over ℝ: `N x = 0 ↔ x = 0`. -/
theorem alt_N_eq_zero_iff (x : CDAlg ℝ n) : N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x.coord i))).mp h
    ext i
    have := hall i (Finset.mem_univ i)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h; subst h; simp [N_def]

/-- Cancelling a nonzero scalar in `CDAlg ℝ n`. -/
theorem eq_zero_of_smul_eq_zero {r : ℝ} (hr : r ≠ 0) {x : CDAlg ℝ n} (h : r • x = 0) : x = 0 := by
  ext k
  have hk := congrArg (fun z => CDAlg.coord z k) h
  simp only [smul_coord, zero_coord] at hk
  simpa using (mul_eq_zero.mp hk).resolve_left hr

/-- `bil x (y − z) = bil x y − bil x z`. -/
theorem alt_bil_sub_right (x y z : CDAlg R n) : bil x (y - z) = bil x y - bil x z := by
  simp only [bil_def, sub_coord]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil x 1 = Re x`. -/
theorem bil_one_right (x : CDAlg R n) : bil x 1 = x.coord 0 := by
  simp only [bil_def, one_coord]
  rw [Finset.sum_eq_single (0 : Fin (2^n))]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb; rw [if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The norm form is quadratic with polar form `bil`:
    `N (x + y) = N x + 2·bil x y + N y`. -/
theorem alt_N_add (x y : CDAlg R n) : N (x + y) = N x + 2 * bil x y + N y := by
  simp only [N_def, bil_def, add_coord, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Polarized Cayley–Dickson square identity.**
    `x·y + y·x = 2·Re(x)·y + 2·Re(y)·x − 2·⟨x,y⟩·1`.
    (Polarization of `cdAlg_sq_eq`; holds at every level of the tower.)  In
    particular two ORTHOGONAL IMAGINARY elements anticommute. -/
theorem mul_add_mul_comm (x y : CDAlg ℝ n) :
    x * y + y * x
      = (2 * x.coord 0) • y + (2 * y.coord 0) • x - (2 * bil x y) • (1 : CDAlg ℝ n) := by
  have hexp : (x + y) * (x + y) = x * x + x * y + y * x + y * y := by
    rw [mul_add_left, mul_add_right, mul_add_right]; abel
  have hx := cdAlg_sq_eq x
  have hy := cdAlg_sq_eq y
  have hxy := cdAlg_sq_eq (x + y)
  have key : x * y + y * x
      = ((2 * (x + y).coord 0) • (x + y) - (N (x + y)) • (1 : CDAlg ℝ n))
        - ((2 * x.coord 0) • x - (N x) • (1 : CDAlg ℝ n))
        - ((2 * y.coord 0) • y - (N y) • (1 : CDAlg ℝ n)) := by
    rw [← hx, ← hy, ← hxy, hexp]; abel
  rw [key, alt_N_add]
  simp only [add_coord]
  module

/-- Orthogonal imaginary elements anticommute. -/
theorem anticomm_of_orthogonal_imaginary {x y : CDAlg ℝ n}
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) (hxy : bil x y = 0) :
    x * y + y * x = 0 := by
  rw [mul_add_mul_comm, hx, hy, hxy]; simp

/-! ## 3. The octonion contraction identity

`Σ_i e_i · [a, e_i, b] = −4 (a·b − b·a)` on 𝕆.  Bilinear in `(a,b)`, so it lifts
from a 64-case integer basis fact.  This is the anchor that turns "the associator
`[a, ·, b]` vanishes identically" into "`a` and `b` commute". -/

/-- `i ⊕ (p ⊕ i ⊕ q) = p ⊕ q`. -/
theorem xor_assoc_fin (i j k : Fin (2^n)) : ((i ^^^ j) ^^^ k) = (i ^^^ (j ^^^ k)) := by
  apply Fin.ext
  simp only [Fin.xor_val_of_two_pow, Nat.xor_assoc]

/-- `i ⊕ (p ⊕ i ⊕ q) = p ⊕ q` — the contraction index collapse. -/
theorem xor_mid_cancel (i p q : Fin (2^n)) : (i ^^^ (p ^^^ i ^^^ q)) = (p ^^^ q) := by
  calc (i ^^^ ((p ^^^ i) ^^^ q))
      = (i ^^^ ((i ^^^ p) ^^^ q)) := by rw [xor_comm_fin p i]
    _ = (i ^^^ (i ^^^ (p ^^^ q))) := by rw [xor_assoc_fin i p q]
    _ = ((i ^^^ i) ^^^ (p ^^^ q)) := by rw [xor_assoc_fin i i (p ^^^ q)]
    _ = (p ^^^ q) := by rw [xor_self_eq, xor_zero_left]

/-- Integer coefficient of the contraction defect on basis pairs. -/
def contractCoeffZ (p q : Fin (2^3)) : Int :=
  (∑ i, assocCoeffZ 3 p i q * mulCoeff 3 i (p ^^^ i ^^^ q))
    + 4 * (mulCoeff 3 p q - mulCoeff 3 q p)

/-- **Integer basis fact (kernel `decide`, 64 cases × 8-term sums).**  The
    contraction defect vanishes on every octonion basis pair. -/
theorem contractCoeffZ_zero : ∀ p q : Fin (2^3), contractCoeffZ p q = 0 := by decide

/-- The contraction defect map `Σ_i e_i·[a,e_i,b] + 4(ab − ba)`. -/
def contractMap (a b : CDAlg ℝ 3) : CDAlg ℝ 3 :=
  (∑ i, (e i) * assoc a (e i) b) + (4 : ℝ) • (a * b - b * a)

theorem contractMap_bilinear : IsBilinear contractMap where
  add_left a a' b := by
    have h1 : ∀ i : Fin (2^3), (e i : CDAlg ℝ 3) * assoc (a + a') (e i) b
        = (e i) * assoc a (e i) b + (e i) * assoc a' (e i) b := by
      intro i; rw [assoc_trilinear.add_left, mul_add_right]
    unfold contractMap
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), Finset.sum_add_distrib,
      mul_add_left, mul_add_right]
    simp only [smul_sub, smul_add]
    abel
  smul_left r a b := by
    have h1 : ∀ i : Fin (2^3), (e i : CDAlg ℝ 3) * assoc (r • a) (e i) b
        = r • ((e i) * assoc a (e i) b) := by
      intro i; rw [assoc_trilinear.smul_left, mul_smul_right]
    unfold contractMap
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), ← Finset.smul_sum,
      mul_smul_left, mul_smul_right]
    rw [smul_add]
    congr 1
    rw [← smul_sub, smul_smul, smul_smul, mul_comm]
  add_right a b b' := by
    have h1 : ∀ i : Fin (2^3), (e i : CDAlg ℝ 3) * assoc a (e i) (b + b')
        = (e i) * assoc a (e i) b + (e i) * assoc a (e i) b' := by
      intro i; rw [assoc_trilinear.add_right, mul_add_right]
    unfold contractMap
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), Finset.sum_add_distrib,
      mul_add_right, mul_add_left]
    simp only [smul_sub, smul_add]
    abel
  smul_right r a b := by
    have h1 : ∀ i : Fin (2^3), (e i : CDAlg ℝ 3) * assoc a (e i) (r • b)
        = r • ((e i) * assoc a (e i) b) := by
      intro i; rw [assoc_trilinear.smul_right, mul_smul_right]
    unfold contractMap
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), ← Finset.smul_sum,
      mul_smul_right, mul_smul_left]
    rw [smul_add]
    congr 1
    rw [← smul_sub, smul_smul, smul_smul, mul_comm]

theorem contractMap_e (p q : Fin (2^3)) :
    contractMap (e p) (e q) = ((contractCoeffZ p q : Int) : ℝ) • e (p ^^^ q) := by
  have h1 : ∀ i : Fin (2^3), (e i : CDAlg ℝ 3) * assoc (e p) (e i) (e q)
      = ((assocCoeffZ 3 p i q * mulCoeff 3 i (p ^^^ i ^^^ q) : Int) : ℝ) • e (p ^^^ q) := by
    intro i
    rw [assoc_e, mul_smul_right, e_mul_e, smul_smul, xor_mid_cancel]
    push_cast; ring_nf
  unfold contractMap contractCoeffZ
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), ← Finset.sum_smul]
  rw [e_mul_e, e_mul_e, xor_comm_fin q p, ← sub_smul, smul_smul]
  rw [← add_smul]
  push_cast
  ring_nf

theorem contractMap_zero (a b : CDAlg ℝ 3) : contractMap a b = 0 :=
  lift_bilinear_eq contractMap_bilinear
    (fun p q => by rw [contractMap_e, contractCoeffZ_zero]; simp) a b

/-- **The octonion contraction identity.**  For all `a b : 𝕆`,
    `Σ_{i=0}^{7} e_i · [a, e_i, b] = −4 · (a·b − b·a)`.
    The full contraction of the associator against the basis recovers exactly
    (−4×) the commutator.  Consequently `[a, ·, b] ≡ 0 ⟹ a·b = b·a`. -/
theorem octonion_assoc_contract (a b : CDAlg ℝ 3) :
    (∑ i, (e i) * assoc a (e i) b) = (-4 : ℝ) • (a * b - b * a) := by
  have h := contractMap_zero a b
  unfold contractMap at h
  have h2 : (∑ i, (e i : CDAlg ℝ 3) * assoc a (e i) b) = -((4 : ℝ) • (a * b - b * a)) :=
    eq_neg_of_add_eq_zero_left h
  rw [h2, ← neg_smul]

/-! ## 4. The octonion commutant and T2a at 𝕆

For imaginary `a ≠ 0` the commutant of `a` in 𝕆 is exactly `span{1, a}`.  Proof
uses only: the polarized square identity, octonion norm composition (Hurwitz
multiplicativity, already proved in `OctonionLaws`), and positive definiteness of
`N` over ℝ.  Combined with flexibility (`[a,y,a] = 0`) this gives one direction
of T2a; the contraction identity gives the other. -/

/-- **Commutant of an imaginary octonion.**  If `a` is imaginary and nonzero and
    `b` commutes with `a`, then `b ∈ span{1, a}`. -/
theorem octonion_commutant {a b : CDAlg ℝ 3} (ha0 : a.coord 0 = 0) (hane : a ≠ 0)
    (hcomm : a * b = b * a) :
    b = (b.coord 0) • (1 : CDAlg ℝ 3) + (bil a b / N a) • a := by
  have hNa : N a ≠ 0 := fun h => hane ((alt_N_eq_zero_iff a).mp h)
  set lam : ℝ := bil a b / N a with hlam
  set b' : CDAlg ℝ 3 := b - ((b.coord 0) • (1 : CDAlg ℝ 3) + lam • a) with hb'def
  have hb'0 : b'.coord 0 = 0 := by
    rw [hb'def]
    simp [ha0]
  have hbil : bil a b' = 0 := by
    rw [hb'def, alt_bil_sub_right, bil_add_right, bil_smul_right, bil_smul_right, bil_one_right,
      ha0, ← N_eq_bil, hlam, div_mul_cancel₀ _ hNa]
    ring
  have hcomm' : a * b' = b' * a := by
    rw [hb'def]
    rw [show b - ((b.coord 0) • (1 : CDAlg ℝ 3) + lam • a)
          = b + (-((b.coord 0) • (1 : CDAlg ℝ 3)) + -(lam • a)) by abel]
    rw [mul_add_right, mul_add_left, mul_add_right, mul_add_left, hcomm]
    congr 1
    congr 1
    · rw [show -((b.coord 0) • (1 : CDAlg ℝ 3)) = (-(b.coord 0)) • (1 : CDAlg ℝ 3) by
        rw [neg_smul]]
      rw [mul_smul_right, mul_smul_left, cd_mul_one, cd_one_mul]
    · rw [show -(lam • a) = (-lam) • a by rw [neg_smul]]
      rw [mul_smul_right, mul_smul_left]
  have hsum : a * b' + b' * a = 0 := anticomm_of_orthogonal_imaginary ha0 hb'0 hbil
  have hzero : a * b' = 0 := by
    have h2 : (2 : ℝ) • (a * b') = 0 := by
      rw [two_smul]; nth_rewrite 2 [hcomm']; exact hsum
    exact eq_zero_of_smul_eq_zero two_ne_zero h2
  have hN0 : N a * N b' = 0 := by
    rw [← octonion_norm_composition, hzero, (alt_N_eq_zero_iff (0 : CDAlg ℝ 3)).mpr rfl]
  have hb'zero : b' = 0 := (alt_N_eq_zero_iff b').mp ((mul_eq_zero.mp hN0).resolve_left hNa)
  rw [hb'def] at hb'zero
  have := sub_eq_zero.mp hb'zero
  exact this

/-- `[x, y, 1] = 0`. -/
theorem alt_assoc_one_right (x y : CDAlg R n) : assoc x y 1 = 0 := by
  rw [assoc, cd_mul_one, cd_mul_one, sub_self]

/-- **T2a at the octonion level.**  For an IMAGINARY octonion `a` and any `b`:
    the associator `[a, y, b]` vanishes for every `y` **iff** `a` and `b` commute.
    (`⇐` uses the commutant lemma + flexibility; `⇒` is the contraction
    identity.) -/
theorem octonion_assoc_vanishes_iff_commute {a b : CDAlg ℝ 3} (ha0 : a.coord 0 = 0) :
    (∀ y, assoc a y b = 0) ↔ a * b = b * a := by
  constructor
  · intro h
    have hc := octonion_assoc_contract a b
    have hz : ∀ i : Fin (2^3), (e i : CDAlg ℝ 3) * assoc a (e i) b = 0 := by
      intro i; rw [h (e i), alt_mul_zero]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hz i),
      Finset.sum_const_zero] at hc
    have := eq_zero_of_smul_eq_zero (r := (-4 : ℝ)) (by norm_num) hc.symm
    exact sub_eq_zero.mp this
  · intro hcomm y
    by_cases ha : a = 0
    · subst ha
      rw [assoc, alt_zero_mul, alt_zero_mul, alt_zero_mul, sub_self]
    · rw [octonion_commutant ha0 ha hcomm]
      rw [assoc_trilinear.add_right, assoc_trilinear.smul_right, assoc_trilinear.smul_right,
        alt_assoc_one_right, assoc_diag_flex]
      simp

/-! ### T2a (𝕆) completeness audit -/

#print axioms contractCoeffZ_zero
#print axioms octonion_assoc_contract
#print axioms mul_add_mul_comm
#print axioms octonion_commutant
#print axioms octonion_assoc_vanishes_iff_commute

/-! ## 5. The Cayley–Dickson pair split of 𝕊 = 𝕆 ⊕ 𝕆

`Fin 16` splits as low half (`loIdx : Fin 8 → Fin 16`, `p ↦ p`) and high half
(`hiIdx : q ↦ q + 8`).  `cdLo`/`cdHi` are the two octonion components of a sedenion:
`s = (cdLo s, cdHi s)` in the CD pair representation. -/

/-- Low-half index embedding `Fin 8 ↪ Fin 16`. -/
def loIdx (p : Fin (2^3)) : Fin (2^4) := ⟨p.val, lt_of_lt_of_le p.isLt (by norm_num)⟩

/-- High-half index embedding `Fin 8 ↪ Fin 16`, `q ↦ q + 8`. -/
def hiIdx (q : Fin (2^3)) : Fin (2^4) :=
  ⟨q.val + 2^3, by have h := q.isLt; norm_num at h ⊢; omega⟩

/-- The first octonion component of a sedenion (CD pair `s = (cdLo s, cdHi s)`). -/
def cdLo (x : CDAlg R 4) : CDAlg R 3 := ⟨fun p => x.coord (loIdx p)⟩

/-- The second octonion component of a sedenion. -/
def cdHi (x : CDAlg R 4) : CDAlg R 3 := ⟨fun q => x.coord (hiIdx q)⟩

@[simp] theorem cdLo_coord (x : CDAlg R 4) (p) : (cdLo x).coord p = x.coord (loIdx p) := rfl
@[simp] theorem cdHi_coord (x : CDAlg R 4) (q) : (cdHi x).coord q = x.coord (hiIdx q) := rfl

theorem cdLo_add (x y : CDAlg R 4) : cdLo (x + y) = cdLo x + cdLo y := by ext p; rfl
theorem cdHi_add (x y : CDAlg R 4) : cdHi (x + y) = cdHi x + cdHi y := by ext q; rfl
theorem cdLo_smul (r : R) (x : CDAlg R 4) : cdLo (r • x) = r • cdLo x := by ext p; rfl
theorem cdHi_smul (r : R) (x : CDAlg R 4) : cdHi (r • x) = r • cdHi x := by ext q; rfl
theorem cdHi_zero : cdHi (0 : CDAlg R 4) = 0 := by ext q; rfl

theorem cdHi_sum {ι : Type*} (s : Finset ι) (f : ι → CDAlg R 4) :
    cdHi (∑ i ∈ s, f i) = ∑ i ∈ s, cdHi (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cdHi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, cdHi_add, ih, Finset.sum_insert ha]

/-! ### Index combinatorics — all by kernel `decide` on `Fin 8` / `Fin 16` -/

theorem loIdx_inj_iff : ∀ p q : Fin (2^3), (loIdx p = loIdx q) ↔ p = q := by decide
theorem hiIdx_inj_iff : ∀ p q : Fin (2^3), (hiIdx p = hiIdx q) ↔ p = q := by decide
theorem loIdx_ne_hiIdx : ∀ p q : Fin (2^3), loIdx p ≠ hiIdx q := by decide

/-- Every `Fin 16` index is either a low-half or a high-half index. -/
theorem idx_cases : ∀ k : Fin (2^4),
    (∃ t : Fin (2^3), k = loIdx t) ∨ (∃ t : Fin (2^3), k = hiIdx t) := by decide

theorem idx3 : ∀ p q t : Fin (2^3),
    (loIdx p ^^^ hiIdx q ^^^ hiIdx t) = loIdx (p ^^^ q ^^^ t) := by decide

theorem idx4 : ∀ p q t : Fin (2^3),
    (hiIdx t ^^^ loIdx (p ^^^ q ^^^ t)) = hiIdx (p ^^^ q) := by decide

theorem cdHi_e_hiIdx (m : Fin (2^3)) : cdHi (e (hiIdx m) : CDAlg R 4) = e m := by
  ext t
  simp only [cdHi_coord, e_coord]
  by_cases h : t = m
  · rw [if_pos h, if_pos ((hiIdx_inj_iff t m).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((hiIdx_inj_iff t m).mp hh))]

/-- **The CD pair split.**  Every sedenion is the sum of its low-half and
    high-half basis expansions. -/
theorem split_eq (x : CDAlg R 4) :
    x = (∑ p : Fin (2^3), x.coord (loIdx p) • e (loIdx p))
      + (∑ q : Fin (2^3), x.coord (hiIdx q) • e (hiIdx q)) := by
  ext k
  rw [add_coord, sum_coord, sum_coord]
  simp only [smul_coord, e_coord, mul_ite, mul_one, mul_zero]
  rcases idx_cases k with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    rw [Finset.sum_eq_single t, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero]
    · intro q _; rw [if_neg (loIdx_ne_hiIdx t q)]
    · intro b _ hb; rw [if_neg (fun hh => hb ((loIdx_inj_iff t b).mp hh).symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · subst ht
    rw [Finset.sum_eq_zero, Finset.sum_eq_single t]
    · rw [if_pos rfl, zero_add]
    · intro b _ hb; rw [if_neg (fun hh => hb ((hiIdx_inj_iff t b).mp hh).symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro p _; rw [if_neg (fun hh => loIdx_ne_hiIdx p t hh.symm)]

/-! ## 6. Basis integer facts for the sedenion alternator -/

/-- Integer coefficient of the polarized left-alternator on basis triples:
    `laMap eᵢ e_j e_k = laCoeffZ n i j k • e_{i⊕j⊕k}`. -/
def laCoeffZ (n : ℕ) (i j k : Fin (2^n)) : Int := assocCoeffZ n i j k + assocCoeffZ n j i k

theorem laMap_e (i j k : Fin (2^n)) :
    (laMap (e i) (e j) (e k) : CDAlg R n) = (laCoeffZ n i j k : R) • e (i ^^^ j ^^^ k) := by
  rw [laMap, assoc_e, assoc_e,
    show (j ^^^ i ^^^ k : Fin (2^n)) = (i ^^^ j ^^^ k) by rw [xor_comm_fin j i], laCoeffZ]
  push_cast
  rw [add_smul]

/-- **𝕆 ⊕ 0 is alternator-flat (kernel `decide`, 1024 cases).**  The polarized
    left alternator vanishes whenever BOTH left slots lie in the low octonion
    copy. -/
theorem laCoeffZ_lo_lo :
    ∀ p r : Fin (2^3), ∀ k : Fin (2^4), laCoeffZ 4 (loIdx p) (loIdx r) k = 0 := by decide

/-- **0 ⊕ 𝕆 is alternator-flat (kernel `decide`, 1024 cases).** -/
theorem laCoeffZ_hi_hi :
    ∀ p r : Fin (2^3), ∀ k : Fin (2^4), laCoeffZ 4 (hiIdx p) (hiIdx r) k = 0 := by decide

/-- **The `b = 1` row vanishes (kernel `decide`, 128 cases):** `[·, e₈, ·]`
    polarized is zero on the low copy — i.e. `s = (a, 1)` is alternator-free. -/
theorem laCoeffZ_lo_hi0 :
    ∀ p : Fin (2^3), ∀ k : Fin (2^4), laCoeffZ 4 (loIdx p) (hiIdx 0) k = 0 := by decide

/-- **The `b = a` row is antisymmetric (kernel `decide`, 1024 cases):** the
    polarization in `a` of `laMap (a,0) (0,a)` vanishes — i.e. `s = (a, a)` is
    alternator-free. -/
theorem laCoeffZ_lo_hi_sym :
    ∀ p q : Fin (2^3), ∀ k : Fin (2^4),
      laCoeffZ 4 (loIdx p) (hiIdx q) k + laCoeffZ 4 (loIdx q) (hiIdx p) k = 0 := by decide

/-- **The sedenion contraction coefficient (kernel `decide`, 64 cases).**
    Contracting the polarized alternator against the high-half basis returns
    `4×` the octonion commutator coefficient. -/
theorem sedContractZ : ∀ p q : Fin (2^3),
    (∑ t : Fin (2^3), laCoeffZ 4 (loIdx p) (hiIdx q) (hiIdx t)
        * mulCoeff 4 (hiIdx t) (loIdx (p ^^^ q ^^^ t)))
      = 4 * (mulCoeff 3 p q - mulCoeff 3 q p) := by decide

/-! ## 7. Multilinear expansion helpers -/

theorem alt_mul_isBilinear : IsBilinear (fun x y : CDAlg R n => x * y) where
  add_left := mul_add_left
  smul_left := mul_smul_left
  add_right := mul_add_right
  smul_right := mul_smul_right

theorem laMap_expand_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Fin (2^4)) (g : κ → Fin (2^4)) (c : ι → ℝ) (d : κ → ℝ) (x : CDAlg ℝ 4) :
    laMap (∑ i, c i • e (f i)) (∑ j, d j • e (g j)) x
      = ∑ i, ∑ j, (c i * d j) • laMap (e (f i)) (e (g j)) x := by
  rw [laMap_trilinear.sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [laMap_trilinear.smul_left, laMap_trilinear.sum_mid, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [laMap_trilinear.smul_mid, smul_smul]

theorem mul_expand_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (F : ι → CDAlg ℝ 3) (d : κ → ℝ) (G : κ → CDAlg ℝ 3) :
    (∑ i, c i • F i) * (∑ j, d j • G j) = ∑ i, ∑ j, (c i * d j) • (F i * G j) := by
  rw [alt_mul_isBilinear.sum_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alt_mul_isBilinear.smul_left, alt_mul_isBilinear.sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [alt_mul_isBilinear.smul_right, smul_smul]

/-- A trilinear map that vanishes on all basis triples with fixed first two slots
    vanishes for arbitrary third argument. -/
theorem laMap_e_e_zero {i j : Fin (2^4)}
    (h : ∀ k, laMap (e i) (e j) (e k) = (0 : CDAlg ℝ 4)) (x : CDAlg ℝ 4) :
    laMap (e i) (e j) x = 0 := by
  conv_lhs => rw [basis_expansion x]
  rw [laMap_trilinear.sum_right]
  exact Finset.sum_eq_zero (fun k _ => by rw [laMap_trilinear.smul_right, h k, smul_zero])

/-- Antisymmetric double sums with a symmetric coefficient weight vanish. -/
theorem sum_sum_smul_antisym {ι : Type*} [Fintype ι] (c : ι → ℝ) (G : ι → ι → CDAlg ℝ 4)
    (h : ∀ i j, G i j + G j i = 0) :
    (∑ i, ∑ j, (c i * c j) • G i j) = 0 := by
  have hswap : (∑ i, ∑ j, (c i * c j) • G i j) = ∑ i, ∑ j, (c i * c j) • G j i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by rw [mul_comm]))
  have h2 : (2 : ℝ) • (∑ i, ∑ j, (c i * c j) • G i j) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hswap]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [← smul_add, h i j, smul_zero]
  exact eq_zero_of_smul_eq_zero two_ne_zero h2

/-! ## 8. `assoc s s = laMap (cdLo-part) (cdHi-part)` -/

/-- Low-half part of a sedenion, as an element of 𝕊. -/
def loPart (x : CDAlg ℝ 4) : CDAlg ℝ 4 := ∑ p : Fin (2^3), x.coord (loIdx p) • e (loIdx p)

/-- High-half part of a sedenion, as an element of 𝕊. -/
def hiPart (x : CDAlg ℝ 4) : CDAlg ℝ 4 := ∑ q : Fin (2^3), x.coord (hiIdx q) • e (hiIdx q)

theorem part_split (x : CDAlg ℝ 4) : x = loPart x + hiPart x := split_eq x

theorem laMap_loPart_loPart (x y : CDAlg ℝ 4) : laMap (loPart x) (loPart x) y = 0 := by
  rw [loPart, laMap_expand_sums]
  refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun r _ => ?_))
  rw [laMap_e_e_zero (fun k => by rw [laMap_e, laCoeffZ_lo_lo]; simp), smul_zero]

theorem laMap_hiPart_hiPart (x y : CDAlg ℝ 4) : laMap (hiPart x) (hiPart x) y = 0 := by
  rw [hiPart, laMap_expand_sums]
  refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun r _ => ?_))
  rw [laMap_e_e_zero (fun k => by rw [laMap_e, laCoeffZ_hi_hi]; simp), smul_zero]

/-- **The alternator only sees the cross term.**  For EVERY sedenion `s`,
    `[s, s, x] = laMap (loPart s) (hiPart s) x` — the two octonion copies
    `𝕆 ⊕ 0` and `0 ⊕ 𝕆` are individually alternator-flat, so the whole left
    alternator of `s` is the polarized cross term between its components. -/
theorem assoc_self_eq_laMap (s x : CDAlg ℝ 4) :
    assoc s s x = laMap (loPart s) (hiPart s) x := by
  have hll : assoc (loPart s) (loPart s) x = 0 := by
    have h2 : (2 : ℝ) • assoc (loPart s) (loPart s) x = 0 := by
      rw [two_smul]; exact laMap_loPart_loPart s x
    exact eq_zero_of_smul_eq_zero two_ne_zero h2
  have hhh : assoc (hiPart s) (hiPart s) x = 0 := by
    have h2 : (2 : ℝ) • assoc (hiPart s) (hiPart s) x = 0 := by
      rw [two_smul]; exact laMap_hiPart_hiPart s x
    exact eq_zero_of_smul_eq_zero two_ne_zero h2
  conv_lhs => rw [part_split s]
  rw [assoc_trilinear.add_left, assoc_trilinear.add_mid, assoc_trilinear.add_mid, hll, hhh, laMap]
  abel

/-! ## 9. T2a — the sedenion alternator vanishes iff the CD components commute -/

theorem loIdx_zero : loIdx (0 : Fin (2^3)) = (0 : Fin (2^4)) := by decide

theorem idx5 : ∀ p q : Fin (2^3), ∀ k : Fin (2^4),
    (loIdx p ^^^ hiIdx q ^^^ k) = (loIdx q ^^^ hiIdx p ^^^ k) := by decide

/-- Embedding of an octonion into the low half of 𝕊. -/
def loOf (a : CDAlg ℝ 3) : CDAlg ℝ 4 := ∑ p : Fin (2^3), a.coord p • e (loIdx p)

/-- Embedding of an octonion into the high half of 𝕊. -/
def hiOf (b : CDAlg ℝ 3) : CDAlg ℝ 4 := ∑ q : Fin (2^3), b.coord q • e (hiIdx q)

theorem loPart_eq_loOf (s : CDAlg ℝ 4) : loPart s = loOf (cdLo s) := rfl
theorem hiPart_eq_hiOf (s : CDAlg ℝ 4) : hiPart s = hiOf (cdHi s) := rfl

theorem hiOf_add (b b' : CDAlg ℝ 3) : hiOf (b + b') = hiOf b + hiOf b' := by
  rw [hiOf, hiOf, hiOf, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _ => by rw [add_coord, add_smul])

theorem hiOf_smul (r : ℝ) (b : CDAlg ℝ 3) : hiOf (r • b) = r • hiOf b := by
  rw [hiOf, hiOf, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun q _ => by rw [smul_coord, smul_smul])

theorem hiOf_one : hiOf (1 : CDAlg ℝ 3) = e (hiIdx 0) := by
  rw [hiOf, Finset.sum_eq_single (0 : Fin (2^3))]
  · rw [one_coord, if_pos rfl, one_smul]
  · intro b _ hb; rw [one_coord, if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Basis value of the high-half contraction of the polarized alternator. -/
theorem sedContract_basis (p q : Fin (2^3)) :
    cdHi (∑ t : Fin (2^3), e (hiIdx t) * laMap (e (loIdx p)) (e (hiIdx q)) (e (hiIdx t)))
      = (4 : ℝ) • ((e p : CDAlg ℝ 3) * e q - e q * e p) := by
  have hterm : ∀ t : Fin (2^3),
      (e (hiIdx t) : CDAlg ℝ 4) * laMap (e (loIdx p)) (e (hiIdx q)) (e (hiIdx t))
        = ((laCoeffZ 4 (loIdx p) (hiIdx q) (hiIdx t)
            * mulCoeff 4 (hiIdx t) (loIdx (p ^^^ q ^^^ t)) : Int) : ℝ) • e (hiIdx (p ^^^ q)) := by
    intro t
    rw [laMap_e, idx3, mul_smul_right, e_mul_e, smul_smul, idx4]
    push_cast; ring_nf
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hterm t), ← Finset.sum_smul,
    ← Int.cast_sum, sedContractZ, cdHi_smul, cdHi_e_hiIdx]
  rw [e_mul_e, e_mul_e, xor_comm_fin q p, ← sub_smul, smul_smul]
  push_cast
  ring_nf

/-- **The sedenion contraction identity.**  For EVERY sedenion `s`,
    `cdHi ( Σ_t e_{8+t} · [s, s, e_{8+t}] ) = 4 · (cdLo s · cdHi s − cdHi s · cdLo s)`.
    Contracting the left alternator against the high-half basis recovers exactly
    `4×` the commutator of the two Cayley–Dickson components — so the alternator
    determines the commutator. -/
theorem sedenion_alternator_contract (s : CDAlg ℝ 4) :
    cdHi (∑ t : Fin (2^3), e (hiIdx t) * assoc s s (e (hiIdx t)))
      = (4 : ℝ) • (cdLo s * cdHi s - cdHi s * cdLo s) := by
  have hstep : ∀ t : Fin (2^3),
      (e (hiIdx t) : CDAlg ℝ 4) * assoc s s (e (hiIdx t))
        = ∑ p : Fin (2^3), ∑ q : Fin (2^3),
            (s.coord (loIdx p) * s.coord (hiIdx q)) •
              ((e (hiIdx t) : CDAlg ℝ 4)
                * laMap (e (loIdx p)) (e (hiIdx q)) (e (hiIdx t))) := by
    intro t
    rw [assoc_self_eq_laMap, loPart, hiPart, laMap_expand_sums, alt_mul_isBilinear.sum_right]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [alt_mul_isBilinear.sum_right]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [mul_smul_right]
  have hL : (∑ t : Fin (2^3), (e (hiIdx t) : CDAlg ℝ 4) * assoc s s (e (hiIdx t)))
      = ∑ p : Fin (2^3), ∑ q : Fin (2^3), ∑ t : Fin (2^3),
          (s.coord (loIdx p) * s.coord (hiIdx q)) •
            ((e (hiIdx t) : CDAlg ℝ 4)
              * laMap (e (loIdx p)) (e (hiIdx q)) (e (hiIdx t))) := by
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hstep t), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  have hRHS : (4 : ℝ) • (cdLo s * cdHi s - cdHi s * cdLo s)
      = ∑ p : Fin (2^3), ∑ q : Fin (2^3),
          (s.coord (loIdx p) * s.coord (hiIdx q)) •
            ((4 : ℝ) • ((e p : CDAlg ℝ 3) * e q - e q * e p)) := by
    have h1 : cdLo s * cdHi s
        = ∑ p : Fin (2^3), ∑ q : Fin (2^3),
            (s.coord (loIdx p) * s.coord (hiIdx q)) • ((e p : CDAlg ℝ 3) * e q) := by
      conv_lhs => rw [basis_expansion (cdLo s), basis_expansion (cdHi s)]
      rw [mul_expand_sums]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => rfl))
    have h2 : cdHi s * cdLo s
        = ∑ p : Fin (2^3), ∑ q : Fin (2^3),
            (s.coord (loIdx p) * s.coord (hiIdx q)) • ((e q : CDAlg ℝ 3) * e p) := by
      conv_lhs => rw [basis_expansion (cdHi s), basis_expansion (cdLo s)]
      rw [mul_expand_sums, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun q _ => by rw [cdHi_coord, cdLo_coord, mul_comm]))
    rw [h1, h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← smul_sub, smul_smul, smul_smul, mul_comm]
  rw [hL, cdHi_sum, hRHS]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [cdHi_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← Finset.smul_sum, cdHi_smul, sedContract_basis]

/-- The two `cdLo/cdHi` cross-basis alternators are antisymmetric in their indices. -/
theorem laMap_lo_hi_antisym (p q : Fin (2^3)) (x : CDAlg ℝ 4) :
    laMap (e (loIdx p)) (e (hiIdx q)) x + laMap (e (loIdx q)) (e (hiIdx p)) x = 0 := by
  conv_lhs => rw [basis_expansion x]
  rw [laMap_trilinear.sum_right, laMap_trilinear.sum_right, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [laMap_trilinear.smul_right, laMap_trilinear.smul_right, ← smul_add, laMap_e, laMap_e,
    idx5 p q k, ← add_smul,
    show ((laCoeffZ 4 (loIdx p) (hiIdx q) k : ℝ) + (laCoeffZ 4 (loIdx q) (hiIdx p) k : ℝ))
      = ((laCoeffZ 4 (loIdx p) (hiIdx q) k + laCoeffZ 4 (loIdx q) (hiIdx p) k : Int) : ℝ) by
      push_cast; ring,
    laCoeffZ_lo_hi_sym]
  simp

/-- `s = (a, 1)` is alternator-free: `laMap (loOf a) e₈ x = 0`. -/
theorem laMap_loOf_hiOne (a : CDAlg ℝ 3) (x : CDAlg ℝ 4) :
    laMap (loOf a) (e (hiIdx 0)) x = 0 := by
  rw [loOf, laMap_trilinear.sum_left]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  rw [laMap_trilinear.smul_left,
    laMap_e_e_zero (fun k => by rw [laMap_e, laCoeffZ_lo_hi0]; simp), smul_zero]

/-- `s = (a, a)` is alternator-free: `laMap (loOf a) (hiOf a) x = 0`. -/
theorem laMap_loOf_hiOf_self (a : CDAlg ℝ 3) (x : CDAlg ℝ 4) :
    laMap (loOf a) (hiOf a) x = 0 := by
  rw [loOf, hiOf, laMap_expand_sums]
  exact sum_sum_smul_antisym (fun p => a.coord p)
    (fun p q => laMap (e (loIdx p)) (e (hiIdx q)) x)
    (fun p q => laMap_lo_hi_antisym p q x)

/-- **T2a — the landscape identity for the sedenion left alternator.**
    For an IMAGINARY sedenion `s`, written in the Cayley–Dickson pair
    representation as `s = (a, b)` with `a = cdLo s ∈ Im 𝕆` and `b = cdHi s ∈ 𝕆`:

      `(∀ x, (s·s)·x − s·(s·x) = 0)  ↔  a·b = b·a`.

    The left alternator of `s` vanishes identically **iff** its two octonion
    components commute.  `⇒` is the contraction identity
    (`sedenion_alternator_contract`); `⇐` runs through the octonion commutant
    (`b ∈ span{1,a}`) and the two kernel-checked alternator-flat rows
    `s = (a, 1)` and `s = (a, a)`. -/
theorem sedenion_alternator_vanishes_iff_components_commute {s : CDAlg ℝ 4}
    (hs : s.coord 0 = 0) :
    (∀ x, assoc s s x = 0) ↔ cdLo s * cdHi s = cdHi s * cdLo s := by
  constructor
  · intro h
    have hc := sedenion_alternator_contract s
    have hz : ∀ t : Fin (2^3), (e (hiIdx t) : CDAlg ℝ 4) * assoc s s (e (hiIdx t)) = 0 := by
      intro t; rw [h, alt_mul_zero]
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hz t), Finset.sum_const_zero,
      cdHi_zero] at hc
    have hz4 := eq_zero_of_smul_eq_zero (r := (4 : ℝ)) (by norm_num) hc.symm
    exact sub_eq_zero.mp hz4
  · intro hcomm x
    rw [assoc_self_eq_laMap, loPart_eq_loOf, hiPart_eq_hiOf]
    by_cases ha : cdLo s = 0
    · have h0 : loOf (cdLo s) = 0 := by
        rw [loOf]
        refine Finset.sum_eq_zero (fun p _ => ?_)
        rw [show (cdLo s).coord p = 0 by rw [ha]; rfl, zero_smul]
      rw [h0]
      have hz := laMap_trilinear.smul_left (R := ℝ) (n := 4) 0 0 (hiOf (cdHi s)) x
      simpa using hz
    · have ha0 : (cdLo s).coord 0 = 0 := by rw [cdLo_coord, loIdx_zero]; exact hs
      have hspan := octonion_commutant ha0 ha hcomm
      rw [hspan, hiOf_add, hiOf_smul, hiOf_smul, hiOf_one]
      rw [laMap_trilinear.add_mid, laMap_trilinear.smul_mid, laMap_trilinear.smul_mid,
        laMap_loOf_hiOne, laMap_loOf_hiOf_self]
      simp

/-! ## 10. Non-vacuity: BOTH sides of T2a are realized

The ↔ would be worthless if one side were unreachable.  It is not:
`s = Σ e_a` (T1) lands on the alternator-free side, and the standard
non-alternativity witness `s = e₁ + e₁₀` lands on the other — and T2a
RE-DERIVES its non-alternativity from a two-line octonion commutator check. -/

theorem sAll_coord_zero : sAll.coord 0 = 0 := by rw [sAll_coord, if_pos rfl]

/-- The CD components of `Σ_{a=1}^{15} e_a` commute (consequence of T1 + T2a). -/
theorem sAll_components_commute : cdLo sAll * cdHi sAll = cdHi sAll * cdLo sAll :=
  (sedenion_alternator_vanishes_iff_components_commute sAll_coord_zero).mp sAll_assoc_zero

theorem sedWitX_coord_zero : sedWitX.coord 0 = 0 := by
  simp [sedWitX, e_coord, Fin.ext_iff]

theorem sedWitX_cdLo : cdLo sedWitX = (e ⟨1, by norm_num⟩ : CDAlg ℝ 3) := by
  have h1 : ∀ p : Fin (2^3),
      (loIdx p = (⟨1, by norm_num⟩ : Fin (2^4))) ↔ (p = ⟨1, by norm_num⟩) := by decide
  have h2 : ∀ p : Fin (2^3), loIdx p ≠ (⟨10, by norm_num⟩ : Fin (2^4)) := by decide
  ext p
  rw [cdLo_coord, sedWitX, add_coord, e_coord, e_coord, e_coord, if_neg (h2 p)]
  by_cases hp : p = ⟨1, by norm_num⟩
  · rw [if_pos ((h1 p).mpr hp), if_pos hp]; ring
  · rw [if_neg (fun hh => hp ((h1 p).mp hh)), if_neg hp]; ring

theorem sedWitX_cdHi : cdHi sedWitX = (e ⟨2, by norm_num⟩ : CDAlg ℝ 3) := by
  have h1 : ∀ q : Fin (2^3),
      (hiIdx q = (⟨10, by norm_num⟩ : Fin (2^4))) ↔ (q = ⟨2, by norm_num⟩) := by decide
  have h2 : ∀ q : Fin (2^3), hiIdx q ≠ (⟨1, by norm_num⟩ : Fin (2^4)) := by decide
  ext q
  rw [cdHi_coord, sedWitX, add_coord, e_coord, e_coord, e_coord, if_neg (h2 q)]
  by_cases hq : q = ⟨2, by norm_num⟩
  · rw [if_pos ((h1 q).mpr hq), if_pos hq]; ring
  · rw [if_neg (fun hh => hq ((h1 q).mp hh)), if_neg hq]; ring

/-- `e₁` and `e₂` do not commute in 𝕆 (constructed witness, not a comment). -/
theorem octonion_e1_e2_not_commute :
    (e ⟨1, by norm_num⟩ : CDAlg ℝ 3) * e ⟨2, by norm_num⟩
      ≠ (e ⟨2, by norm_num⟩ : CDAlg ℝ 3) * e ⟨1, by norm_num⟩ := by
  intro h
  have hxor : ((⟨2, by norm_num⟩ : Fin (2^3)) ^^^ ⟨1, by norm_num⟩)
      = ((⟨1, by norm_num⟩ : Fin (2^3)) ^^^ ⟨2, by norm_num⟩) := by decide
  rw [e_mul_e, e_mul_e, hxor] at h
  have hc := congrArg
    (fun z => CDAlg.coord z ((⟨1, by norm_num⟩ : Fin (2^3)) ^^^ ⟨2, by norm_num⟩)) h
  simp only [smul_coord, e_coord] at hc
  have hz : mulCoeff 3 (⟨1, by norm_num⟩ : Fin (2^3)) ⟨2, by norm_num⟩
      = mulCoeff 3 (⟨2, by norm_num⟩ : Fin (2^3)) ⟨1, by norm_num⟩ := by exact_mod_cast hc
  revert hz
  decide

/-- **Non-vacuity / payoff: sedenion non-alternativity RE-DERIVED from T2a.**
    For `s = e₁ + e₁₀` the CD components are `(e₁, e₂)`, which do not commute, so
    by T2a the left alternator of `s` cannot vanish identically — an independent
    proof that 𝕊 is not alternative, obtained from the commutator criterion
    rather than from a hand-picked associator coordinate. -/
theorem sedWitX_alternator_ne_zero : ¬ (∀ x, assoc sedWitX sedWitX x = 0) := by
  intro hall
  have hcomm :=
    (sedenion_alternator_vanishes_iff_components_commute sedWitX_coord_zero).mp hall
  rw [sedWitX_cdLo, sedWitX_cdHi] at hcomm
  exact octonion_e1_e2_not_commute hcomm

/-- 𝕊 is not alternative — re-derived through the T2a commutator criterion. -/
theorem sedenion_not_alternative_via_commutator :
    ∃ x y : CDAlg ℝ 4, (x * x) * y ≠ x * (x * y) := by
  obtain ⟨y, hy⟩ := not_forall.mp sedWitX_alternator_ne_zero
  exact ⟨sedWitX, y, fun hcontra => hy (by rw [assoc, hcontra, sub_self])⟩

/-! ## 11. The `L_s²` form of the alternator (T2c, scalar part)

For an imaginary `s` the CD square identity collapses to `s·s = −N(s)`, so the
left alternator is exactly the defect of `L_s²` from `−N(s)·id`. -/

/-- For imaginary `s`: `s·s = −N(s)·1`. -/
theorem imaginary_sq (s : CDAlg ℝ n) (hs : s.coord 0 = 0) :
    s * s = (-(N s)) • (1 : CDAlg ℝ n) := by
  rw [cdAlg_sq_eq, hs, mul_zero, zero_smul, zero_sub, neg_smul]

/-- **T2c (scalar part).**  For imaginary `s`,
    `s·(s·x) = −N(s)·x − [s, s, x]`, i.e. `−L_s² = N(s)·id + T_s` for
    `T_s x := [s, s, x] = (s·s)·x − s·(s·x)`.
    So the alternator is precisely the failure of `L_s²` to be the scalar
    `−N(s)`. -/
theorem left_mul_sq_imaginary (s x : CDAlg ℝ n) (hs : s.coord 0 = 0) :
    s * (s * x) = (-(N s)) • x - assoc s s x := by
  rw [assoc, imaginary_sq s hs, mul_smul_left, cd_one_mul]
  abel

/-- `N (Σ_{a=1}^{15} e_a) = 15` — the scalar that T1 produces. -/
theorem N_sAll : N sAll = 15 := by
  have h : ∀ i : Fin (2^4), (sAll.coord i)^2 = 1 - (if i = 0 then (1:ℝ) else 0) := by
    intro i; rw [sAll_coord]; split <;> norm_num
  rw [N_def, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i),
    Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin (2^4)) (fun _ => (1:ℝ)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, if_pos (Finset.mem_univ _)]
  norm_num

/-- Cross-check: T1 is exactly the `N(s) = 15` instance of T2c — the two
    independent computations agree. -/
theorem sAll_left_mul_sq_via_T2c (x : CDAlg ℝ 4) :
    sAll * (sAll * x) = (-(N sAll)) • x := by
  rw [left_mul_sq_imaginary sAll x sAll_coord_zero, sAll_assoc_zero, sub_zero]

/-! ### T2a (𝕊) completeness audit -/

#print axioms laCoeffZ_lo_lo
#print axioms laCoeffZ_hi_hi
#print axioms laCoeffZ_lo_hi0
#print axioms laCoeffZ_lo_hi_sym
#print axioms sedContractZ
#print axioms assoc_self_eq_laMap
#print axioms sedenion_alternator_contract
#print axioms sedenion_alternator_vanishes_iff_components_commute
#print axioms sAll_components_commute
#print axioms sedWitX_alternator_ne_zero
#print axioms sedenion_not_alternative_via_commutator
#print axioms left_mul_sq_imaginary
#print axioms N_sAll
#print axioms sAll_left_mul_sq_via_T2c

end QBP.Foundations.CDAlg
