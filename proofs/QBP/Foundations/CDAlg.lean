/-
  QBP.Foundations.CDAlg
  =====================

  The Cayley–Dickson carrier `CDAlg R n` — a ring-generic coordinate algebra of
  dimension `2^n` over a commutative ring `R`, with multiplication given by the
  Cayley–Dickson structure constants `mulCoeff`.  This is the keystone carrier the
  #474 / #476 / #477 operations-complete program consumes: ℝ→ℂ→ℍ→𝕆→𝕊 are the
  instances `CDAlg R 0..4`.

  Design (federation Lean standard, ~/Documents/inter/lean-proof-best-practices.md):
  * `CDAlg` carries ONLY the structure that genuinely holds at every level:
    `AddCommGroup`, `Module R`, `One`, `Mul`.  It is deliberately NOT a `Ring`
    (𝕆 is non-associative, 𝕊 is non-alternative) — see the operations-complete
    matrix in `docs/foundations/scope-deliberation-2026-05-31.md`.
  * `mulCoeff` is DEFINED by the genuine Cayley–Dickson doubling recursion
    `(a,b)(c,d) = (ac − d̄b, da + bc̄)` on the high-bit / low-index split of each
    `Fin (2^n)` index.  Its correctness is pinned by `mulCoeff_four_eq_sgnTable`:
    it agrees on all 256 basis pairs (kernel `decide`) with the independently
    kernel-verified sedenion sign table `SedenionOctonionCount.sgnTable`, and by
    `mulCoeff_three_eq_fano` with the F3 octonion construction.  No table is
    transcribed by hand here.
  * Multiplication is `e_i · e_j = mulCoeff n i j • e_{i ⊕ j}` (XOR-on-`Fin`
    index encoding, consistent with `SedenionOctonionCount` / `FanoOrientationF3`).

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom — every main result depends only on
  `{propext, Classical.choice, Quot.sound}`.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Module.Basic
import QBP.Foundations.SedenionOctonionCount
import QBP.Foundations.FanoOrientationF3

namespace QBP.Foundations.CDAlg

/-! ## 1. The carrier and its module structure -/

/-- The Cayley–Dickson carrier of dimension `2^n` over `R`: a tuple of `2^n`
    coordinates.  Levels ℝ,ℂ,ℍ,𝕆,𝕊 are `n = 0,1,2,3,4`. -/
structure CDAlg (R : Type*) [CommRing R] (n : ℕ) where
  /-- The coordinate vector. -/
  coord : Fin (2^n) → R

variable {R : Type*} [CommRing R] {n : ℕ}

@[ext] theorem ext (x y : CDAlg R n) (h : ∀ i, x.coord i = y.coord i) : x = y := by
  cases x; cases y; simp only [CDAlg.mk.injEq]; funext i; exact h i

instance : Add (CDAlg R n) := ⟨fun x y => ⟨fun i => x.coord i + y.coord i⟩⟩
instance : Zero (CDAlg R n) := ⟨⟨fun _ => 0⟩⟩
instance : Neg (CDAlg R n) := ⟨fun x => ⟨fun i => - x.coord i⟩⟩
instance : SMul R (CDAlg R n) := ⟨fun r x => ⟨fun i => r * x.coord i⟩⟩

@[simp] theorem add_coord (x y : CDAlg R n) (i) : (x + y).coord i = x.coord i + y.coord i := rfl
@[simp] theorem zero_coord (i) : (0 : CDAlg R n).coord i = 0 := rfl
@[simp] theorem neg_coord (x : CDAlg R n) (i) : (-x).coord i = - x.coord i := rfl
@[simp] theorem smul_coord (r : R) (x : CDAlg R n) (i) : (r • x).coord i = r * x.coord i := rfl

instance : AddCommGroup (CDAlg R n) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  neg_add_cancel a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module R (CDAlg R n) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

@[simp] theorem sub_coord (x y : CDAlg R n) (i) : (x - y).coord i = x.coord i - y.coord i := by
  rw [sub_eq_add_neg, add_coord, neg_coord, sub_eq_add_neg]

/-! ## 2. Basis and basis expansion -/

/-- The basis element `eᵢ`: a 1 in coordinate `i`, 0 elsewhere. -/
def e (i : Fin (2^n)) : CDAlg R n := ⟨fun j => if j = i then 1 else 0⟩

@[simp] theorem e_coord (i j : Fin (2^n)) : (e i : CDAlg R n).coord j = if j = i then 1 else 0 := rfl

/-- The coordinate of a `Finset.sum` is the sum of coordinates. -/
theorem sum_coord {ι : Type*} (s : Finset ι) (f : ι → CDAlg R n) (j : Fin (2^n)) :
    (∑ i ∈ s, f i).coord j = ∑ i ∈ s, (f i).coord j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_coord, ih]

/-- **Basis expansion.**  Every element is the sum of its coordinates times basis
    vectors: `x = ∑ i, x.coord i • eᵢ`. -/
theorem basis_expansion (x : CDAlg R n) : x = ∑ i, x.coord i • e i := by
  ext j
  rw [sum_coord]
  simp only [smul_coord, e_coord, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j (fun i => x.coord i)]
  simp

/-! ## 3. Cayley–Dickson structure constants `mulCoeff`

The recursion mirrors the doubling product `(a,b)(c,d) = (ac − d̄b, da + bc̄)`,
splitting each `Fin (2^(n+1))` index into a high bit (component selector) and a
low part (index within the component). -/

/-- Conjugation sign of a basis index: `+1` for the real unit (index 0), `−1` for
    every imaginary unit.  `conj eᵢ = conjSign n i • eᵢ`. -/
def conjSign (n : ℕ) (i : Fin (2^n)) : Int := if i.val = 0 then 1 else -1

/-- Cayley–Dickson structure constant: `eᵢ · e_j = mulCoeff n i j • e_{i ⊕ j}`. -/
def mulCoeff : (n : ℕ) → Fin (2^n) → Fin (2^n) → Int
  | 0, _, _ => 1
  | n+1, i, j =>
    let half : ℕ := 2^n
    let pi : ℕ := i.val / half
    let ai : ℕ := i.val % half
    let pj : ℕ := j.val / half
    let aj : ℕ := j.val % half
    have hai : ai < 2^n := Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))
    have haj : aj < 2^n := Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))
    let a : Fin (2^n) := ⟨ai, hai⟩
    let c : Fin (2^n) := ⟨aj, haj⟩
    match pi, pj with
    | 0, 0 => mulCoeff n a c                       -- (a,0)(c,0) → (ac, 0)
    | 0, 1 => mulCoeff n c a                       -- (a,0)(0,d) → (0, da)
    | 1, 0 => conjSign n c * mulCoeff n a c        -- (0,b)(c,0) → (0, b c̄)
    | _, _ => - (conjSign n c * mulCoeff n c a)    -- (0,b)(0,d) → (-d̄ b, 0)

/-- **Provenance: agreement with the sedenion sign table (n = 4).**  `mulCoeff 4`
    equals the kernel-verified `SedenionOctonionCount.sgnTable` on all 256 basis
    pairs.  This pins the recursion to the independently-built CD sedenion table —
    no hand-transcription. -/
theorem mulCoeff_four_eq_sgnTable :
    ∀ i j : Fin 16, mulCoeff 4 i j = QBP.Foundations.SedenionOctonionCount.sgnTable i j := by
  decide

/-- **Provenance: agreement with the F3 octonion construction (n = 3).**  For all
    basis indices `i j : Fin 8`, the `mulCoeff 3` sign equals the sign of the F3
    Cayley–Dickson octonion product `Omul (e i) (e j)` (from `FanoOrientationF3`),
    whose table is `eᵢ·e_j = (fanoTableF4 i j).1 • e_{(fanoTableF4 i j).2}`. -/
theorem mulCoeff_three_eq_fano :
    ∀ i j : Fin 8,
      mulCoeff 3 i j = (QBP.Foundations.FanoOrientationF3.fanoTableF4 i j).1 := by
  decide

/-! ## 4. Multiplication via structure constants -/

instance : One (CDAlg R n) := ⟨e 0⟩

theorem one_def : (1 : CDAlg R n) = e 0 := rfl

@[simp] theorem one_coord (k : Fin (2^n)) :
    (1 : CDAlg R n).coord k = if k = 0 then 1 else 0 := rfl

instance : Mul (CDAlg R n) :=
  ⟨fun x y => ⟨fun k => ∑ i, ∑ j, if (i ^^^ j : Fin (2^n)) = k then
      (mulCoeff n i j : R) * x.coord i * y.coord j else 0⟩⟩

theorem mul_coord (x y : CDAlg R n) (k : Fin (2^n)) :
    (x * y).coord k = ∑ i, ∑ j, if (i ^^^ j : Fin (2^n)) = k then
      (mulCoeff n i j : R) * x.coord i * y.coord j else 0 := rfl

/-- **Product of two basis elements:** `eᵢ · e_j = mulCoeff n i j • e_{i ⊕ j}`. -/
theorem e_mul_e (i j : Fin (2^n)) :
    (e i * e j : CDAlg R n) = (mulCoeff n i j : R) • e (i ^^^ j) := by
  ext k
  rw [mul_coord, smul_coord, e_coord]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp only [e_coord, if_true]
      by_cases h : (i ^^^ j : Fin (2^n)) = k
      · simp [h]
      · rw [if_neg h, if_neg (fun hk => h hk.symm), mul_zero]
    · intro b _ hb; simp only [e_coord, if_neg hb, mul_zero]; split <;> rfl
    · intro h; simp at h
  · intro b _ hb
    apply Finset.sum_eq_zero; intro q _
    simp only [e_coord, if_neg hb, mul_zero, zero_mul]; split <;> rfl
  · intro h; simp at h

/-! ## 5. Bilinearity of multiplication -/

/-- Multiplication is additive in the left argument. -/
theorem mul_add_left (x x' y : CDAlg R n) : (x + x') * y = x * y + x' * y := by
  ext k
  simp only [mul_coord, add_coord, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : (i ^^^ j : Fin (2^n)) = k <;> simp [h, mul_add, add_mul]

/-- Multiplication is additive in the right argument. -/
theorem mul_add_right (x y y' : CDAlg R n) : x * (y + y') = x * y + x * y' := by
  ext k
  simp only [mul_coord, add_coord, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : (i ^^^ j : Fin (2^n)) = k <;> simp [h, mul_add]

/-- Multiplication is `R`-homogeneous in the left argument. -/
theorem mul_smul_left (r : R) (x y : CDAlg R n) : (r • x) * y = r • (x * y) := by
  ext k
  simp only [mul_coord, smul_coord, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : (i ^^^ j : Fin (2^n)) = k <;> simp only [h, if_true, if_false] <;> ring

/-- Multiplication is `R`-homogeneous in the right argument. -/
theorem mul_smul_right (r : R) (x y : CDAlg R n) : x * (r • y) = r • (x * y) := by
  ext k
  simp only [mul_coord, smul_coord, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : (i ^^^ j : Fin (2^n)) = k <;> simp only [h, if_true, if_false] <;> ring

/-! ## 6. Conjugation, real/imaginary parts, norm form -/

/-- Conjugation: negate every imaginary coordinate, fix the real one. -/
def conj (x : CDAlg R n) : CDAlg R n :=
  ⟨fun i => if i.val = 0 then x.coord i else - x.coord i⟩

@[simp] theorem conj_coord (x : CDAlg R n) (i) :
    (conj x).coord i = if i.val = 0 then x.coord i else - x.coord i := rfl

/-- Real (scalar) part: the coefficient on `e₀`, returned as a scalar. -/
def reCoord (x : CDAlg R n) : R := x.coord 0

/-- The norm FORM `N(x) = ∑ xᵢ²`.  This is the algebraic norm form (sum of squares
    of coordinates), NOT identified with any spacetime metric (non-identification
    clause, scope-deliberation §5 guardrail 1). -/
def N (x : CDAlg R n) : R := ∑ i, (x.coord i)^2

@[simp] theorem N_def (x : CDAlg R n) : N x = ∑ i, (x.coord i)^2 := rfl

/-! ## 7. Structural facts about `mulCoeff` (general `n`, by induction)

These power the quadraticity theorem (§8) and downstream conjugation/norm laws. -/

/-- The low part of an index at level `n+1`. -/
def lo (n : ℕ) (i : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨i.val % 2^n, Nat.mod_lt _ (by positivity)⟩

theorem lo_val (n : ℕ) (i : Fin (2^(n+1))) : (lo n i).val = i.val % 2^n := rfl

theorem zero_mk_eq (n : ℕ) (h) : (⟨0, h⟩ : Fin (2^n)) = 0 := by apply Fin.ext; simp

theorem div_lt_two (n : ℕ) (j : Fin (2^(n+1))) : j.val / 2^n < 2 := by
  have hj : j.val < 2^(n+1) := j.isLt
  have h2 : (2:ℕ)^(n+1) = 2^n * 2 := by ring
  exact Nat.div_lt_of_lt_mul (h2 ▸ hj)

theorem div_zero_or_one (n : ℕ) (j : Fin (2^(n+1))) :
    j.val / 2^n = 0 ∨ j.val / 2^n = 1 := by
  have h := div_lt_two n j
  generalize j.val / 2^n = q at h ⊢
  omega

theorem conjSign_zero_of (n : ℕ) (i : Fin (2^n)) (hi : i.val = 0) : conjSign n i = 1 := by
  unfold conjSign; simp [hi]

theorem conjSign_neg_of (n : ℕ) (i : Fin (2^n)) (hi : i.val ≠ 0) : conjSign n i = -1 := by
  unfold conjSign; simp [hi]

theorem lt_two_pow_of_div_zero (n : ℕ) (i : Fin (2^(n+1))) (h : i.val / 2^n = 0) :
    i.val < 2^n := by
  by_contra hge
  push_neg at hge
  have : i.val / 2^n ≥ 1 := Nat.one_le_div_iff (by positivity) |>.mpr hge
  omega

theorem mod_eq_self_of_div_zero (n : ℕ) (i : Fin (2^(n+1))) (h : i.val / 2^n = 0) :
    i.val % 2^n = i.val :=
  Nat.mod_eq_of_lt (lt_two_pow_of_div_zero n i h)

theorem val_eq_zero_iff (n : ℕ) (i : Fin (2^(n+1))) :
    i.val = 0 ↔ i.val / 2^n = 0 ∧ (lo n i).val = 0 := by
  rw [lo_val]
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨hd, hm⟩
    have h1 := Nat.div_add_mod i.val (2^n)
    rw [hd, hm] at h1; omega

theorem eq_of_hi_lo (n : ℕ) (i j : Fin (2^(n+1)))
    (hd : i.val / 2^n = j.val / 2^n) (hm : (lo n i).val = (lo n j).val) : i = j := by
  apply Fin.ext
  rw [lo_val, lo_val] at hm
  have hi := Nat.div_add_mod i.val (2^n)
  have hj := Nat.div_add_mod j.val (2^n)
  rw [hd, hm] at hi; omega

/-- Combined structural facts about `mulCoeff`, proven by induction on `n`:
    products with the real unit are `+1`; squares of units are `+1` (real) / `−1`
    (imaginary); and distinct imaginary units anticommute. -/
theorem mulCoeff_props : ∀ n : ℕ,
    (∀ j : Fin (2^n), mulCoeff n 0 j = 1) ∧
    (∀ i : Fin (2^n), mulCoeff n i 0 = 1) ∧
    (∀ i : Fin (2^n), mulCoeff n i i = if i.val = 0 then 1 else -1) ∧
    (∀ i j : Fin (2^n), i.val ≠ 0 → j.val ≠ 0 → i ≠ j →
        mulCoeff n i j = - mulCoeff n j i) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun j => ?_, fun i => ?_, fun i => ?_, fun i j _ _ hij => ?_⟩
    · rfl
    · rfl
    · fin_cases i; rfl
    · exfalso; apply hij; apply Fin.ext
      have h1 : i.val < 2^0 := i.isLt
      have h2 : j.val < 2^0 := j.isLt
      simp only [pow_zero] at h1 h2; omega
  | succ n ih =>
    obtain ⟨ihL, ihR, ihS, ihA⟩ := ih
    refine ⟨fun j => ?_, fun i => ?_, fun i => ?_, fun i j hi0 hj0 hij => ?_⟩
    · rw [mulCoeff]
      simp only [Fin.val_zero, Nat.zero_div, Nat.zero_mod]
      rcases div_zero_or_one n j with hpj | hpj
      · rw [hpj]; simp only [zero_mk_eq]; exact ihL _
      · rw [hpj]; simp only [zero_mk_eq]; exact ihR _
    · rw [mulCoeff]
      simp only [Fin.val_zero, Nat.zero_div, Nat.zero_mod]
      rcases div_zero_or_one n i with hpi | hpi
      · rw [hpi]; simp only [zero_mk_eq]; exact ihR _
      · rw [hpi]; simp only [zero_mk_eq]
        rw [conjSign_zero_of n _ (by rfl), one_mul]; exact ihR _
    · rw [mulCoeff]
      rcases div_zero_or_one n i with hpi | hpi
      · rw [hpi]
        have hmod : i.val % 2^n = i.val := mod_eq_self_of_div_zero n i hpi
        rw [ihS ⟨i.val % 2^n, _⟩]; simp only [hmod]
      · rw [hpi]
        have hi0' : i.val ≠ 0 := by
          intro h0
          have hz : i.val / 2^n = 0 := by rw [h0]; simp
          rw [hz] at hpi; exact absurd hpi (by norm_num)
        rw [if_neg hi0']
        by_cases hlow : (i.val % 2^n) = 0
        · rw [conjSign_zero_of n ⟨i.val % 2^n, _⟩ (by simpa using hlow)]
          rw [ihS ⟨i.val % 2^n, _⟩]; simp [hlow]
        · rw [conjSign_neg_of n ⟨i.val % 2^n, _⟩ (by simpa using hlow)]
          rw [ihS ⟨i.val % 2^n, _⟩]; simp [hlow]
    · -- antisymmetry
      set a : Fin (2^n) := ⟨i.val % 2^n, Nat.mod_lt _ (by positivity)⟩ with ha
      set c : Fin (2^n) := ⟨j.val % 2^n, Nat.mod_lt _ (by positivity)⟩ with hc
      have hai : (lo n i).val = a.val := rfl
      have hcj : (lo n j).val = c.val := rfl
      rw [mulCoeff, mulCoeff]
      rcases div_zero_or_one n i with hpi | hpi <;>
        rcases div_zero_or_one n j with hpj | hpj <;>
        rw [hpi, hpj] <;> simp only [← ha, ← hc]
      · have hane : a.val ≠ 0 := fun h =>
          hi0 ((val_eq_zero_iff n i).mpr ⟨hpi, by rw [hai]; exact h⟩)
        have hcne : c.val ≠ 0 := fun h =>
          hj0 ((val_eq_zero_iff n j).mpr ⟨hpj, by rw [hcj]; exact h⟩)
        have hac : a ≠ c := fun h =>
          hij (eq_of_hi_lo n i j (by rw [hpi, hpj]) (by rw [hai, hcj, h]))
        exact ihA a c hane hcne hac
      · have hane : a.val ≠ 0 := fun h =>
          hi0 ((val_eq_zero_iff n i).mpr ⟨hpi, by rw [hai]; exact h⟩)
        rw [conjSign_neg_of n a hane]; ring
      · have hcne : c.val ≠ 0 := fun h =>
          hj0 ((val_eq_zero_iff n j).mpr ⟨hpj, by rw [hcj]; exact h⟩)
        rw [conjSign_neg_of n c hcne]; ring
      · have hac : a ≠ c := fun h =>
          hij (eq_of_hi_lo n i j (by rw [hpi, hpj]) (by rw [hai, hcj, h]))
        have haeq : a = 0 → mulCoeff n c a = 1 ∧ mulCoeff n a c = 1 := by
          intro h; rw [h]; exact ⟨ihR c, ihL c⟩
        have hceq : c = 0 → mulCoeff n c a = 1 ∧ mulCoeff n a c = 1 := by
          intro h; rw [h]; exact ⟨ihL a, ihR a⟩
        by_cases haz : a.val = 0
        · have ha0 : a = 0 := Fin.ext haz
          have hcne : c.val ≠ 0 := fun h => hac (Fin.ext (by rw [haz, h]))
          rw [conjSign_neg_of n c hcne, conjSign_zero_of n a haz]
          obtain ⟨e1, e2⟩ := haeq ha0; rw [e1, e2]; ring
        · by_cases hcz : c.val = 0
          · have hc0 : c = 0 := Fin.ext hcz
            rw [conjSign_zero_of n c hcz, conjSign_neg_of n a haz]
            obtain ⟨e1, e2⟩ := hceq hc0; rw [e1, e2]; ring
          · rw [conjSign_neg_of n c hcz, conjSign_neg_of n a haz]
            rw [ihA c a hcz haz (fun h => hac h.symm)]; ring

/-- `eₐ · e₀ = eₐ` at the coefficient level: `mulCoeff n 0 j = 1`. -/
theorem mulCoeff_zero_left (n : ℕ) (j : Fin (2^n)) : mulCoeff n 0 j = 1 :=
  (mulCoeff_props n).1 j
/-- `mulCoeff n i 0 = 1`. -/
theorem mulCoeff_zero_right (n : ℕ) (i : Fin (2^n)) : mulCoeff n i 0 = 1 :=
  (mulCoeff_props n).2.1 i
/-- Unit squares: `mulCoeff n i i = +1` (real) / `−1` (imaginary). -/
theorem mulCoeff_self (n : ℕ) (i : Fin (2^n)) :
    mulCoeff n i i = if i.val = 0 then 1 else -1 :=
  (mulCoeff_props n).2.2.1 i
/-- Distinct imaginary units anticommute: `mulCoeff n i j = − mulCoeff n j i`. -/
theorem mulCoeff_antisymm (n : ℕ) (i j : Fin (2^n))
    (hi : i.val ≠ 0) (hj : j.val ≠ 0) (hij : i ≠ j) :
    mulCoeff n i j = - mulCoeff n j i :=
  (mulCoeff_props n).2.2.2 i j hi hj hij

/-! ## 8. Quadraticity: `x·x = (2 Re x)·x − N(x)·1`

The Cayley–Dickson identity that powers the exp/log construction (span{1,x} ≅ ℂ).
Proven structurally (ℝ-coordinates are not decidable) via the `mulCoeff`
structural lemmas of §7. -/

/-- `i ⊕ 0 = i` on `Fin (2^n)`. -/
theorem xor_zero_right (i : Fin (2^n)) : (i ^^^ (0 : Fin (2^n))) = i := by
  apply Fin.ext; rw [Fin.xor_val_of_two_pow]; simp

/-- `0 ⊕ k = k`. -/
theorem xor_zero_left (k : Fin (2^n)) : ((0 : Fin (2^n)) ^^^ k) = k := by
  apply Fin.ext; rw [Fin.xor_val_of_two_pow]; simp

/-- `i ⊕ i = 0`. -/
theorem xor_self_eq (i : Fin (2^n)) : (i ^^^ i) = (0 : Fin (2^n)) := by
  apply Fin.ext; rw [Fin.xor_val_of_two_pow, Nat.xor_self]; rfl

/-- XOR by `k` is an involution: `(i ⊕ k) ⊕ k = i`. -/
theorem xor_xor_cancel (i k : Fin (2^n)) : ((i ^^^ k) ^^^ k) = i := by
  apply Fin.ext
  rw [Fin.xor_val_of_two_pow, Fin.xor_val_of_two_pow, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- XOR by a fixed `i` on the left is injective. -/
theorem xor_left_injective (i : Fin (2^n)) : Function.Injective (i ^^^ ·) := by
  intro a b h
  apply Fin.ext
  have hv : i.val ^^^ a.val = i.val ^^^ b.val := by
    have := congrArg Fin.val h
    rwa [Fin.xor_val_of_two_pow, Fin.xor_val_of_two_pow] at this
  have h2 : i.val ^^^ (i.val ^^^ a.val) = i.val ^^^ (i.val ^^^ b.val) := by rw [hv]
  rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, ← Nat.xor_assoc, Nat.xor_self,
    Nat.zero_xor] at h2

/-- XOR is an involution: `i ⊕ j = k ↔ j = i ⊕ k` on `Fin (2^n)`. -/
theorem xor_eq_iff (i j k : Fin (2^n)) : (i ^^^ j = k) ↔ (j = i ^^^ k) := by
  constructor
  · intro h; apply Fin.ext; subst h
    simp only [Fin.xor_val_of_two_pow]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro h; apply Fin.ext; subst h
    simp only [Fin.xor_val_of_two_pow]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- The product coordinate `(x·y).coord k` collapses to a single sum over `i`
    (picking `j = i ⊕ k`). -/
theorem mul_coord_single (x y : CDAlg R n) (k : Fin (2^n)) :
    (x * y).coord k =
      ∑ i, (mulCoeff n i (i ^^^ k) : R) * x.coord i * y.coord (i ^^^ k) := by
  rw [mul_coord]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single (i ^^^ k)]
  · rw [if_pos]; exact (xor_eq_iff i (i ^^^ k) k).mpr rfl
  · intro b _ hb
    rw [if_neg]; intro h; exact hb ((xor_eq_iff i b k).mp h)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Quadraticity (Cayley–Dickson square identity).**  For every `x : CDAlg ℝ n`,
    `x · x = (2 · Re x) • x − N(x) • 1`, where `Re x = x.coord 0` and
    `N x = ∑ xᵢ²`.  This is the identity span{1, x} ≅ ℂ rests on. -/
theorem cdAlg_sq_eq (x : CDAlg ℝ n) :
    x * x = (2 * x.coord 0) • x - (N x) • 1 := by
  ext k
  rw [mul_coord_single, sub_coord, smul_coord, smul_coord, one_coord, N_def]
  by_cases hk : k = 0
  · -- real coordinate: ∑ᵢ mulCoeff i i · xᵢ² = 2 x₀² − N x
    subst hk
    simp only [xor_zero_right, mul_one]
    -- LHS = ∑ᵢ mulCoeff i i · xᵢ · xᵢ ; mulCoeff i i = ±1
    rw [show (∑ i, (mulCoeff n i i : ℝ) * x.coord i * x.coord i)
          = ∑ i, (if i.val = 0 then (1:ℝ) else -1) * x.coord i * x.coord i from
        Finset.sum_congr rfl (fun i _ => by rw [mulCoeff_self]; split <;> push_cast <;> ring)]
    -- split the singleton i=0 from both sums
    rw [show (∑ i, (if i.val = 0 then (1:ℝ) else -1) * x.coord i * x.coord i)
          = ∑ i, ((if i.val = 0 then (2:ℝ) else 0) * x.coord i ^ 2
                   - x.coord i ^ 2) from
        Finset.sum_congr rfl (fun i _ => by split <;> ring)]
    rw [Finset.sum_sub_distrib]
    rw [show (∑ i, (if i.val = 0 then (2:ℝ) else 0) * x.coord i ^ 2)
          = ∑ i, (if i = 0 then (2:ℝ) * x.coord i ^ 2 else 0) from
        Finset.sum_congr rfl (fun i _ => by
          by_cases h : i = 0
          · subst h; simp
          · have hv : i.val ≠ 0 := fun hh => h (Fin.ext hh)
            rw [if_neg h, if_neg hv]; ring)]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (2^n)) (fun i => (2:ℝ) * x.coord i ^ 2)]
    simp only [Finset.mem_univ, if_true]
    ring
  · -- imaginary coordinate k ≠ 0: ∑ᵢ mulCoeff i (i⊕k) xᵢ x_{i⊕k} = 2 x₀ x_k
    rw [if_neg hk, mul_zero, sub_zero]
    -- the i=0 and i=k terms; everything else cancels pairwise
    -- ∑ᵢ f i with f i = mulCoeff i (i⊕k) xᵢ x_{i⊕k}
    -- pair i ↔ i⊕k.  Use Finset.sum over an involution.
    have hknz : (k.val) ≠ 0 := fun h => hk (Fin.ext h)
    have key : (∑ i, (mulCoeff n i (i ^^^ k) : ℝ) * x.coord i * x.coord (i ^^^ k))
                = 2 * x.coord 0 * x.coord k := by
      -- Symmetrize over the involution σ i = i ⊕ k: 2·S = ∑ (mc i (i⊕k) + mc (i⊕k) i)·xᵢ·x_{i⊕k};
      -- the antisymmetric (both-imaginary) pairs cancel, leaving i=0 and i=k.
      -- reindex i ↦ i⊕k: ∑ g i = ∑ g (i⊕k), and g(i⊕k) is the swapped summand
      have hreindex : ∀ g : Fin (2^n) → ℝ, (∑ i, g i) = ∑ i, g (i ^^^ k) := by
        intro g
        apply Finset.sum_nbij' (fun i => i ^^^ k) (fun i => i ^^^ k) <;>
          intro a _ <;>
          first
            | exact Finset.mem_univ _
            | exact xor_xor_cancel a k
            | exact congrArg g (xor_xor_cancel a k).symm
      have hsum_swap : (∑ i, (mulCoeff n i (i ^^^ k) : ℝ) * x.coord i * x.coord (i ^^^ k))
            = ∑ i, (mulCoeff n (i ^^^ k) i : ℝ) * x.coord (i ^^^ k) * x.coord i := by
        rw [hreindex (fun i => (mulCoeff n i (i ^^^ k) : ℝ) * x.coord i * x.coord (i ^^^ k))]
        exact Finset.sum_congr rfl (fun i _ => by rw [xor_xor_cancel i k])
      have h2S : (2:ℝ) * (∑ i, (mulCoeff n i (i ^^^ k) : ℝ) * x.coord i * x.coord (i ^^^ k))
            = ∑ i, ((mulCoeff n i (i ^^^ k) : ℝ) + (mulCoeff n (i ^^^ k) i : ℝ))
                      * x.coord i * x.coord (i ^^^ k) := by
        rw [two_mul]
        nth_rewrite 2 [hsum_swap]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hterm : ∀ i : Fin (2^n),
          ((mulCoeff n i (i ^^^ k) : ℝ) + (mulCoeff n (i ^^^ k) i : ℝ))
              * x.coord i * x.coord (i ^^^ k)
            = (if i = 0 then (2:ℝ) * x.coord 0 * x.coord k else 0)
              + (if i = k then (2:ℝ) * x.coord 0 * x.coord k else 0) := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0
          rw [xor_zero_left, mulCoeff_zero_left, mulCoeff_zero_right]
          rw [if_pos rfl, if_neg (fun h => hk h.symm)]
          push_cast; ring
        · by_cases hik : i = k
          · subst hik
            rw [xor_self_eq, mulCoeff_zero_left, mulCoeff_zero_right]
            rw [if_neg hi0, if_pos rfl]
            push_cast; ring
          · have hiknz : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
            have hixk_nz : (i ^^^ k).val ≠ 0 := by
              intro h
              have h0 : (i ^^^ k) = 0 := Fin.ext h
              exact hik (by rw [← xor_xor_cancel i k, h0, xor_zero_left])
            have hne : i ≠ (i ^^^ k) := by
              intro h
              -- h : i = i ⊕ k ⟹ k = 0, contradiction with hk
              apply hk
              apply xor_left_injective i
              show i ^^^ k = i ^^^ 0
              rw [xor_zero_right, ← h]
            rw [mulCoeff_antisymm n i (i ^^^ k) hiknz hixk_nz hne]
            rw [if_neg hi0, if_neg hik]
            push_cast; ring
      have hexpand : (2:ℝ) * (∑ i, (mulCoeff n i (i ^^^ k) : ℝ) * x.coord i * x.coord (i ^^^ k))
            = 2 * ((2:ℝ) * x.coord 0 * x.coord k) := by
        rw [h2S, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (2^n)) (fun _ => (2:ℝ) * x.coord 0 * x.coord k)]
        rw [Finset.sum_ite_eq' Finset.univ k (fun _ => (2:ℝ) * x.coord 0 * x.coord k)]
        simp only [Finset.mem_univ, if_true]; ring
      linarith [hexpand]
    rw [key, mul_assoc]

/-! ## 9. Completeness audit — `#print axioms` -/

#print axioms basis_expansion
#print axioms mulCoeff_four_eq_sgnTable
#print axioms mulCoeff_three_eq_fano
#print axioms e_mul_e
#print axioms mul_add_left
#print axioms mul_smul_left
#print axioms mulCoeff_self
#print axioms mulCoeff_antisymm
#print axioms cdAlg_sq_eq

end QBP.Foundations.CDAlg
