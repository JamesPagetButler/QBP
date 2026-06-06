/-
  QBP.Foundations.CDLifting
  =========================

  The multilinear lifting metalemmas for `CDAlg R n` — the keystone the
  operations-complete program (#474 / #476 / #477) consumes.  An algebra-wide law
  (associativity, alternativity, Moufang, …) holds for ALL elements iff it holds
  on all basis tuples, PROVIDED the law's defining map is multilinear.  This file
  proves that bridge once, in three arities:

    * `lift_bilinear_eq`     — 2 arguments  (powers e.g. commutator laws)
    * `lift_trilinear_eq`    — 3 arguments  (KEYSTONE; powers associativity /
                                             alternativity)
    * `lift_quadrilinear_eq` — 4 arguments  (powers the Moufang identities, PR-C1)

  and demonstrates them end-to-end:

    * `octonion_alternative`        — 𝕆 = CDAlg ℝ 3 is left- and right-alternative
                                      (basis fact `decide`d over ℤ + trilinear lift)
    * `sedenion_not_alternative`    — 𝕊 = CDAlg ℝ 4 is NOT alternative
                                      (constructed witness, coordinate ≠ 0 by norm_num)

  Formulation choice (reported for the record): the trilinearity hypotheses are
  carried as an explicit `IsTrilinear` predicate (six add/smul laws), NOT wrapped
  in Mathlib's `MultilinearMap`.  Rationale: the associator and its symmetrizations
  are bare functions `CDAlg → CDAlg → CDAlg → CDAlg`; wrapping each in a bundled
  `MultilinearMap (fun _ : Fin 3 => CDAlg R n) (CDAlg R n)` would force `Fin 3`
  tuple-plumbing (`Matrix.cons`/`Fin.cons` updates) at every use site, whereas the
  predicate form lets `simp only [assoc, mul_add_left, …]` discharge the six laws
  directly.  The lift proof itself (expand each argument via `basis_expansion`,
  push `T` through the three sums) is identical either way; the predicate keeps the
  consumer-side boilerplate minimal.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import QBP.Foundations.CDAlg

namespace QBP.Foundations.CDAlg

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ## 1. Multilinearity predicates -/

/-- `T` is `R`-bilinear: additive and `R`-homogeneous in each of its two slots. -/
structure IsBilinear (T : CDAlg R n → CDAlg R n → CDAlg R n) : Prop where
  add_left  : ∀ x x' y, T (x + x') y = T x y + T x' y
  smul_left : ∀ (r : R) x y, T (r • x) y = r • T x y
  add_right : ∀ x y y', T x (y + y') = T x y + T x y'
  smul_right: ∀ (r : R) x y, T x (r • y) = r • T x y

/-- `T` is `R`-trilinear: additive and `R`-homogeneous in each of its three slots. -/
structure IsTrilinear (T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n) : Prop where
  add_left  : ∀ x x' y z, T (x + x') y z = T x y z + T x' y z
  smul_left : ∀ (r : R) x y z, T (r • x) y z = r • T x y z
  add_mid   : ∀ x y y' z, T x (y + y') z = T x y z + T x y' z
  smul_mid  : ∀ (r : R) x y z, T x (r • y) z = r • T x y z
  add_right : ∀ x y z z', T x y (z + z') = T x y z + T x y z'
  smul_right: ∀ (r : R) x y z, T x y (r • z) = r • T x y z

/-- `T` is `R`-quadrilinear: additive and `R`-homogeneous in each of its four slots. -/
structure IsQuadrilinear (T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n) :
    Prop where
  add_1  : ∀ w w' x y z, T (w + w') x y z = T w x y z + T w' x y z
  smul_1 : ∀ (r : R) w x y z, T (r • w) x y z = r • T w x y z
  add_2  : ∀ w x x' y z, T w (x + x') y z = T w x y z + T w x' y z
  smul_2 : ∀ (r : R) w x y z, T w (r • x) y z = r • T w x y z
  add_3  : ∀ w x y y' z, T w x (y + y') z = T w x y z + T w x y' z
  smul_3 : ∀ (r : R) w x y z, T w x (r • y) z = r • T w x y z
  add_4  : ∀ w x y z z', T w x y (z + z') = T w x y z + T w x y z'
  smul_4 : ∀ (r : R) w x y z, T w x y (r • z) = r • T w x y z

/-! ## 2. Distribution over `Finset.sum` -/

theorem IsBilinear.sum_left {T : CDAlg R n → CDAlg R n → CDAlg R n} (hT : IsBilinear T)
    {ι : Type*} (s : Finset ι) (f : ι → CDAlg R n) (y : CDAlg R n) :
    T (∑ i ∈ s, f i) y = ∑ i ∈ s, T (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_left 0 0 y; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_left, ih, Finset.sum_insert ha]

theorem IsBilinear.sum_right {T : CDAlg R n → CDAlg R n → CDAlg R n} (hT : IsBilinear T)
    {ι : Type*} (s : Finset ι) (x : CDAlg R n) (f : ι → CDAlg R n) :
    T x (∑ i ∈ s, f i) = ∑ i ∈ s, T x (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_right 0 x 0; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_right, ih, Finset.sum_insert ha]

theorem IsTrilinear.sum_left {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsTrilinear T) {ι : Type*} (s : Finset ι) (f : ι → CDAlg R n) (y z : CDAlg R n) :
    T (∑ i ∈ s, f i) y z = ∑ i ∈ s, T (f i) y z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_left 0 0 y z; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_left, ih, Finset.sum_insert ha]

theorem IsTrilinear.sum_mid {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsTrilinear T) {ι : Type*} (s : Finset ι) (x : CDAlg R n) (f : ι → CDAlg R n)
    (z : CDAlg R n) :
    T x (∑ i ∈ s, f i) z = ∑ i ∈ s, T x (f i) z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_mid 0 x 0 z; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_mid, ih, Finset.sum_insert ha]

theorem IsTrilinear.sum_right {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsTrilinear T) {ι : Type*} (s : Finset ι) (x y : CDAlg R n) (f : ι → CDAlg R n) :
    T x y (∑ i ∈ s, f i) = ∑ i ∈ s, T x y (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_right 0 x y 0; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_right, ih, Finset.sum_insert ha]

theorem IsQuadrilinear.sum_1 {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsQuadrilinear T) {ι : Type*} (s : Finset ι) (f : ι → CDAlg R n) (x y z : CDAlg R n) :
    T (∑ i ∈ s, f i) x y z = ∑ i ∈ s, T (f i) x y z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_1 0 0 x y z; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_1, ih, Finset.sum_insert ha]

theorem IsQuadrilinear.sum_2 {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsQuadrilinear T) {ι : Type*} (s : Finset ι) (w : CDAlg R n) (f : ι → CDAlg R n)
    (y z : CDAlg R n) :
    T w (∑ i ∈ s, f i) y z = ∑ i ∈ s, T w (f i) y z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_2 0 w 0 y z; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_2, ih, Finset.sum_insert ha]

theorem IsQuadrilinear.sum_3 {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsQuadrilinear T) {ι : Type*} (s : Finset ι) (w x : CDAlg R n) (f : ι → CDAlg R n)
    (z : CDAlg R n) :
    T w x (∑ i ∈ s, f i) z = ∑ i ∈ s, T w x (f i) z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_3 0 w x 0 z; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_3, ih, Finset.sum_insert ha]

theorem IsQuadrilinear.sum_4 {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsQuadrilinear T) {ι : Type*} (s : Finset ι) (w x y : CDAlg R n) (f : ι → CDAlg R n) :
    T w x y (∑ i ∈ s, f i) = ∑ i ∈ s, T w x y (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (by have := hT.smul_4 0 w x y 0; simpa using this)
  | insert a s ha ih => rw [Finset.sum_insert ha, hT.add_4, ih, Finset.sum_insert ha]

/-! ## 3. The lifting metalemmas

A multilinear map vanishing on all basis tuples vanishes everywhere.  Proof:
expand each argument by `basis_expansion`, push the map through each sum, conclude
from the basis hypothesis. -/

/-- A bilinear map vanishing on all basis pairs vanishes everywhere. -/
theorem lift_bilinear_eq {T : CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsBilinear T) (hbasis : ∀ i j : Fin (2^n), T (e i) (e j) = 0)
    (x y : CDAlg R n) : T x y = 0 := by
  conv_lhs => rw [basis_expansion x, basis_expansion y]
  rw [hT.sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [hT.smul_left, hT.sum_right, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hT.smul_right, hbasis, smul_zero, smul_zero]

/-- **KEYSTONE.**  A trilinear map vanishing on all basis triples vanishes
    everywhere.  This is the bridge from `decide`-checked basis facts to
    algebra-wide laws that the entire #474 program rests on. -/
theorem lift_trilinear_eq {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsTrilinear T) (hbasis : ∀ i j k : Fin (2^n), T (e i) (e j) (e k) = 0)
    (x y z : CDAlg R n) : T x y z = 0 := by
  conv_lhs => rw [basis_expansion x, basis_expansion y, basis_expansion z]
  rw [hT.sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [hT.smul_left, hT.sum_mid, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hT.smul_mid, hT.sum_right, smul_comm, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [hT.smul_right, hbasis, smul_zero, smul_zero, smul_zero]

/-- A quadrilinear map vanishing on all basis 4-tuples vanishes everywhere.
    (Powers the Moufang identities in PR-C1.) -/
theorem lift_quadrilinear_eq {T : CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n → CDAlg R n}
    (hT : IsQuadrilinear T)
    (hbasis : ∀ i j k l : Fin (2^n), T (e i) (e j) (e k) (e l) = 0)
    (w x y z : CDAlg R n) : T w x y z = 0 := by
  conv_lhs => rw [basis_expansion w, basis_expansion x, basis_expansion y, basis_expansion z]
  rw [hT.sum_1]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [hT.smul_1, hT.sum_2, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hT.smul_2, hT.sum_3, smul_comm, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [hT.smul_3, hT.sum_4, smul_comm, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  rw [hT.smul_4, hbasis, smul_zero, smul_zero, smul_zero, smul_zero]

/-! ## 4. The associator and its trilinearity -/

/-- The associator `[x,y,z] = (x·y)·z − x·(y·z)`.  Vanishes iff `(x,y,z)` associate. -/
def assoc (x y z : CDAlg R n) : CDAlg R n := (x * y) * z - x * (y * z)

/-- The associator is `R`-trilinear (from bilinearity of `*`). -/
theorem assoc_trilinear : IsTrilinear (assoc : CDAlg R n → _ → _ → _) where
  add_left x x' y z := by simp only [assoc, mul_add_left]; abel
  smul_left r x y z := by simp only [assoc, mul_smul_left, smul_sub]
  add_mid x y y' z := by simp only [assoc, mul_add_left, mul_add_right]; abel
  smul_mid r x y z := by simp only [assoc, mul_smul_left, mul_smul_right, smul_sub]
  add_right x y z z' := by simp only [assoc, mul_add_right]; abel
  smul_right r x y z := by simp only [assoc, mul_smul_right, smul_sub]

/-- The associator on basis elements: `[eᵢ, e_j, e_k] = assocCoeffZ • e_{i⊕j⊕k}`,
    where the integer coefficient is the basis associator. -/
def assocCoeffZ (n : ℕ) (i j k : Fin (2^n)) : Int :=
  mulCoeff n i j * mulCoeff n (i ^^^ j) k - mulCoeff n j k * mulCoeff n i (j ^^^ k)

theorem assoc_e (i j k : Fin (2^n)) :
    (assoc (e i) (e j) (e k) : CDAlg R n)
      = (assocCoeffZ n i j k : R) • e (i ^^^ j ^^^ k) := by
  have hxor : (i ^^^ j ^^^ k : Fin (2^n)) = (i ^^^ (j ^^^ k) : Fin (2^n)) := by
    apply Fin.ext
    simp only [Fin.xor_val_of_two_pow, Nat.xor_assoc]
  simp only [assoc, e_mul_e, mul_smul_left, mul_smul_right, smul_smul]
  rw [assocCoeffZ, hxor]
  push_cast
  rw [sub_smul, mul_comm (mulCoeff n j k : R)]

/-! ## 5. Octonion alternativity payoff (𝕆 = CDAlg ℝ 3) -/

/-- Polarized-left-alternativity map `[x,y,z] + [y,x,z]`, trilinear. -/
def laMap (x y z : CDAlg R n) : CDAlg R n := assoc x y z + assoc y x z

theorem laMap_trilinear : IsTrilinear (laMap : CDAlg R n → _ → _ → _) where
  add_left x x' y z := by
    simp only [laMap, assoc_trilinear.add_left, assoc_trilinear.add_mid]; abel
  smul_left r x y z := by
    simp only [laMap, assoc_trilinear.smul_left, assoc_trilinear.smul_mid, smul_add]
  add_mid x y y' z := by
    simp only [laMap, assoc_trilinear.add_mid, assoc_trilinear.add_left]; abel
  smul_mid r x y z := by
    simp only [laMap, assoc_trilinear.smul_mid, assoc_trilinear.smul_left, smul_add]
  add_right x y z z' := by
    simp only [laMap, assoc_trilinear.add_right]; abel
  smul_right r x y z := by
    simp only [laMap, assoc_trilinear.smul_right, smul_add]

/-- Polarized-right-alternativity map `[x,y,z] + [x,z,y]`, trilinear. -/
def raMap (x y z : CDAlg R n) : CDAlg R n := assoc x y z + assoc x z y

theorem raMap_trilinear : IsTrilinear (raMap : CDAlg R n → _ → _ → _) where
  add_left x x' y z := by
    simp only [raMap, assoc_trilinear.add_left]; abel
  smul_left r x y z := by
    simp only [raMap, assoc_trilinear.smul_left, smul_add]
  add_mid x y y' z := by
    simp only [raMap, assoc_trilinear.add_mid, assoc_trilinear.add_right]; abel
  smul_mid r x y z := by
    simp only [raMap, assoc_trilinear.smul_mid, assoc_trilinear.smul_right, smul_add]
  add_right x y z z' := by
    simp only [raMap, assoc_trilinear.add_right, assoc_trilinear.add_mid]; abel
  smul_right r x y z := by
    simp only [raMap, assoc_trilinear.smul_right, assoc_trilinear.smul_mid, smul_add]

/-- **Integer basis fact (kernel `decide`).**  The octonion associator is
    left-alternating on all 8³ = 512 basis triples. -/
theorem octonion_assocCoeffZ_left_alt :
    ∀ i j k : Fin (2^3), assocCoeffZ 3 i j k + assocCoeffZ 3 j i k = 0 := by decide

/-- **Integer basis fact (kernel `decide`).**  The octonion associator is
    right-alternating on all basis triples. -/
theorem octonion_assocCoeffZ_right_alt :
    ∀ i j k : Fin (2^3), assocCoeffZ 3 i j k + assocCoeffZ 3 i k j = 0 := by decide

theorem octonion_laMap_basis (i j k : Fin (2^3)) :
    (laMap (e i) (e j) (e k) : CDAlg ℝ 3) = 0 := by
  rw [laMap, assoc_e, assoc_e]
  have h1 : (j ^^^ i ^^^ k : Fin (2^3)) = (i ^^^ j ^^^ k : Fin (2^3)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; rw [Nat.xor_comm i.val j.val]
  rw [h1, ← add_smul]
  rw [show ((assocCoeffZ 3 i j k : ℝ) + (assocCoeffZ 3 j i k : ℝ))
        = (((assocCoeffZ 3 i j k + assocCoeffZ 3 j i k : Int)) : ℝ) by push_cast; ring,
     octonion_assocCoeffZ_left_alt i j k]
  simp

theorem octonion_raMap_basis (i j k : Fin (2^3)) :
    (raMap (e i) (e j) (e k) : CDAlg ℝ 3) = 0 := by
  rw [raMap, assoc_e, assoc_e]
  have h1 : (i ^^^ k ^^^ j : Fin (2^3)) = (i ^^^ j ^^^ k : Fin (2^3)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm k.val j.val]
  rw [h1, ← add_smul]
  rw [show ((assocCoeffZ 3 i j k : ℝ) + (assocCoeffZ 3 i k j : ℝ))
        = (((assocCoeffZ 3 i j k + assocCoeffZ 3 i k j : Int)) : ℝ) by push_cast; ring,
     octonion_assocCoeffZ_right_alt i j k]
  simp

/-- **Octonion left-alternativity, polarized form** (lifted from the basis fact):
    for all `x y z : CDAlg ℝ 3`, `[x,y,z] + [y,x,z] = 0`. -/
theorem octonion_left_alternative_polarized (x y z : CDAlg ℝ 3) :
    assoc x y z + assoc y x z = 0 :=
  lift_trilinear_eq laMap_trilinear octonion_laMap_basis x y z

/-- **Octonion right-alternativity, polarized form** (lifted): `[x,y,z] + [x,z,y] = 0`. -/
theorem octonion_right_alternative_polarized (x y z : CDAlg ℝ 3) :
    assoc x y z + assoc x z y = 0 :=
  lift_trilinear_eq raMap_trilinear octonion_raMap_basis x y z

theorem assoc_diag_left (x y : CDAlg ℝ 3) : assoc x x y = 0 := by
  have h2 : (2 : ℝ) • assoc x x y = 0 := by
    rw [two_smul]; exact octonion_left_alternative_polarized x x y
  rcases smul_eq_zero.mp h2 with hz | hz
  · exact absurd hz two_ne_zero
  · exact hz

theorem assoc_diag_right (x y : CDAlg ℝ 3) : assoc x y y = 0 := by
  have h2 : (2 : ℝ) • assoc x y y = 0 := by
    rw [two_smul]; exact octonion_right_alternative_polarized x y y
  rcases smul_eq_zero.mp h2 with hz | hz
  · exact absurd hz two_ne_zero
  · exact hz

/-- **PAYOFF: octonion alternativity.**  𝕆 = `CDAlg ℝ 3` is left- and
    right-alternative: for all `x y`, `(x·x)·y = x·(x·y)` and `(x·y)·y = x·(y·y)`.
    Proven via the trilinear lift (`lift_trilinear_eq`) + the basis facts
    `octonion_assocCoeffZ_{left,right}_alt` — the basis-vs-algebra-wide honesty gap
    closed by the keystone, not asserted. -/
theorem octonion_alternative (x y : CDAlg ℝ 3) :
    (x * x) * y = x * (x * y) ∧ (x * y) * y = x * (y * y) := by
  refine ⟨?_, ?_⟩
  · have := assoc_diag_left x y; rwa [assoc, sub_eq_zero] at this
  · have := assoc_diag_right x y; rwa [assoc, sub_eq_zero] at this

/-! ## 6. Sedenion non-alternativity counterexample (𝕊 = CDAlg ℝ 4)

A constructed witness: `x = e₁ + e₁₀`, `y = e₄`.  The associator `[x, x, y]` has a
nonzero coordinate (index 15), so `(x·x)·y ≠ x·(x·y)`.  The nonzeroness is by
`norm_num` on that ℝ-coordinate — NOT a named witness in a comment. -/

/-- The sedenion witness `x = e₁ + e₁₀`. -/
def sedWitX : CDAlg ℝ 4 := e ⟨1, by norm_num⟩ + e ⟨10, by norm_num⟩
/-- The sedenion witness `y = e₄`. -/
def sedWitY : CDAlg ℝ 4 := e ⟨4, by norm_num⟩

/-- The integer associator coefficient `assocCoeffZ 4 1 10 4 = 2 ≠ 0` (kernel
    `decide`): this is the seed of the sedenion non-alternativity witness. -/
theorem sed_assocCoeffZ_witness :
    assocCoeffZ 4 ⟨1, by norm_num⟩ ⟨10, by norm_num⟩ ⟨4, by norm_num⟩ = 2 := by decide

/-- **PAYOFF: sedenions are NOT alternative.**  𝕊 = `CDAlg ℝ 4` fails left
    alternativity: there exist `x y` with `(x·x)·y ≠ x·(x·y)`.  Witnessed by
    `x = e₁ + e₁₀`, `y = e₄`, whose associator has coordinate 2 (≠ 0) at index 15. -/
theorem sedenion_not_alternative :
    ∃ x y : CDAlg ℝ 4, (x * x) * y ≠ x * (x * y) := by
  refine ⟨sedWitX, sedWitY, ?_⟩
  intro hcontra
  -- the associator [x,x,y] = (x*x)*y - x*(x*y) would then be 0
  have hzero : assoc sedWitX sedWitX sedWitY = 0 := by
    rw [assoc, hcontra, sub_self]
  -- but its coordinate at index 15 is 2 ≠ 0.  Expand by trilinearity into the four
  -- basis associators, each evaluated by `assoc_e`.
  set i1 : Fin (2^4) := ⟨1, by norm_num⟩
  set i10 : Fin (2^4) := ⟨10, by norm_num⟩
  set i4 : Fin (2^4) := ⟨4, by norm_num⟩
  have hexp : assoc sedWitX sedWitX sedWitY
      = assoc (e i1) (e i1) (e i4) + assoc (e i1) (e i10) (e i4)
        + (assoc (e i10) (e i1) (e i4) + assoc (e i10) (e i10) (e i4)) := by
    rw [sedWitX, sedWitY, assoc_trilinear.add_left, assoc_trilinear.add_mid,
      assoc_trilinear.add_mid]
  have h15 : (⟨15, by norm_num⟩ : Fin (2^4)) = i1 ^^^ i10 ^^^ i4 := by decide
  have hcoord : (assoc sedWitX sedWitX sedWitY).coord ⟨15, by norm_num⟩ = 2 := by
    rw [hexp]
    simp only [assoc_e, add_coord, smul_coord, e_coord]
    have e1 : assocCoeffZ 4 i1 i1 i4 = 0 := by decide
    have e2 : assocCoeffZ 4 i1 i10 i4 = 2 := by decide
    have e3 : assocCoeffZ 4 i10 i1 i4 = 0 := by decide
    have e4 : assocCoeffZ 4 i10 i10 i4 = 0 := by decide
    have x1 : (i1 ^^^ i1 ^^^ i4 : Fin (2^4)) = i4 := by decide
    have x2 : (i1 ^^^ i10 ^^^ i4 : Fin (2^4)) = ⟨15, by norm_num⟩ := by decide
    have x3 : (i10 ^^^ i1 ^^^ i4 : Fin (2^4)) = ⟨15, by norm_num⟩ := by decide
    have x4 : (i10 ^^^ i10 ^^^ i4 : Fin (2^4)) = i4 := by decide
    rw [e1, e2, e3, e4, x1, x2, x3, x4]
    norm_num [i4]
  rw [hzero] at hcoord
  simp only [zero_coord] at hcoord
  norm_num at hcoord

/-! ## 7. Completeness audit — `#print axioms` -/

#print axioms lift_bilinear_eq
#print axioms lift_trilinear_eq
#print axioms lift_quadrilinear_eq
#print axioms assoc_trilinear
#print axioms octonion_alternative
#print axioms octonion_left_alternative_polarized
#print axioms octonion_right_alternative_polarized
#print axioms sedenion_not_alternative

end QBP.Foundations.CDAlg
