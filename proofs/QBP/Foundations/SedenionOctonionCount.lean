/-
  QBP.Foundations.SedenionOctonionCount
  =====================================

  Task O1a (crystallisation-conjecture E-rung threshold ladder):
  determine how many of the 15 hyperplane subalgebras of the standard
  Cayley–Dickson sedenion frame are isomorphic to the octonions 𝕆.

  Result (kernel-checked below): **k = 8**, NOT 15.

  -- Mathematical setup ----------------------------------------------------
  In the standard Cayley–Dickson basis e₀..e₁₅ (e₀ = 1) the unit products
  satisfy eₐ·e_b = sgn(a,b)·e_{a XOR b}, where the integer sign table
  `sgnTable` below is generated from the genuine Cayley–Dickson doubling
  recursion (ℝ → ℂ → ℍ → 𝕆 → 𝕊), formula
      (a,b)(c,d) = (a·c − conj(d)·b,  d·a + b·conj(c)),
  NOT guessed from memory. (Generator: see the task's Python cross-check;
  XOR-closure eₐ·e_b ∈ ±e_{a⊕b} is a *theorem* of that recursion, used here
  as the encoding — every sign is the actual doubled value.)

  The 15 nonzero indices 1..15 are the 15 points of PG(3,2) ≅ F₂⁴\{0}.
  PG(3,2) has 15 hyperplanes (3-dim F₂-subspaces); a hyperplane is the set
  Hₙ = { x ∈ {1..15} : ⟨n,x⟩ = 0 } for a nonzero "normal" n ∈ {1..15},
  where ⟨n,x⟩ = parity(n AND x). Each Hₙ has 7 elements and is automatically
  XOR-closed, so {0} ∪ Hₙ spans an 8-dimensional multiplication-closed
  subalgebra of 𝕊.

  -- The decidable criterion ----------------------------------------------
  An 8-dim Cayley–Dickson subalgebra here is ≅ 𝕆 iff it is *alternative*
  (Hurwitz/Zorn: a finite-dimensional alternative real algebra carrying the
  inherited positive-definite norm is a normed division algebra, hence ℝ, ℂ,
  ℍ or 𝕆; an 8-dim one is 𝕆 — this classification step is cited, NOT
  re-proved, in Lean). For *unit basis* elements alternativity is the purely
  combinatorial statement that the associator
      [a,b,c] := (eₐ·e_b)·e_c − eₐ·(e_b·e_c)
  is **alternating** (totally antisymmetric) in (a,b,c). Since for units both
  (eₐ·e_b)·e_c and eₐ·(e_b·e_c) land on the single index a⊕b⊕c, the
  associator is the scalar
      assocCoeff a b c
        = sgn a b · sgn (a⊕b) c  −  sgn b c · sgn a (b⊕c)
  times e_{a⊕b⊕c}, and "alternating" reduces to swap-antisymmetry:
      assocCoeff a b c = − assocCoeff b a c   (swap first two)
      assocCoeff a b c = − assocCoeff a c b   (swap last two).
  (The vanishing-on-repeats laws [a,a,c]=0, [a,b,b]=0 hold for ALL 15
  hyperplanes; the *discriminating* content is the antisymmetry above.)

  `isAlternative H` checks this for all basis triples drawn from the
  8-element index set {0} ∪ H. The count of hyperplanes satisfying it is 8.

  Independent cross-check (also formalized): each of the 7 FAILING
  hyperplanes carries an explicit **zero divisor** — a constructed pair of
  nonzero subalgebra elements with vanishing product (witnessed as concrete
  Lean terms, product = 0 by `decide`), confirming those 7 are not division
  algebras and hence not 𝕆.

  Lean file status: COMPLETE (zero sorry, zero native_decide, zero vacuous
  True). #print axioms audited at the bottom.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace QBP.Foundations.SedenionOctonionCount

/-! ## 1. The Cayley–Dickson sedenion sign table -/

/-- `sgnTable a b` is the sign s ∈ {−1, +1} in `eₐ · e_b = s · e_{a XOR b}`,
    for the standard Cayley–Dickson sedenions (ℝ→ℂ→ℍ→𝕆→𝕊). Generated from the
    doubling recursion `(a,b)(c,d) = (a c − conj(d) b, d a + b conj(c))`;
    every entry is the actual doubled value, not a guessed table. -/
def sgnTable : Fin 16 → Fin 16 → Int :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1],
    ![1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1],
    ![1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1],
    ![1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1],
    ![1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1],
    ![1, 1, 1, -1, -1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1],
    ![1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1],
    ![1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1],
    ![1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, 1],
    ![1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1],
    ![1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1],
    ![1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1],
    ![1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1],
    ![1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1]]

/-- Sign accessor. -/
def sgn (a b : Fin 16) : Int := sgnTable a b

/-- XOR of two `Fin 16` indices (= product index, since eₐe_b ∝ e_{a⊕b}).
    Uses the core `Xor (Fin (2^4))` instance (`Fin 16 = Fin (2^4)`); the
    bound `a ⊕ b < 16` is `Nat.xor_lt_two_pow` discharged by that instance. -/
def ixor (a b : Fin 16) : Fin 16 := a ^^^ b

/-! ## 2. The unit-element associator coefficient -/

/-- The scalar coefficient of the associator `[eₐ,e_b,e_c]` on `e_{a⊕b⊕c}`:
    `(eₐ e_b) e_c − eₐ (e_b e_c)` evaluates to `assocCoeff a b c · e_{a⊕b⊕c}`. -/
def assocCoeff (a b c : Fin 16) : Int :=
  sgn a b * sgn (ixor a b) c - sgn b c * sgn a (ixor b c)

/-! ## 3. Hyperplanes of PG(3,2) and the alternativity predicate -/

/-- The 8 index sets `{0} ∪ Hₙ` (n = 1..15 read as a normal vector), where
    `Hₙ = { x ∈ 1..15 : parity(n AND x) = 0 }`. Each is 8 indices, XOR-closed,
    spanning an 8-dim subalgebra. (Generated from `parity(n AND x)`.) -/
def hyperIdx : Fin 15 → List (Fin 16)
  | ⟨0, _⟩  => [0, 2, 4, 6, 8, 10, 12, 14]   -- normal 1
  | ⟨1, _⟩  => [0, 1, 4, 5, 8, 9, 12, 13]    -- normal 2
  | ⟨2, _⟩  => [0, 3, 4, 7, 8, 11, 12, 15]   -- normal 3
  | ⟨3, _⟩  => [0, 1, 2, 3, 8, 9, 10, 11]    -- normal 4
  | ⟨4, _⟩  => [0, 2, 5, 7, 8, 10, 13, 15]   -- normal 5
  | ⟨5, _⟩  => [0, 1, 6, 7, 8, 9, 14, 15]    -- normal 6
  | ⟨6, _⟩  => [0, 3, 5, 6, 8, 11, 13, 14]   -- normal 7
  | ⟨7, _⟩  => [0, 1, 2, 3, 4, 5, 6, 7]      -- normal 8
  | ⟨8, _⟩  => [0, 2, 4, 6, 9, 11, 13, 15]   -- normal 9
  | ⟨9, _⟩  => [0, 1, 4, 5, 10, 11, 14, 15]  -- normal 10
  | ⟨10, _⟩ => [0, 3, 4, 7, 9, 10, 13, 14]   -- normal 11
  | ⟨11, _⟩ => [0, 1, 2, 3, 12, 13, 14, 15]  -- normal 12
  | ⟨12, _⟩ => [0, 2, 5, 7, 9, 11, 12, 14]   -- normal 13
  | ⟨13, _⟩ => [0, 1, 6, 7, 10, 11, 12, 13]  -- normal 14
  | ⟨14, _⟩ => [0, 3, 5, 6, 9, 10, 12, 15]   -- normal 15

/-- Alternativity of the 8-dim subalgebra indexed by `H` (a basis-index list),
    expressed on basis triples: the associator coefficient is antisymmetric
    under swapping the first two and the last two arguments (which generates
    full S₃ antisymmetry, i.e. "alternating"). For unit basis elements this is
    exactly alternativity of the subalgebra. -/
def isAlternative (H : List (Fin 16)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H,
    assocCoeff a b c = - assocCoeff b a c ∧
    assocCoeff a b c = - assocCoeff a c b

instance (H : List (Fin 16)) : Decidable (isAlternative H) := by
  unfold isAlternative; infer_instance

/-- The number of the 15 hyperplanes whose subalgebra is alternative.
    (Each such 8-dim alternative subalgebra is ≅ 𝕆 by Hurwitz/Zorn — cited,
    not proved in Lean; this identifier names only the kernel-checked fact,
    the alternativity count.) -/
def alternativeHyperplaneCount : Nat :=
  (List.finRange 15).countP (fun n => decide (isAlternative (hyperIdx n)))

/-! ## 4. Main results -/

/-- **Main theorem.** Exactly 8 of the 15 hyperplane subalgebras of the
    Cayley–Dickson sedenion frame are alternative. (Each such 8-dim alternative
    subalgebra is ≅ 𝕆 by Hurwitz/Zorn, cited not proved in Lean.) So `k = 8`,
    not 15: the threshold-ladder factor `ln k` uses `k = 8`. -/
theorem alternative_hyperplane_count_eq_eight : alternativeHyperplaneCount = 8 := by
  decide

/-- The 8 PASSING hyperplanes are exactly the normals 1..8 (`Fin 15` indices
    0..7): these subalgebras are alternative. -/
theorem alternative_passes :
    ∀ n : Fin 15, n.val < 8 → isAlternative (hyperIdx n) := by
  decide

/-- The 7 FAILING hyperplanes are exactly the normals 9..15 (`Fin 15` indices
    8..14): these subalgebras are NOT alternative. -/
theorem alternative_fails :
    ∀ n : Fin 15, 8 ≤ n.val → ¬ isAlternative (hyperIdx n) := by
  decide

/-! ## 5. Witnessed zero divisors for the 7 failing hyperplanes

    Each failing subalgebra is shown to contain a genuine zero divisor: a pair
    of nonzero elements `x, y` with `x · y = 0`. Elements are encoded sparsely
    as `List (Int × Fin 16)` (coefficient, basis index). Multiplication uses
    the same sign table; the product's coefficient on each index k is computed
    and shown to vanish. This independently confirms (no alternativity used)
    that these 7 are not division algebras, hence not 𝕆. -/

/-- A sparse algebra element: list of (coefficient, basis-index) terms. -/
abbrev Elt := List (Int × Fin 16)

/-- Coefficient of the product `x · y` on basis index `k`:
    sum over term pairs `(c,i),(d,j)` with `i⊕j = k` of `c·d·sgn i j`. -/
def prodCoeff (x y : Elt) (k : Fin 16) : Int :=
  (x.flatMap (fun ti => y.map (fun tj =>
      if ixor ti.2 tj.2 = k then ti.1 * tj.1 * sgn ti.2 tj.2 else 0))).sum

/-- `x · y = 0` (as algebra elements): all product coefficients vanish. -/
def prodIsZero (x y : Elt) : Prop := ∀ k : Fin 16, prodCoeff x y k = 0

instance (x y : Elt) : Decidable (prodIsZero x y) := by
  unfold prodIsZero; infer_instance

/-- A `nonzero` certificate: a specific index where the element's coefficient
    is nonzero. -/
def eltNonzeroAt (x : Elt) (k : Fin 16) : Prop :=
  (x.map (fun ti => if ti.2 = k then ti.1 else 0)).sum ≠ 0

instance (x : Elt) (k : Fin 16) : Decidable (eltNonzeroAt x k) := by
  unfold eltNonzeroAt; infer_instance

-- The 7 witnesses (x in {0}∪Hₙ, y in {0}∪Hₙ, both nonzero, x·y = 0):

/-- normal 9: x = e₂ + e₉, y = e₄ + e₁₅. -/
def zd9_x : Elt := [(1, 2), (1, 9)]
def zd9_y : Elt := [(1, 4), (1, 15)]
/-- normal 10: x = e₁ + e₁₀, y = e₄ − e₁₅. -/
def zd10_x : Elt := [(1, 1), (1, 10)]
def zd10_y : Elt := [(1, 4), (-1, 15)]
/-- normal 11: x = e₃ + e₉, y = e₄ − e₁₄. -/
def zd11_x : Elt := [(1, 3), (1, 9)]
def zd11_y : Elt := [(1, 4), (-1, 14)]
/-- normal 12: x = e₁ + e₁₂, y = e₂ + e₁₅. -/
def zd12_x : Elt := [(1, 1), (1, 12)]
def zd12_y : Elt := [(1, 2), (1, 15)]
/-- normal 13: x = e₂ + e₉, y = e₅ − e₁₄. -/
def zd13_x : Elt := [(1, 2), (1, 9)]
def zd13_y : Elt := [(1, 5), (-1, 14)]
/-- normal 14: x = e₁ + e₁₀, y = e₆ − e₁₃. -/
def zd14_x : Elt := [(1, 1), (1, 10)]
def zd14_y : Elt := [(1, 6), (-1, 13)]
/-- normal 15: x = e₃ + e₉, y = e₅ − e₁₅. -/
def zd15_x : Elt := [(1, 3), (1, 9)]
def zd15_y : Elt := [(1, 5), (-1, 15)]

/-- **Zero divisors in each of the 7 failing hyperplanes.** For each failing
    normal n ∈ {9..15}, `x` and `y` are nonzero (witnessed at an explicit
    index) yet `x · y = 0`. This is the constructed-witness confirmation that
    these subalgebras are not division algebras (hence ≠ 𝕆). -/
theorem zero_divisor_normal9 :
    eltNonzeroAt zd9_x 2 ∧ eltNonzeroAt zd9_y 4 ∧ prodIsZero zd9_x zd9_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem zero_divisor_normal10 :
    eltNonzeroAt zd10_x 1 ∧ eltNonzeroAt zd10_y 4 ∧ prodIsZero zd10_x zd10_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem zero_divisor_normal11 :
    eltNonzeroAt zd11_x 3 ∧ eltNonzeroAt zd11_y 4 ∧ prodIsZero zd11_x zd11_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem zero_divisor_normal12 :
    eltNonzeroAt zd12_x 1 ∧ eltNonzeroAt zd12_y 2 ∧ prodIsZero zd12_x zd12_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem zero_divisor_normal13 :
    eltNonzeroAt zd13_x 2 ∧ eltNonzeroAt zd13_y 5 ∧ prodIsZero zd13_x zd13_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem zero_divisor_normal14 :
    eltNonzeroAt zd14_x 1 ∧ eltNonzeroAt zd14_y 6 ∧ prodIsZero zd14_x zd14_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem zero_divisor_normal15 :
    eltNonzeroAt zd15_x 3 ∧ eltNonzeroAt zd15_y 5 ∧ prodIsZero zd15_x zd15_y := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 6. Consistency: alternativity-criterion count = zero-divisor-free count

    The 8 alternative hyperplanes (normals 1..8) and the 7 with witnessed zero
    divisors (normals 9..15) partition the 15 — two independent criteria agree,
    giving `k = 8` both ways. The witnesses above are exactly the failing set
    from `alternative_fails`. -/

/-- The passing set has size 8 and the failing set has size 7, partitioning 15. -/
theorem partition_8_7 :
    (List.finRange 15).countP (fun n => decide (isAlternative (hyperIdx n))) = 8 ∧
    (List.finRange 15).countP (fun n => decide (¬ isAlternative (hyperIdx n))) = 7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## 7. Completeness audit — `#print axioms` on every main theorem

    Each must depend only on the three standard axioms
    `{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no native/reduceBool
    axiom). Reported in the build log. -/

#print axioms alternative_hyperplane_count_eq_eight
#print axioms alternative_passes
#print axioms alternative_fails
#print axioms partition_8_7
#print axioms zero_divisor_normal9
#print axioms zero_divisor_normal10
#print axioms zero_divisor_normal11
#print axioms zero_divisor_normal12
#print axioms zero_divisor_normal13
#print axioms zero_divisor_normal14
#print axioms zero_divisor_normal15

end QBP.Foundations.SedenionOctonionCount
