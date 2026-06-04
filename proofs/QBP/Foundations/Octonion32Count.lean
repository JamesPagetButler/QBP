/-
  QBP.Foundations.Octonion32Count
  ================================

  Tasks D1 + D3 (crystallisation-conjecture O2-invariant debate,
  `docs/foundations/debate-O2-invariant-2026-06-03.md`, obligations D1/D3).

  Setting: the 32-dimensional Cayley–Dickson algebra 𝕋 = CD(𝕊), the double of
  the sedenions, basis e₀..e₃₁ with unit products eₐ·e_b = ±e_{a⊕b}. The 155
  candidate 8-dim frame subalgebras are the 3-dim GF(2)-subspaces of F₂⁵∖{0}.
  As in O1a, such an 8-dim subalgebra is an octonion copy iff it is *alternative*
  on basis triples (Hurwitz/Zorn classification of finite-dim normed division
  algebras; cited, not re-proved here — same caveat as O1a).

  Results (all kernel-checked below; independently Python-verified against the
  genuine CD doubling recursion (a,b)(c,d) = (ac − d*b, da + bc*)):

  • D3 — `alternative_subspace_count_32_eq_fifty`: exactly **50** of the 155 are
    alternative 8-dim subalgebras (≅ 𝕆 by Hurwitz/Zorn, cited not proved in
    Lean), split **8 + 42** (`base_plus_crossing_eq_fifty`): 8 lie inside the
    base sedenion (all indices < 16; these are the O1a result restated in 𝕋),
    42 cross into the doubled half.

  • `base_copies_persist`: each of the 8 passing 𝕊-hyperplane subalgebras from
    O1a remains alternative as a subalgebra of 𝕋 (subalgebra-persistence witness
    k(5) ≥ k(4)).

  • `all_sedenion_lines_associative`: all 35 GF(2)-lines of the 𝕊 frame (indices
    1..15) span associative — i.e. quaternionic — subalgebras.

  • D1 — `crossing_pass_iff_discriminator`: a crossing candidate (determined by a
    pair (L, c): L a line of the sedenion, c a coset rep of span₄(L)) is
    alternative **iff** the closed predicate `predPass L c` holds:
        PASS(L,c) ⟺ c ∈ span₄(L)                        (the canonical double)
                   OR (L ⊂ {1..7} AND c ∈ {8⊕v : v∈{1..7}∖span₄(L)})  (twisted).

  • `forty_two_split`: passing crossing candidates number 42 = 35 + 7, the two
    clauses of the predicate (35 canonical, one per line; +7, one extra coset
    per base-octonion Fano line).

  Every sign in `sgnTable` is the actual doubled value from the CD recursion
  (the 16×16 sub-block reproduces the kernel-checked O1a table exactly; verified
  in the Python cross-check). XOR-closure eₐe_b ∈ ±e_{a⊕b} is a theorem of that
  recursion, used here as the encoding.

  Status: zero sorry, zero native_decide, zero vacuous True. `#print axioms`
  audited at the bottom.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace QBP.Foundations.Octonion32Count

/-! ## 1. The 32-dim Cayley–Dickson sign table (CD double of the sedenions) -/

/-- `sgnTable a b` is the sign s ∈ {−1,+1} in `eₐ·e_b = s·e_{a⊕b}` for the
    32-dim algebra 𝕋 = CD(𝕊). Generated from the genuine doubling recursion
    `(a,b)(c,d) = (ac − conj(d)b, da + b·conj(c))`; the 16×16 sub-block equals
    the kernel-checked O1a sedenion table. -/
def sgnTable : Fin 32 → Fin 32 → Int :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1],
    ![1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1],
    ![1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1],
    ![1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
    ![1, 1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1],
    ![1, 1, 1, -1, -1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1],
    ![1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1],
    ![1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, 1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1],
    ![1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1],
    ![1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1],
    ![1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1],
    ![1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1],
    ![1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1],
    ![1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1],
    ![1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1],
    ![1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1],
    ![1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1],
    ![1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
    ![1, -1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1],
    ![1, -1, -1, 1, 1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1],
    ![1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1],
    ![1, -1, 1, -1, 1, -1, -1, 1, 1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1],
    ![1, -1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1],
    ![1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1],
    ![1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1],
    ![1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1],
    ![1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1],
    ![1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1]]
/-- Sign accessor. -/
def sgn (a b : Fin 32) : Int := sgnTable a b

/-- XOR of two `Fin 32` indices (= product index, since eₐe_b ∝ e_{a⊕b}). -/
def ixor (a b : Fin 32) : Fin 32 := a ^^^ b

/-! ## 2. Associator coefficient and the alternativity / associativity predicates -/

/-- Scalar coefficient of the associator `[eₐ,e_b,e_c]` on `e_{a⊕b⊕c}`:
    `(eₐe_b)e_c − eₐ(e_be_c) = assocCoeff a b c · e_{a⊕b⊕c}`. -/
def assocCoeff (a b c : Fin 32) : Int :=
  sgn a b * sgn (ixor a b) c - sgn b c * sgn a (ixor b c)

/-- Alternativity of the subalgebra spanned by index list `H` (with the unit
    `e₀` adjoined): on basis triples the associator coefficient is antisymmetric
    under swapping the first two and the last two arguments (generating full S₃
    antisymmetry = "alternating"). Same criterion as O1a. -/
def isAlternative (H : List (Fin 32)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H,
    assocCoeff a b c = - assocCoeff b a c ∧
    assocCoeff a b c = - assocCoeff a c b

instance (H : List (Fin 32)) : Decidable (isAlternative H) := by
  unfold isAlternative; infer_instance

/-- Associativity of the subalgebra spanned by index list `H` (with `e₀`
    adjoined): every basis-triple associator coefficient vanishes. -/
def isAssociative (H : List (Fin 32)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, assocCoeff a b c = 0

instance (H : List (Fin 32)) : Decidable (isAssociative H) := by
  unfold isAssociative; infer_instance

/-- Adjoin the unit index `e₀` to a list of imaginary basis indices. -/
def withUnit (H : List (Fin 32)) : List (Fin 32) := 0 :: H

/-! ## 3. The 155 candidate 8-dim frame subalgebras and the 35 sedenion lines -/

/-- The 155 candidate 8-dim frame subalgebras: the 3-dim GF(2)-subspaces of
    F₂⁵∖{0}, each given by its 7 nonzero basis indices (the unit e₀ is adjoined
    via `withUnit`). Enumerated from the GF(2) subspace structure. -/
def subspaces : List (List (Fin 32)) :=
  [[1, 2, 3, 4, 5, 6, 7],
   [1, 2, 3, 8, 9, 10, 11],
   [1, 2, 3, 12, 13, 14, 15],
   [1, 2, 3, 16, 17, 18, 19],
   [1, 2, 3, 20, 21, 22, 23],
   [1, 2, 3, 24, 25, 26, 27],
   [1, 2, 3, 28, 29, 30, 31],
   [1, 4, 5, 8, 9, 12, 13],
   [1, 4, 5, 10, 11, 14, 15],
   [1, 4, 5, 16, 17, 20, 21],
   [1, 4, 5, 18, 19, 22, 23],
   [1, 4, 5, 24, 25, 28, 29],
   [1, 4, 5, 26, 27, 30, 31],
   [1, 6, 7, 8, 9, 14, 15],
   [1, 6, 7, 10, 11, 12, 13],
   [1, 6, 7, 16, 17, 22, 23],
   [1, 6, 7, 18, 19, 20, 21],
   [1, 6, 7, 24, 25, 30, 31],
   [1, 6, 7, 26, 27, 28, 29],
   [1, 8, 9, 16, 17, 24, 25],
   [1, 8, 9, 18, 19, 26, 27],
   [1, 8, 9, 20, 21, 28, 29],
   [1, 8, 9, 22, 23, 30, 31],
   [1, 10, 11, 16, 17, 26, 27],
   [1, 10, 11, 18, 19, 24, 25],
   [1, 10, 11, 20, 21, 30, 31],
   [1, 10, 11, 22, 23, 28, 29],
   [1, 12, 13, 16, 17, 28, 29],
   [1, 12, 13, 18, 19, 30, 31],
   [1, 12, 13, 20, 21, 24, 25],
   [1, 12, 13, 22, 23, 26, 27],
   [1, 14, 15, 16, 17, 30, 31],
   [1, 14, 15, 18, 19, 28, 29],
   [1, 14, 15, 20, 21, 26, 27],
   [1, 14, 15, 22, 23, 24, 25],
   [2, 4, 6, 8, 10, 12, 14],
   [2, 4, 6, 9, 11, 13, 15],
   [2, 4, 6, 16, 18, 20, 22],
   [2, 4, 6, 17, 19, 21, 23],
   [2, 4, 6, 24, 26, 28, 30],
   [2, 4, 6, 25, 27, 29, 31],
   [2, 5, 7, 8, 10, 13, 15],
   [2, 5, 7, 9, 11, 12, 14],
   [2, 5, 7, 16, 18, 21, 23],
   [2, 5, 7, 17, 19, 20, 22],
   [2, 5, 7, 24, 26, 29, 31],
   [2, 5, 7, 25, 27, 28, 30],
   [2, 8, 10, 16, 18, 24, 26],
   [2, 8, 10, 17, 19, 25, 27],
   [2, 8, 10, 20, 22, 28, 30],
   [2, 8, 10, 21, 23, 29, 31],
   [2, 9, 11, 16, 18, 25, 27],
   [2, 9, 11, 17, 19, 24, 26],
   [2, 9, 11, 20, 22, 29, 31],
   [2, 9, 11, 21, 23, 28, 30],
   [2, 12, 14, 16, 18, 28, 30],
   [2, 12, 14, 17, 19, 29, 31],
   [2, 12, 14, 20, 22, 24, 26],
   [2, 12, 14, 21, 23, 25, 27],
   [2, 13, 15, 16, 18, 29, 31],
   [2, 13, 15, 17, 19, 28, 30],
   [2, 13, 15, 20, 22, 25, 27],
   [2, 13, 15, 21, 23, 24, 26],
   [3, 4, 7, 8, 11, 12, 15],
   [3, 4, 7, 9, 10, 13, 14],
   [3, 4, 7, 16, 19, 20, 23],
   [3, 4, 7, 17, 18, 21, 22],
   [3, 4, 7, 24, 27, 28, 31],
   [3, 4, 7, 25, 26, 29, 30],
   [3, 5, 6, 8, 11, 13, 14],
   [3, 5, 6, 9, 10, 12, 15],
   [3, 5, 6, 16, 19, 21, 22],
   [3, 5, 6, 17, 18, 20, 23],
   [3, 5, 6, 24, 27, 29, 30],
   [3, 5, 6, 25, 26, 28, 31],
   [3, 8, 11, 16, 19, 24, 27],
   [3, 8, 11, 17, 18, 25, 26],
   [3, 8, 11, 20, 23, 28, 31],
   [3, 8, 11, 21, 22, 29, 30],
   [3, 9, 10, 16, 19, 25, 26],
   [3, 9, 10, 17, 18, 24, 27],
   [3, 9, 10, 20, 23, 29, 30],
   [3, 9, 10, 21, 22, 28, 31],
   [3, 12, 15, 16, 19, 28, 31],
   [3, 12, 15, 17, 18, 29, 30],
   [3, 12, 15, 20, 23, 24, 27],
   [3, 12, 15, 21, 22, 25, 26],
   [3, 13, 14, 16, 19, 29, 30],
   [3, 13, 14, 17, 18, 28, 31],
   [3, 13, 14, 20, 23, 25, 26],
   [3, 13, 14, 21, 22, 24, 27],
   [4, 8, 12, 16, 20, 24, 28],
   [4, 8, 12, 17, 21, 25, 29],
   [4, 8, 12, 18, 22, 26, 30],
   [4, 8, 12, 19, 23, 27, 31],
   [4, 9, 13, 16, 20, 25, 29],
   [4, 9, 13, 17, 21, 24, 28],
   [4, 9, 13, 18, 22, 27, 31],
   [4, 9, 13, 19, 23, 26, 30],
   [4, 10, 14, 16, 20, 26, 30],
   [4, 10, 14, 17, 21, 27, 31],
   [4, 10, 14, 18, 22, 24, 28],
   [4, 10, 14, 19, 23, 25, 29],
   [4, 11, 15, 16, 20, 27, 31],
   [4, 11, 15, 17, 21, 26, 30],
   [4, 11, 15, 18, 22, 25, 29],
   [4, 11, 15, 19, 23, 24, 28],
   [5, 8, 13, 16, 21, 24, 29],
   [5, 8, 13, 17, 20, 25, 28],
   [5, 8, 13, 18, 23, 26, 31],
   [5, 8, 13, 19, 22, 27, 30],
   [5, 9, 12, 16, 21, 25, 28],
   [5, 9, 12, 17, 20, 24, 29],
   [5, 9, 12, 18, 23, 27, 30],
   [5, 9, 12, 19, 22, 26, 31],
   [5, 10, 15, 16, 21, 26, 31],
   [5, 10, 15, 17, 20, 27, 30],
   [5, 10, 15, 18, 23, 24, 29],
   [5, 10, 15, 19, 22, 25, 28],
   [5, 11, 14, 16, 21, 27, 30],
   [5, 11, 14, 17, 20, 26, 31],
   [5, 11, 14, 18, 23, 25, 28],
   [5, 11, 14, 19, 22, 24, 29],
   [6, 8, 14, 16, 22, 24, 30],
   [6, 8, 14, 17, 23, 25, 31],
   [6, 8, 14, 18, 20, 26, 28],
   [6, 8, 14, 19, 21, 27, 29],
   [6, 9, 15, 16, 22, 25, 31],
   [6, 9, 15, 17, 23, 24, 30],
   [6, 9, 15, 18, 20, 27, 29],
   [6, 9, 15, 19, 21, 26, 28],
   [6, 10, 12, 16, 22, 26, 28],
   [6, 10, 12, 17, 23, 27, 29],
   [6, 10, 12, 18, 20, 24, 30],
   [6, 10, 12, 19, 21, 25, 31],
   [6, 11, 13, 16, 22, 27, 29],
   [6, 11, 13, 17, 23, 26, 28],
   [6, 11, 13, 18, 20, 25, 31],
   [6, 11, 13, 19, 21, 24, 30],
   [7, 8, 15, 16, 23, 24, 31],
   [7, 8, 15, 17, 22, 25, 30],
   [7, 8, 15, 18, 21, 26, 29],
   [7, 8, 15, 19, 20, 27, 28],
   [7, 9, 14, 16, 23, 25, 30],
   [7, 9, 14, 17, 22, 24, 31],
   [7, 9, 14, 18, 21, 27, 28],
   [7, 9, 14, 19, 20, 26, 29],
   [7, 10, 13, 16, 23, 26, 29],
   [7, 10, 13, 17, 22, 27, 28],
   [7, 10, 13, 18, 21, 24, 31],
   [7, 10, 13, 19, 20, 25, 30],
   [7, 11, 12, 16, 23, 27, 28],
   [7, 11, 12, 17, 22, 26, 29],
   [7, 11, 12, 18, 21, 25, 30],
   [7, 11, 12, 19, 20, 24, 31]]
/-- The 35 GF(2)-lines of the sedenion frame: `{a, b, a⊕b}` with a,b ∈ 1..15.
    Each spans (with e₀) a 4-dim subalgebra. -/
def sedLines : List (List (Fin 32)) :=
  [[1, 2, 3],
   [1, 4, 5],
   [1, 6, 7],
   [1, 8, 9],
   [1, 10, 11],
   [1, 12, 13],
   [1, 14, 15],
   [2, 4, 6],
   [2, 5, 7],
   [2, 8, 10],
   [2, 9, 11],
   [2, 12, 14],
   [2, 13, 15],
   [3, 4, 7],
   [3, 5, 6],
   [3, 8, 11],
   [3, 9, 10],
   [3, 12, 15],
   [3, 13, 14],
   [4, 8, 12],
   [4, 9, 13],
   [4, 10, 14],
   [4, 11, 15],
   [5, 8, 13],
   [5, 9, 12],
   [5, 10, 15],
   [5, 11, 14],
   [6, 8, 14],
   [6, 9, 15],
   [6, 10, 12],
   [6, 11, 13],
   [7, 8, 15],
   [7, 9, 14],
   [7, 10, 13],
   [7, 11, 12]]


/-! ## 4. The D1 discriminator predicate (closed form) -/

/-- `span₄(L) = {0, a, b, a⊕b}` for a line `L = [a, b, a⊕b]`, as a list of
    `Nat` index values (all < 16). -/
def span4 (L : List (Fin 32)) : List Nat := 0 :: L.map (·.val)

/-- `L` is a base-octonion **Fano line**: every element lies in {1,..,7}. -/
def isFano (L : List (Fin 32)) : Bool := L.all (fun x => 1 ≤ x.val ∧ x.val ≤ 7)

/-- The "doubly-twisted" coset reps for a Fano line `L`:
    `{8 ⊕ v : v ∈ {1..7}, v ∉ span₄(L)}` (as `Nat` values). -/
def twistedReps (L : List (Fin 32)) : List Nat :=
  (List.range 8).filter (fun v => 1 ≤ v ∧ v ∉ span4 L) |>.map (fun v => 8 ^^^ v)

/-- **D1 discriminator.** A crossing candidate built from line `L` and coset rep
    `c` is an octonion copy iff `predPass L c`:
      `c ∈ span₄(L)`  (the canonical CD-double — valid for ALL 35 lines)
      OR `L` is a Fano line AND `c ∈ twistedReps L`  (the extra twisted double). -/
def predPass (L : List (Fin 32)) (c : Fin 16) : Bool :=
  (c.val ∈ span4 L) || (isFano L && c.val ∈ twistedReps L)

/-- Crossing candidate data: for each of the 140 crossing (line × coset) pairs,
    the line `L`, the coset representative `c`, and the resulting 8-dim
    candidate's 7 nonzero indices (lower part = the line, upper part =
    {16 + (c⊕s) : s ∈ span₄(L)}). Reconstruction is verified consistent with
    `predPass`/`isAlternative` below; the candidate index list lets each
    theorem recompute alternativity directly (the brute-force truth). -/
def crossingData : List ((List (Fin 32)) × (Fin 16) × (List (Fin 32))) :=
  [([1, 2, 3], 0, [1, 2, 3, 16, 17, 18, 19]),
   ([1, 2, 3], 4, [1, 2, 3, 20, 21, 22, 23]),
   ([1, 2, 3], 8, [1, 2, 3, 24, 25, 26, 27]),
   ([1, 2, 3], 12, [1, 2, 3, 28, 29, 30, 31]),
   ([1, 4, 5], 0, [1, 4, 5, 16, 17, 20, 21]),
   ([1, 4, 5], 2, [1, 4, 5, 18, 19, 22, 23]),
   ([1, 4, 5], 8, [1, 4, 5, 24, 25, 28, 29]),
   ([1, 4, 5], 10, [1, 4, 5, 26, 27, 30, 31]),
   ([1, 6, 7], 0, [1, 6, 7, 16, 17, 22, 23]),
   ([1, 6, 7], 2, [1, 6, 7, 18, 19, 20, 21]),
   ([1, 6, 7], 8, [1, 6, 7, 24, 25, 30, 31]),
   ([1, 6, 7], 10, [1, 6, 7, 26, 27, 28, 29]),
   ([1, 8, 9], 0, [1, 8, 9, 16, 17, 24, 25]),
   ([1, 8, 9], 2, [1, 8, 9, 18, 19, 26, 27]),
   ([1, 8, 9], 4, [1, 8, 9, 20, 21, 28, 29]),
   ([1, 8, 9], 6, [1, 8, 9, 22, 23, 30, 31]),
   ([1, 10, 11], 0, [1, 10, 11, 16, 17, 26, 27]),
   ([1, 10, 11], 2, [1, 10, 11, 18, 19, 24, 25]),
   ([1, 10, 11], 4, [1, 10, 11, 20, 21, 30, 31]),
   ([1, 10, 11], 6, [1, 10, 11, 22, 23, 28, 29]),
   ([1, 12, 13], 0, [1, 12, 13, 16, 17, 28, 29]),
   ([1, 12, 13], 2, [1, 12, 13, 18, 19, 30, 31]),
   ([1, 12, 13], 4, [1, 12, 13, 20, 21, 24, 25]),
   ([1, 12, 13], 6, [1, 12, 13, 22, 23, 26, 27]),
   ([1, 14, 15], 0, [1, 14, 15, 16, 17, 30, 31]),
   ([1, 14, 15], 2, [1, 14, 15, 18, 19, 28, 29]),
   ([1, 14, 15], 4, [1, 14, 15, 20, 21, 26, 27]),
   ([1, 14, 15], 6, [1, 14, 15, 22, 23, 24, 25]),
   ([2, 4, 6], 0, [2, 4, 6, 16, 18, 20, 22]),
   ([2, 4, 6], 1, [2, 4, 6, 17, 19, 21, 23]),
   ([2, 4, 6], 8, [2, 4, 6, 24, 26, 28, 30]),
   ([2, 4, 6], 9, [2, 4, 6, 25, 27, 29, 31]),
   ([2, 5, 7], 0, [2, 5, 7, 16, 18, 21, 23]),
   ([2, 5, 7], 1, [2, 5, 7, 17, 19, 20, 22]),
   ([2, 5, 7], 8, [2, 5, 7, 24, 26, 29, 31]),
   ([2, 5, 7], 9, [2, 5, 7, 25, 27, 28, 30]),
   ([2, 8, 10], 0, [2, 8, 10, 16, 18, 24, 26]),
   ([2, 8, 10], 1, [2, 8, 10, 17, 19, 25, 27]),
   ([2, 8, 10], 4, [2, 8, 10, 20, 22, 28, 30]),
   ([2, 8, 10], 5, [2, 8, 10, 21, 23, 29, 31]),
   ([2, 9, 11], 0, [2, 9, 11, 16, 18, 25, 27]),
   ([2, 9, 11], 1, [2, 9, 11, 17, 19, 24, 26]),
   ([2, 9, 11], 4, [2, 9, 11, 20, 22, 29, 31]),
   ([2, 9, 11], 5, [2, 9, 11, 21, 23, 28, 30]),
   ([2, 12, 14], 0, [2, 12, 14, 16, 18, 28, 30]),
   ([2, 12, 14], 1, [2, 12, 14, 17, 19, 29, 31]),
   ([2, 12, 14], 4, [2, 12, 14, 20, 22, 24, 26]),
   ([2, 12, 14], 5, [2, 12, 14, 21, 23, 25, 27]),
   ([2, 13, 15], 0, [2, 13, 15, 16, 18, 29, 31]),
   ([2, 13, 15], 1, [2, 13, 15, 17, 19, 28, 30]),
   ([2, 13, 15], 4, [2, 13, 15, 20, 22, 25, 27]),
   ([2, 13, 15], 5, [2, 13, 15, 21, 23, 24, 26]),
   ([3, 4, 7], 0, [3, 4, 7, 16, 19, 20, 23]),
   ([3, 4, 7], 1, [3, 4, 7, 17, 18, 21, 22]),
   ([3, 4, 7], 8, [3, 4, 7, 24, 27, 28, 31]),
   ([3, 4, 7], 9, [3, 4, 7, 25, 26, 29, 30]),
   ([3, 5, 6], 0, [3, 5, 6, 16, 19, 21, 22]),
   ([3, 5, 6], 1, [3, 5, 6, 17, 18, 20, 23]),
   ([3, 5, 6], 8, [3, 5, 6, 24, 27, 29, 30]),
   ([3, 5, 6], 9, [3, 5, 6, 25, 26, 28, 31]),
   ([3, 8, 11], 0, [3, 8, 11, 16, 19, 24, 27]),
   ([3, 8, 11], 1, [3, 8, 11, 17, 18, 25, 26]),
   ([3, 8, 11], 4, [3, 8, 11, 20, 23, 28, 31]),
   ([3, 8, 11], 5, [3, 8, 11, 21, 22, 29, 30]),
   ([3, 9, 10], 0, [3, 9, 10, 16, 19, 25, 26]),
   ([3, 9, 10], 1, [3, 9, 10, 17, 18, 24, 27]),
   ([3, 9, 10], 4, [3, 9, 10, 20, 23, 29, 30]),
   ([3, 9, 10], 5, [3, 9, 10, 21, 22, 28, 31]),
   ([3, 12, 15], 0, [3, 12, 15, 16, 19, 28, 31]),
   ([3, 12, 15], 1, [3, 12, 15, 17, 18, 29, 30]),
   ([3, 12, 15], 4, [3, 12, 15, 20, 23, 24, 27]),
   ([3, 12, 15], 5, [3, 12, 15, 21, 22, 25, 26]),
   ([3, 13, 14], 0, [3, 13, 14, 16, 19, 29, 30]),
   ([3, 13, 14], 1, [3, 13, 14, 17, 18, 28, 31]),
   ([3, 13, 14], 4, [3, 13, 14, 20, 23, 25, 26]),
   ([3, 13, 14], 5, [3, 13, 14, 21, 22, 24, 27]),
   ([4, 8, 12], 0, [4, 8, 12, 16, 20, 24, 28]),
   ([4, 8, 12], 1, [4, 8, 12, 17, 21, 25, 29]),
   ([4, 8, 12], 2, [4, 8, 12, 18, 22, 26, 30]),
   ([4, 8, 12], 3, [4, 8, 12, 19, 23, 27, 31]),
   ([4, 9, 13], 0, [4, 9, 13, 16, 20, 25, 29]),
   ([4, 9, 13], 1, [4, 9, 13, 17, 21, 24, 28]),
   ([4, 9, 13], 2, [4, 9, 13, 18, 22, 27, 31]),
   ([4, 9, 13], 3, [4, 9, 13, 19, 23, 26, 30]),
   ([4, 10, 14], 0, [4, 10, 14, 16, 20, 26, 30]),
   ([4, 10, 14], 1, [4, 10, 14, 17, 21, 27, 31]),
   ([4, 10, 14], 2, [4, 10, 14, 18, 22, 24, 28]),
   ([4, 10, 14], 3, [4, 10, 14, 19, 23, 25, 29]),
   ([4, 11, 15], 0, [4, 11, 15, 16, 20, 27, 31]),
   ([4, 11, 15], 1, [4, 11, 15, 17, 21, 26, 30]),
   ([4, 11, 15], 2, [4, 11, 15, 18, 22, 25, 29]),
   ([4, 11, 15], 3, [4, 11, 15, 19, 23, 24, 28]),
   ([5, 8, 13], 0, [5, 8, 13, 16, 21, 24, 29]),
   ([5, 8, 13], 1, [5, 8, 13, 17, 20, 25, 28]),
   ([5, 8, 13], 2, [5, 8, 13, 18, 23, 26, 31]),
   ([5, 8, 13], 3, [5, 8, 13, 19, 22, 27, 30]),
   ([5, 9, 12], 0, [5, 9, 12, 16, 21, 25, 28]),
   ([5, 9, 12], 1, [5, 9, 12, 17, 20, 24, 29]),
   ([5, 9, 12], 2, [5, 9, 12, 18, 23, 27, 30]),
   ([5, 9, 12], 3, [5, 9, 12, 19, 22, 26, 31]),
   ([5, 10, 15], 0, [5, 10, 15, 16, 21, 26, 31]),
   ([5, 10, 15], 1, [5, 10, 15, 17, 20, 27, 30]),
   ([5, 10, 15], 2, [5, 10, 15, 18, 23, 24, 29]),
   ([5, 10, 15], 3, [5, 10, 15, 19, 22, 25, 28]),
   ([5, 11, 14], 0, [5, 11, 14, 16, 21, 27, 30]),
   ([5, 11, 14], 1, [5, 11, 14, 17, 20, 26, 31]),
   ([5, 11, 14], 2, [5, 11, 14, 18, 23, 25, 28]),
   ([5, 11, 14], 3, [5, 11, 14, 19, 22, 24, 29]),
   ([6, 8, 14], 0, [6, 8, 14, 16, 22, 24, 30]),
   ([6, 8, 14], 1, [6, 8, 14, 17, 23, 25, 31]),
   ([6, 8, 14], 2, [6, 8, 14, 18, 20, 26, 28]),
   ([6, 8, 14], 3, [6, 8, 14, 19, 21, 27, 29]),
   ([6, 9, 15], 0, [6, 9, 15, 16, 22, 25, 31]),
   ([6, 9, 15], 1, [6, 9, 15, 17, 23, 24, 30]),
   ([6, 9, 15], 2, [6, 9, 15, 18, 20, 27, 29]),
   ([6, 9, 15], 3, [6, 9, 15, 19, 21, 26, 28]),
   ([6, 10, 12], 0, [6, 10, 12, 16, 22, 26, 28]),
   ([6, 10, 12], 1, [6, 10, 12, 17, 23, 27, 29]),
   ([6, 10, 12], 2, [6, 10, 12, 18, 20, 24, 30]),
   ([6, 10, 12], 3, [6, 10, 12, 19, 21, 25, 31]),
   ([6, 11, 13], 0, [6, 11, 13, 16, 22, 27, 29]),
   ([6, 11, 13], 1, [6, 11, 13, 17, 23, 26, 28]),
   ([6, 11, 13], 2, [6, 11, 13, 18, 20, 25, 31]),
   ([6, 11, 13], 3, [6, 11, 13, 19, 21, 24, 30]),
   ([7, 8, 15], 0, [7, 8, 15, 16, 23, 24, 31]),
   ([7, 8, 15], 1, [7, 8, 15, 17, 22, 25, 30]),
   ([7, 8, 15], 2, [7, 8, 15, 18, 21, 26, 29]),
   ([7, 8, 15], 3, [7, 8, 15, 19, 20, 27, 28]),
   ([7, 9, 14], 0, [7, 9, 14, 16, 23, 25, 30]),
   ([7, 9, 14], 1, [7, 9, 14, 17, 22, 24, 31]),
   ([7, 9, 14], 2, [7, 9, 14, 18, 21, 27, 28]),
   ([7, 9, 14], 3, [7, 9, 14, 19, 20, 26, 29]),
   ([7, 10, 13], 0, [7, 10, 13, 16, 23, 26, 29]),
   ([7, 10, 13], 1, [7, 10, 13, 17, 22, 27, 28]),
   ([7, 10, 13], 2, [7, 10, 13, 18, 21, 24, 31]),
   ([7, 10, 13], 3, [7, 10, 13, 19, 20, 25, 30]),
   ([7, 11, 12], 0, [7, 11, 12, 16, 23, 27, 28]),
   ([7, 11, 12], 1, [7, 11, 12, 17, 22, 26, 29]),
   ([7, 11, 12], 2, [7, 11, 12, 18, 21, 25, 30]),
   ([7, 11, 12], 3, [7, 11, 12, 19, 20, 24, 31])]


/-! ## 5. Theorem 3 — all 35 sedenion lines are associative (quaternionic) -/

/-- **All 35 GF(2)-lines of the sedenion frame span associative subalgebras**
    (quaternion copies ℍ): every basis-triple associator coefficient vanishes.
    Light check (35 lines × 4³ triples over the lower 16 indices). -/
theorem all_sedenion_lines_associative :
    ∀ L ∈ sedLines, isAssociative (withUnit L) := by
  unfold sedLines withUnit
  decide +kernel

/-! ## 6. Theorem 2 — the 8 base octonion copies persist into 𝕋 -/

/-- The 8 base 𝕊-hyperplane subalgebras that pass O1a (all indices < 16). These
    are the `hyperIdx` normals 1..8 of `SedenionOctonionCount`, restated here as
    their 7 nonzero index lists, embedded unchanged into the 32-dim frame. -/
def baseCopies : List (List (Fin 32)) :=
  [[2, 4, 6, 8, 10, 12, 14],
   [1, 4, 5, 8, 9, 12, 13],
   [3, 4, 7, 8, 11, 12, 15],
   [1, 2, 3, 8, 9, 10, 11],
   [2, 5, 7, 8, 10, 13, 15],
   [1, 6, 7, 8, 9, 14, 15],
   [3, 5, 6, 8, 11, 13, 14],
   [1, 2, 3, 4, 5, 6, 7]]

/-- **Base copies persist.** Each of the 8 O1a-passing 𝕊-hyperplane subalgebras
    is alternative as a subalgebra of the 32-dim 𝕋 (the 16×16 sub-block of the
    sign table is the O1a table, so alternativity is inherited — witness for
    monotonicity k(5) ≥ k(4)). -/
theorem base_copies_persist :
    ∀ H ∈ baseCopies, isAlternative H := by
  unfold baseCopies
  decide +kernel

/-- The 8 base copies all live in the sedenion (all indices < 16). -/
theorem base_copies_inside_sedenion :
    ∀ H ∈ baseCopies, ∀ x ∈ H, x.val < 16 := by
  unfold baseCopies
  decide +kernel

/-! ## 7. Theorem 4 (D1) — crossing alternativity ⟺ the closed predicate -/

/-- **D1 — the discriminator.** For every one of the 140 crossing (line × coset)
    candidates, the candidate 8-dim subalgebra (with `e₀` adjoined) is alternative
    — i.e. an octonion copy — **iff** the closed predicate `predPass L c` holds.
    The left side is recomputed directly from the candidate's index list (the
    brute-force alternativity truth); the right side from `(L, c)` alone. Their
    agreement on all 140 crossing pairs is the kernel-checked discriminator. -/
theorem crossing_pass_iff_discriminator :
    ∀ t ∈ crossingData,
      (isAlternative (withUnit t.2.2) ↔ predPass t.1 t.2.1 = true) := by
  unfold crossingData
  decide +kernel

/-! ## 8. Theorem 5 — the 42 = 35 + 7 split of passing crossing candidates -/

/-- Number of crossing pairs whose candidate is alternative (recomputed from the
    candidate index list). -/
def crossingAlternativeCount : Nat :=
  crossingData.countP (fun t => decide (isAlternative (withUnit t.2.2)))

/-- Number of crossing pairs passing the closed predicate `predPass`. -/
def crossingPredCount : Nat :=
  crossingData.countP (fun t => predPass t.1 t.2.1)

/-- Number of crossing pairs passing the **canonical** clause `c ∈ span₄(L)`
    (one per line → 35). -/
def crossingCanonicalCount : Nat :=
  crossingData.countP (fun t => decide (t.2.1.val ∈ span4 t.1))

/-- Number of crossing pairs passing **only** the twisted clause (the extra
    Fano coset → 7). -/
def crossingTwistedExtraCount : Nat :=
  crossingData.countP (fun t =>
    decide (t.2.1.val ∉ span4 t.1) && predPass t.1 t.2.1)

/-- The brute-force alternative count equals the predicate count, via the
    pointwise discriminator `crossing_pass_iff_discriminator`. Proved by
    `List.countP_congr` (cheap — reuses Theorem 4, no second heavy alternativity
    sweep). -/
theorem crossingAlternativeCount_eq_predCount :
    crossingAlternativeCount = crossingPredCount := by
  unfold crossingAlternativeCount crossingPredCount
  apply List.countP_congr
  intro t ht
  have h := crossing_pass_iff_discriminator t ht
  simp only [decide_eq_true_eq]
  exact h

/-- **The 42 = 35 + 7 split.** Passing crossing candidates number 42; this equals
    35 canonical doublings (one per sedenion line) + 7 doubly-twisted doublings
    (one extra coset for each base-octonion Fano line). The predicate count and
    the brute-force alternativity count both equal 42. The (heavy) alternativity
    count is obtained from the predicate count via the discriminator, so the
    only expensive sweep is Theorem 4. -/
theorem forty_two_split :
    crossingAlternativeCount = 42 ∧
    crossingPredCount = 42 ∧
    crossingCanonicalCount = 35 ∧
    crossingTwistedExtraCount = 7 ∧
    crossingCanonicalCount + crossingTwistedExtraCount = 42 := by
  have hpred : crossingPredCount = 42 := by decide +kernel
  refine ⟨?_, hpred, ?_, ?_, ?_⟩
  · rw [crossingAlternativeCount_eq_predCount]; exact hpred
  · decide +kernel
  · decide +kernel
  · decide +kernel


/-! ## 9. Theorem 1 (D3) — exactly 50 of the 155 subspaces are octonion copies -/

/-- The number of the 155 candidate 8-dim frame subalgebras (with `e₀` adjoined)
    that are alternative. (Each such 8-dim alternative subalgebra is ≅ 𝕆 by
    Hurwitz/Zorn — cited, not proved in Lean; this identifier names only the
    kernel-checked fact, the alternativity count.) -/
def alternativeSubspaceCount : Nat :=
  subspaces.countP (fun H => decide (isAlternative (withUnit H)))

/-- The number of the 155 that are alternative AND lie entirely inside the base
    sedenion (all indices < 16). -/
def baseAlternativeCount : Nat :=
  subspaces.countP (fun H => H.all (·.val < 16) && decide (isAlternative (withUnit H)))

/-- The number of the 155 that are alternative AND cross into the doubled half. -/
def crossAlternativeCount : Nat :=
  subspaces.countP (fun H => H.any (·.val ≥ 16) && decide (isAlternative (withUnit H)))

/-- **D3 — the count.** Exactly **50** of the 155 candidate 8-dim frame
    subalgebras of the 32-dim Cayley–Dickson algebra 𝕋 = CD(𝕊) are alternative.
    (Each such 8-dim alternative subalgebra is ≅ 𝕆 by Hurwitz/Zorn, cited not
    proved in Lean.) So k(5) = 50, not 2⁵−1 = 31 and not 155. -/
theorem alternative_subspace_count_32_eq_fifty : alternativeSubspaceCount = 50 := by
  unfold alternativeSubspaceCount
  decide +kernel

/-- **The 8 + 42 split of the 50.** Of the 50 octonion copies, 8 lie inside the
    base sedenion (the O1a result restated in 𝕋) and 42 cross into the doubled
    half; 8 + 42 = 50. -/
theorem base_plus_crossing_eq_fifty :
    baseAlternativeCount = 8 ∧
    crossAlternativeCount = 42 ∧
    baseAlternativeCount + crossAlternativeCount = alternativeSubspaceCount := by
  have hbase : baseAlternativeCount = 8 := by unfold baseAlternativeCount; decide +kernel
  have hcross : crossAlternativeCount = 42 := by unfold crossAlternativeCount; decide +kernel
  refine ⟨hbase, hcross, ?_⟩
  rw [hbase, hcross, alternative_subspace_count_32_eq_fifty]

/-! ## 10. Completeness audit — `#print axioms` on every main theorem

    Each must depend only on the three standard axioms
    `{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no native/reduceBool
    axiom). Reported in the build log. -/

#print axioms alternative_subspace_count_32_eq_fifty
#print axioms base_plus_crossing_eq_fifty
#print axioms base_copies_persist
#print axioms base_copies_inside_sedenion
#print axioms all_sedenion_lines_associative
#print axioms crossing_pass_iff_discriminator
#print axioms crossingAlternativeCount_eq_predCount
#print axioms forty_two_split

end QBP.Foundations.Octonion32Count
