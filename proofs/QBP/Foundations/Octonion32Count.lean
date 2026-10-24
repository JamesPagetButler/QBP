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

  Proof architecture + resource note (housekeeping #633, 2026-10-18). The
  theorem statements are unchanged since b1bd7ae; the proofs were re-factored
  because the original monolithic `decide +kernel` sweeps needed > 12 GiB
  (measured: killed at a 12 GiB cgroup cap; RSS at kill 14.9 GiB, still
  climbing — a lower bound on the true peak; `lake build` OOM-killed at 10 GB
  in #633 and at 6 GB in #683). Measured after the refactor, standalone `lean`
  under `run-bounded 12G` / `8G`: exit 0, wall ≈ 1:37, peak RSS 4.42–4.58 GiB
  (author, 2026-10-21), 4.52 GiB / 1:36.73 (Red Team review of PR #727); the
  import floor alone is 3.35 GiB. Root cause: each kernel
  sign lookup through the `![...]` table (`Matrix.vecCons`/`Fin.cases`) costs
  ≈35 KB of never-freed kernel cache, ≈140 MB per 8-dim candidate. Now:
    • §4b `sgnFast` — a bit-packed copy of the table, kernel-checked equal to
      `sgnTable` on all 1024 entries (`sgnTable_eq_sgnFast`); the brute-force
      sweeps run on it and are transported by `isAlternative_iff_fast`.
    • §7 the one unavoidable sweep (140 crossing candidates) runs in 7 kernel
      chunks of 20, glued by `forall_mem_split`/`forall_mem_split_at`.
    • §9 the 155-count is derived: `crossing_subspaces_eq_crossingData`
      kernel-checks that the 140 crossing subspaces ARE the `crossingData`
      index lists (in order), so cross = 42 from Theorem 5; the 15 base
      candidates are swept (8 pass); a generic `countP` partition
      (`countP_eq_add_of_parts`, over variables) adds them.
  Measured after the refactor: see `analysis/633-octonion32count/` and
  `docs/foundations/lean-build-resource-notes.md` (per-module peak-RSS table).
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


/-! ## 4b. Kernel-cheap sign lookup (housekeeping #633)

The `![...]` table in §1 is the human-readable record, but every kernel lookup
through `Matrix.vecCons`/`Fin.cases` costs ≈35 KB of kernel whnf-cache, i.e.
≈140 MB and ≈1.7 s **per candidate** 8-dim subalgebra (8³ triples × 2 associator
identities × 4 lookups). The kernel never frees that cache inside one
declaration, so a single `decide +kernel` over all 155 candidates needed
> 12 GiB (killed at the cap; RSS at kill 14.9 GiB, still climbing — a lower
bound on the true peak; measured 2026-10-18, `analysis/633-octonion32count/`). The heavy
sweeps below therefore run against `sgnFast`, a bit-packed copy of the same
table (`sgnRowMask a` has bit `b` set iff `sgnTable a b = -1`; the lookup is a
GMP-accelerated `Nat.testBit`), and `sgnTable_eq_sgnFast` kernel-checks that
the two encodings agree on all 32 × 32 entries. Every theorem *statement* still
refers to `sgnTable` through `sgn` / `assocCoeff` / `isAlternative`; the `Fast`
variants appear only inside proofs, transported by `isAlternative_iff_fast` /
`isAssociative_iff_fast`. -/

/-- Row `a` of `sgnTable`, packed as a 32-bit mask: bit `b` is set iff
    `sgnTable a b = -1`. (Row 0 and column 0 are all `+1`, so `sgnRowMask 0 = 0`
    and every mask is even; `sgnTable a a = -1` for `a ≥ 1`, so bit `a` of mask
    `a` is set.) Generated mechanically from the `![...]` table; equality with it
    is the kernel-checked theorem `sgnTable_eq_sgnFast`, not an assumption. -/
def sgnRowMask : Fin 32 → Nat := fun a =>
  [0x00000000, 0x6996966a, 0xc33c3cc6, 0xa55a5aac, 0x0ff0f01e, 0x55aaaa74, 0x996666d8, 0x33ccccb2,
   0xff0001fe, 0x6a6a9794, 0xc6c63d38, 0xacac5b52, 0x1e1ef1e0, 0x7474ab8a, 0xd8d86726, 0xb2b2cd4c,
   0x0001fffe, 0x69976994, 0xc33dc338, 0xa55ba552, 0x0ff10fe0, 0x55ab558a, 0x99679926, 0x33cd334c,
   0xff01fe00, 0x6a6b686a, 0xc6c7c2c6, 0xacada4ac, 0x1e1f0e1e, 0x74755474, 0xd8d998d8, 0xb2b332b2].getD a.val 0

/-- Bit-packed sign lookup. `sgnTable_eq_sgnFast` proves it equals `sgnTable`. -/
def sgnFast (a b : Fin 32) : Int := if (sgnRowMask a).testBit b.val then -1 else 1

/-- The two encodings of the sign table agree on all 1024 entries (kernel-checked
    over the `Nat` ranges; ≈0.5 GiB, ≈4 s). -/
theorem sgnTable_eq_sgnFast :
    ∀ a (ha : a < 32), ∀ b (hb : b < 32), sgnTable ⟨a, ha⟩ ⟨b, hb⟩ = sgnFast ⟨a, ha⟩ ⟨b, hb⟩ := by
  decide +kernel

theorem sgn_eq_sgnFast (a b : Fin 32) : sgn a b = sgnFast a b :=
  sgnTable_eq_sgnFast a.1 a.2 b.1 b.2

/-- `assocCoeff` computed through the bit-packed table. -/
def assocCoeffFast (a b c : Fin 32) : Int :=
  sgnFast a b * sgnFast (ixor a b) c - sgnFast b c * sgnFast a (ixor b c)

theorem assocCoeff_eq_fast (a b c : Fin 32) : assocCoeff a b c = assocCoeffFast a b c := by
  simp only [assocCoeff, assocCoeffFast, sgn_eq_sgnFast]

/-- `isAlternative` with `assocCoeffFast` in place of `assocCoeff` (proof-internal). -/
def isAlternativeFast (H : List (Fin 32)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H,
    assocCoeffFast a b c = - assocCoeffFast b a c ∧
    assocCoeffFast a b c = - assocCoeffFast a c b

instance (H : List (Fin 32)) : Decidable (isAlternativeFast H) := by
  unfold isAlternativeFast; infer_instance

/-- `isAssociative` with `assocCoeffFast` in place of `assocCoeff` (proof-internal). -/
def isAssociativeFast (H : List (Fin 32)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, assocCoeffFast a b c = 0

instance (H : List (Fin 32)) : Decidable (isAssociativeFast H) := by
  unfold isAssociativeFast; infer_instance

theorem isAlternative_iff_fast (H : List (Fin 32)) : isAlternative H ↔ isAlternativeFast H := by
  simp only [isAlternative, isAlternativeFast, assocCoeff_eq_fast]

theorem isAssociative_iff_fast (H : List (Fin 32)) : isAssociative H ↔ isAssociativeFast H := by
  simp only [isAssociative, isAssociativeFast, assocCoeff_eq_fast]

/-! ## 4c. Chunking helpers (housekeeping #633)

A bounded universal over a literal list is split at `take`/`drop` positions so
that each piece is kernel-decided in its **own** declaration; the kernel's
whnf-cache is released between declarations, so peak memory is bounded by the
largest chunk rather than by the whole list. -/

/-- Split `∀ x ∈ l, p x` into the first `k` elements and the rest. -/
private theorem forall_mem_split {α : Type} (l : List α) (k : Nat) {p : α → Prop}
    (h₁ : ∀ x ∈ l.take k, p x) (h₂ : ∀ x ∈ l.drop k, p x) : ∀ x ∈ l, p x := by
  intro x hx
  rw [← List.take_append_drop k l, List.mem_append] at hx
  exact hx.elim (h₁ x) (h₂ x)

/-- Split `∀ x ∈ l.drop i, p x` into the `k` elements at offset `i` and the rest. -/
private theorem forall_mem_split_at {α : Type} (l : List α) (i k : Nat) {p : α → Prop}
    (h₁ : ∀ x ∈ (l.drop i).take k, p x) (h₂ : ∀ x ∈ l.drop (i + k), p x) :
    ∀ x ∈ l.drop i, p x := by
  intro x hx
  rw [← List.take_append_drop k (l.drop i), List.mem_append, List.drop_drop] at hx
  exact hx.elim (h₁ x) (h₂ x)

/-- `countP` partition: a predicate `g` counted over the `f`-part and the `¬f`-part
    of a list adds up to `g` counted over the whole list. -/
private theorem countP_and_add_countP_not_and {α : Type} (f g : α → Bool) (l : List α) :
    l.countP (fun x => f x && g x) + l.countP (fun x => !f x && g x) = l.countP g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.countP_cons]
    cases f x <;> cases g x <;> simp <;> omega


/-- `countP` partition with the complement given as any pointwise-equal predicate `f'`. -/
private theorem countP_partition {α : Type} (f g f' : α → Bool) (l : List α)
    (hf' : ∀ x, f' x = !f x) :
    l.countP (fun x => f x && g x) + l.countP (fun x => f' x && g x) = l.countP g := by
  rw [← countP_and_add_countP_not_and f g l]
  congr 1
  exact List.countP_congr (fun x _ => by rw [hf' x])

/-- A `g`-count equals `a + b` when the `f`-part counts `a` and the `f'`-part (`f'` =
    pointwise `¬f`) counts `b`. Stated over variables on purpose: the concrete sum
    `baseAlternativeCount + crossAlternativeCount` must never be unified or
    kernel-compared against a non-identical term, because a `Nat.add` definitional
    check makes both the elaborator (`reduceNat?`) and the kernel (`reduce_nat`)
    `whnf` the summands — i.e. evaluate `isAlternative` on the `![...]` table
    (#633 bisect: > 11 GB and climbing). Here only `a + b` on literals is ever
    reduced. -/
private theorem countP_eq_add_of_parts {α : Type} (f g f' : α → Bool) (l : List α)
    (hf' : ∀ x, f' x = !f x) (a b : Nat)
    (ha : l.countP (fun x => f x && g x) = a) (hb : l.countP (fun x => f' x && g x) = b) :
    l.countP g = a + b := by
  rw [← countP_partition f g f' l hf', ha, hb]

/-- If the `q`-part of `l` is the `f`-image of `l'`, counting `p` on the `q`-part of `l`
    is counting `p ∘ f` on `l'`. (Stated over variables so that instantiating it on the
    155- and 140-element lists is first-order unification — no elaborator evaluation.) -/
private theorem countP_and_eq_of_filter_eq_map {α β : Type} (p q : β → Bool) (l : List β)
    (f : α → β) (l' : List α) (h : l.filter q = l'.map f) :
    l.countP (fun x => q x && p x) = l'.countP (fun t => p (f t)) := by
  have h1 : l.countP (fun x => q x && p x) = l.countP (fun x => p x && q x) :=
    List.countP_congr (fun x _ => by rw [Bool.and_comm])
  rw [h1, ← List.countP_filter, h, List.countP_map, Function.comp_def]

/-- `any (≥ 16)` is the pointwise negation of `all (< 16)`. -/
private theorem any_ge_eq_not_all_lt (H : List (Fin 32)) :
    H.any (·.val ≥ 16) = !H.all (·.val < 16) := by
  rw [List.any_eq_not_all_not]
  have : (fun x : Fin 32 => !decide (x.val ≥ 16)) = (fun x => decide (x.val < 16)) := by
    funext x; rw [← decide_not]; exact decide_eq_decide.2 Nat.not_le
  rw [this]

/-! ## 5. Theorem 3 — all 35 sedenion lines are associative (quaternionic) -/

/-- **All 35 GF(2)-lines of the sedenion frame span associative subalgebras**
    (quaternion copies ℍ): every basis-triple associator coefficient vanishes.
    Light check (35 lines × 4³ triples over the lower 16 indices), run on the
    bit-packed table and transported by `isAssociative_iff_fast`. -/
theorem all_sedenion_lines_associative :
    ∀ L ∈ sedLines, isAssociative (withUnit L) := by
  have h : ∀ L ∈ sedLines, isAssociativeFast (withUnit L) := by
    decide +kernel
  intro L hL
  rw [isAssociative_iff_fast]
  exact h L hL

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
  have h : ∀ H ∈ baseCopies, isAlternativeFast H := by
    decide +kernel
  intro H hH
  rw [isAlternative_iff_fast]
  exact h H hH

/-- The 8 base copies all live in the sedenion (all indices < 16). -/
theorem base_copies_inside_sedenion :
    ∀ H ∈ baseCopies, ∀ x ∈ H, x.val < 16 := by
  unfold baseCopies
  decide +kernel

/-! ## 7. Theorem 4 (D1) — crossing alternativity ⟺ the closed predicate

This is the one unavoidable brute-force sweep (140 candidates × 8³ triples). It
is run on the bit-packed table in seven chunks of 20 candidates, each its own
kernel declaration (≈0.5 GiB each, from the measured ≈27 MB/candidate slope on
the bit-packed table; the monolithic form needed > 12 GiB), and the
chunks are glued by `forall_mem_split` / `forall_mem_split_at`. -/

/-- The D1 discriminator on the bit-packed table, for one crossing candidate. -/
private abbrev DiscriminatorFast (t : (List (Fin 32)) × (Fin 16) × (List (Fin 32))) : Prop :=
  isAlternativeFast (withUnit t.2.2) ↔ predPass t.1 t.2.1 = true

private theorem crossing_chunk₁ : ∀ t ∈ crossingData.take 20, DiscriminatorFast t := by
  decide +kernel
private theorem crossing_chunk₂ : ∀ t ∈ (crossingData.drop 20).take 20, DiscriminatorFast t := by
  decide +kernel
private theorem crossing_chunk₃ : ∀ t ∈ (crossingData.drop 40).take 20, DiscriminatorFast t := by
  decide +kernel
private theorem crossing_chunk₄ : ∀ t ∈ (crossingData.drop 60).take 20, DiscriminatorFast t := by
  decide +kernel
private theorem crossing_chunk₅ : ∀ t ∈ (crossingData.drop 80).take 20, DiscriminatorFast t := by
  decide +kernel
private theorem crossing_chunk₆ : ∀ t ∈ (crossingData.drop 100).take 20, DiscriminatorFast t := by
  decide +kernel
private theorem crossing_chunk₇ : ∀ t ∈ crossingData.drop 120, DiscriminatorFast t := by
  decide +kernel

/-- The seven chunks glued back together: the discriminator on the bit-packed
    table holds for all 140 crossing candidates. -/
private theorem crossing_pass_iff_discriminator_fast :
    ∀ t ∈ crossingData, DiscriminatorFast t :=
  forall_mem_split crossingData 20 crossing_chunk₁ <|
  forall_mem_split_at crossingData 20 20 crossing_chunk₂ <|
  forall_mem_split_at crossingData 40 20 crossing_chunk₃ <|
  forall_mem_split_at crossingData 60 20 crossing_chunk₄ <|
  forall_mem_split_at crossingData 80 20 crossing_chunk₅ <|
  forall_mem_split_at crossingData 100 20 crossing_chunk₆ crossing_chunk₇

/-- **D1 — the discriminator.** For every one of the 140 crossing (line × coset)
    candidates, the candidate 8-dim subalgebra (with `e₀` adjoined) is alternative
    — i.e. an octonion copy — **iff** the closed predicate `predPass L c` holds.
    The left side is recomputed directly from the candidate's index list (the
    brute-force alternativity truth); the right side from `(L, c)` alone. Their
    agreement on all 140 crossing pairs is the kernel-checked discriminator. -/
theorem crossing_pass_iff_discriminator :
    ∀ t ∈ crossingData,
      (isAlternative (withUnit t.2.2) ↔ predPass t.1 t.2.1 = true) := by
  intro t ht
  rw [isAlternative_iff_fast]
  exact crossing_pass_iff_discriminator_fast t ht

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

/-! ## 9. Theorem 1 (D3) — exactly 50 of the 155 subspaces are octonion copies

The count is **derived**, not re-swept (housekeeping #633): the 155 candidates
split into the 15 that lie inside the base sedenion and the 140 that cross into
the doubled half; `crossing_subspaces_eq_crossingData` kernel-checks that the
140 crossing index lists of `subspaces` are *exactly* the index lists recorded in
`crossingData`, in order, so their alternativity count is Theorem 5's 42; the 15
base candidates are swept directly (8 pass); and the generic partition lemma
`countP_eq_add_of_parts` adds the two halves to the total. Before #633
the total, the base part and the crossing part were three independent
monolithic sweeps (155 + 15 + 140 candidates). -/

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

/-- The 140 crossing candidates of `subspaces` are exactly the candidate index
    lists of `crossingData`, in the same order (kernel-checked list equality).
    This is what lets Theorem 5's count stand in for the crossing part of the
    155-count; before #633 this identity was implicit and never stated (the old
    proofs swept `subspaces` directly and never related it to `crossingData`). -/
theorem crossing_subspaces_eq_crossingData :
    subspaces.filter (fun H => H.any (·.val ≥ 16)) = crossingData.map (·.2.2) := by
  decide +kernel

/-- The 15 base candidates, swept on the bit-packed table (the `&&` short-circuits
    the 140 crossing candidates away before any alternativity check). -/
private theorem baseAlternativeCount_eq_eight : baseAlternativeCount = 8 := by
  have hfast : subspaces.countP
      (fun H => H.all (·.val < 16) && decide (isAlternativeFast (withUnit H))) = 8 := by
    decide +kernel
  have hcongr : baseAlternativeCount = subspaces.countP
      (fun H => H.all (·.val < 16) && decide (isAlternativeFast (withUnit H))) :=
    List.countP_congr (fun H _ => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, isAlternative_iff_fast])
  exact hcongr.trans hfast

/-- The crossing part of the 155-count is the crossing-pair count of §8
    (`countP_and_eq_of_filter_eq_map` instantiated on the kernel-checked list identity). -/
private theorem crossAlternativeCount_eq_crossingAlternativeCount :
    crossAlternativeCount = crossingAlternativeCount := by
  unfold crossAlternativeCount crossingAlternativeCount
  exact countP_and_eq_of_filter_eq_map
    (fun H : List (Fin 32) => decide (isAlternative (withUnit H)))
    (fun H : List (Fin 32) => H.any (·.val ≥ 16)) subspaces
    (fun t : (List (Fin 32)) × (Fin 16) × (List (Fin 32)) => t.2.2) crossingData
    crossing_subspaces_eq_crossingData

/-- The crossing part of the 155-count is 42 (Theorem 5 through the list identity). -/
private theorem crossAlternativeCount_eq_fortytwo : crossAlternativeCount = 42 := by
  rw [crossAlternativeCount_eq_crossingAlternativeCount, forty_two_split.1]

/-- **D3 — the count.** Exactly **50** of the 155 candidate 8-dim frame
    subalgebras of the 32-dim Cayley–Dickson algebra 𝕋 = CD(𝕊) are alternative.
    (Each such 8-dim alternative subalgebra is ≅ 𝕆 by Hurwitz/Zorn, cited not
    proved in Lean.) So k(5) = 50, not 2⁵−1 = 31 and not 155.

    Derived as 8 + 42 by the generic partition `countP_eq_add_of_parts`
    (`all (< 16)` / `any (≥ 16)` split the 155 candidates), from the 15-candidate
    base sweep and Theorem 5 via `crossing_subspaces_eq_crossingData`. -/
theorem alternative_subspace_count_32_eq_fifty : alternativeSubspaceCount = 50 := by
  have h := countP_eq_add_of_parts (fun H : List (Fin 32) => H.all (·.val < 16))
    (fun H : List (Fin 32) => decide (isAlternative (withUnit H)))
    (fun H : List (Fin 32) => H.any (·.val ≥ 16)) subspaces any_ge_eq_not_all_lt 8 42
    baseAlternativeCount_eq_eight crossAlternativeCount_eq_fortytwo
  exact h

/-- **The 8 + 42 split of the 50.** Of the 50 octonion copies, 8 lie inside the
    base sedenion (the O1a result restated in 𝕋) and 42 cross into the doubled
    half; 8 + 42 = 50. -/
theorem base_plus_crossing_eq_fifty :
    baseAlternativeCount = 8 ∧
    crossAlternativeCount = 42 ∧
    baseAlternativeCount + crossAlternativeCount = alternativeSubspaceCount := by
  refine ⟨baseAlternativeCount_eq_eight, crossAlternativeCount_eq_fortytwo, ?_⟩
  rw [baseAlternativeCount_eq_eight, crossAlternativeCount_eq_fortytwo,
    alternative_subspace_count_32_eq_fifty]

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
#print axioms sgnTable_eq_sgnFast
#print axioms crossing_subspaces_eq_crossingData

end QBP.Foundations.Octonion32Count
