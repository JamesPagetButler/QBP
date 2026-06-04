/-
  QBP.Foundations.FanoOrientationF3
  =================================

  Kernel-checked provenance for the F4 Fano-orientation table.

  This file settles the open provenance escalation on PR #470: it proves that the
  corrected 7×7 octonion multiplication table in `docs/conventions/fano-orientation.md`
  (F4) is *exactly* the multiplication forced by the ratified F3 Cayley–Dickson
  doubling formula (`docs/conventions/cd-doubling.md`), applied along the standard
  tower ℝ → ℂ → ℍ → 𝕆 with the ℍ-triad e₁ = i, e₂ = j, e₃ = k.

  Method.  We build the Cayley–Dickson tower as concrete nested pairs of `Int`
  coordinates (ℝ = `Int`, ℂ = `Int × Int`, ℍ = ℂ × ℂ, 𝕆 = ℍ × ℍ), with `Omul`
  the literal F3 doubling product
      (a₁,a₂)(b₁,b₂) = (a₁b₁ − conj(b₂)·a₂,  b₂·a₁ + a₂·conj(b₁)).
  Basis element eᵢ is the octonion with a 1 in coordinate i.  Every claim below is
  a finite statement over `Fin 8` indices with `Int` coefficients, closed by the
  Lean *kernel* `decide` (NO `native_decide`, NO `sorry`, NO vacuous `True`).

  Provenance result (see `fanoTableF4_eq_cayleyDickson`): the literal transcription
  of the F4 doc table agrees with the F3-derived products on ALL 64 basis pairs —
  0 mismatches.  The orientation in F4 is therefore F3-FORCED, not an independent
  literature pin.  (The archive table `archive/QBP_Octonion.lean::octonionMul`
  disagrees with F3 on 18 of 42 imaginary entries and is non-alternative — issue
  #472; a single witnessed disagreement is recorded in `archiveTable_disagrees_cd`.)

  Convention refs: docs/conventions/cd-doubling.md (F3), docs/conventions/fano-orientation.md (F4).
  Best-practices: ~/Documents/inter/lean-proof-best-practices.md (kernel `decide`,
  `#print axioms` gate, witnessed counterexamples).
-/

namespace QBP.Foundations.FanoOrientationF3

/-! ## 1. The Cayley–Dickson tower ℝ → ℂ → ℍ → 𝕆 (F3 doubling, Int coordinates)

We instantiate the F3 doubling formula
`(a₁,a₂)(b₁,b₂) = (a₁ b₁ − conj(b₂)·a₂,  b₂·a₁ + a₂·conj(b₁))`
at each rung.  Coordinates are `Int`; conjugation negates the second component of
each pair (and is the identity at the ℝ rung).  Everything is concrete data with
decidable equality, so the kernel can reduce products of basis elements. -/

/-- ℝ rung: coordinates are `Int`; conjugation is the identity. -/
abbrev R := Int
/-- ℝ multiplication. -/
def Rmul (a b : R) : R := a * b
/-- ℝ conjugation (trivial). -/
def Rconj (a : R) : R := a

/-- ℂ rung as a pair of reals. -/
abbrev C := R × R
/-- ℂ addition. -/
def Cadd (x y : C) : C := (x.1 + y.1, x.2 + y.2)
/-- ℂ negation. -/
def Cneg (x : C) : C := (-x.1, -x.2)
/-- ℂ conjugation: negate the imaginary part. -/
def Cconj (x : C) : C := (Rconj x.1, -x.2)
/-- ℂ multiplication via the F3 doubling formula on ℝ. -/
def Cmul (x y : C) : C :=
  (Rmul x.1 y.1 - Rmul (Rconj y.2) x.2,
   Rmul y.2 x.1 + Rmul x.2 (Rconj y.1))

/-- ℍ rung as a pair of complexes. -/
abbrev H := C × C
/-- ℍ addition. -/
def Hadd (x y : H) : H := (Cadd x.1 y.1, Cadd x.2 y.2)
/-- ℍ negation. -/
def Hneg (x : H) : H := (Cneg x.1, Cneg x.2)
/-- ℍ conjugation: conjugate first part, negate second. -/
def Hconj (x : H) : H := (Cconj x.1, Cneg x.2)
/-- ℂ subtraction (helper). -/
def Csub (x y : C) : C := Cadd x (Cneg y)
/-- ℍ multiplication via the F3 doubling formula on ℂ. -/
def Hmul (x y : H) : H :=
  (Csub (Cmul x.1 y.1) (Cmul (Cconj y.2) x.2),
   Cadd (Cmul y.2 x.1) (Cmul x.2 (Cconj y.1)))

/-- 𝕆 rung as a pair of quaternions. -/
abbrev O := H × H
/-- 𝕆 addition. -/
def Oadd (x y : O) : O := (Hadd x.1 y.1, Hadd x.2 y.2)
/-- 𝕆 negation. -/
def Oneg (x : O) : O := (Hneg x.1, Hneg x.2)
/-- 𝕆 conjugation: conjugate first part, negate second. -/
def Oconj (x : O) : O := (Hconj x.1, Hneg x.2)
/-- ℍ subtraction (helper). -/
def Hsub (x y : H) : H := Hadd x (Hneg y)
/-- 𝕆 multiplication via the F3 doubling formula on ℍ. -/
def Omul (x y : O) : O :=
  (Hsub (Hmul x.1 y.1) (Hmul (Hconj y.2) x.2),
   Hadd (Hmul y.2 x.1) (Hmul x.2 (Hconj y.1)))

/-- The octonion basis element `eᵢ` (i : Fin 8): a 1 in coordinate `i`, 0 elsewhere.
    Coordinate 0 = e₀ (the real unit), coordinates 1..7 = the imaginary units e₁..e₇. -/
def e (i : Fin 8) : O :=
  let c : Nat → Int := fun k => if k == i.val then 1 else 0
  (((c 0, c 1), (c 2, c 3)), ((c 4, c 5), (c 6, c 7)))

/-- The signed basis element `s · eₖ` for a `(sign, index)` pair, as produced by a
    multiplication-table entry.  Used to compare table entries to CD products. -/
def signedBasis (p : Int × Fin 8) : O :=
  let s := p.1
  let c : Nat → Int := fun k => if k == p.2.val then s else 0
  (((c 0, c 1), (c 2, c 3)), ((c 4, c 5), (c 6, c 7)))

/-! ## 2. Literal transcription of the F4 doc table

`fanoTableF4 a b = (sign, k)` means the F4 doc asserts `eₐ·e_b = sign · e_k`.
Indices are 0-based `Fin 8` (0 = e₀ identity, 1..7 = e₁..e₇).

This is a *verbatim* transcription of `docs/conventions/fano-orientation.md`:
the identity row/column (e₀) plus the 7×7 imaginary block at lines 36–42 of that
doc.  It is meant to be diffable by eye against the doc table; the kernel then
checks it against the F3 construction in `fanoTableF4_eq_cayleyDickson`. -/
def fanoTableF4 : Fin 8 → Fin 8 → Int × Fin 8 := fun a b =>
  match a.val, b.val with
  | 0, _ => (1, b)                       -- e₀·e_b = e_b
  | _, 0 => (1, a)                       -- eₐ·e₀ = eₐ
  -- e₁ row:  −1, e₃, −e₂, e₅, −e₄, −e₇, e₆
  | 1, 1 => (-1, 0) | 1, 2 => (1, 3) | 1, 3 => (-1, 2) | 1, 4 => (1, 5)
  | 1, 5 => (-1, 4) | 1, 6 => (-1, 7) | 1, 7 => (1, 6)
  -- e₂ row:  −e₃, −1, e₁, e₆, e₇, −e₄, −e₅
  | 2, 1 => (-1, 3) | 2, 2 => (-1, 0) | 2, 3 => (1, 1) | 2, 4 => (1, 6)
  | 2, 5 => (1, 7) | 2, 6 => (-1, 4) | 2, 7 => (-1, 5)
  -- e₃ row:  e₂, −e₁, −1, e₇, −e₆, e₅, −e₄
  | 3, 1 => (1, 2) | 3, 2 => (-1, 1) | 3, 3 => (-1, 0) | 3, 4 => (1, 7)
  | 3, 5 => (-1, 6) | 3, 6 => (1, 5) | 3, 7 => (-1, 4)
  -- e₄ row:  −e₅, −e₆, −e₇, −1, e₁, e₂, e₃
  | 4, 1 => (-1, 5) | 4, 2 => (-1, 6) | 4, 3 => (-1, 7) | 4, 4 => (-1, 0)
  | 4, 5 => (1, 1) | 4, 6 => (1, 2) | 4, 7 => (1, 3)
  -- e₅ row:  e₄, −e₇, e₆, −e₁, −1, −e₃, e₂
  | 5, 1 => (1, 4) | 5, 2 => (-1, 7) | 5, 3 => (1, 6) | 5, 4 => (-1, 1)
  | 5, 5 => (-1, 0) | 5, 6 => (-1, 3) | 5, 7 => (1, 2)
  -- e₆ row:  e₇, e₄, −e₅, −e₂, e₃, −1, −e₁
  | 6, 1 => (1, 7) | 6, 2 => (1, 4) | 6, 3 => (-1, 5) | 6, 4 => (-1, 2)
  | 6, 5 => (1, 3) | 6, 6 => (-1, 0) | 6, 7 => (-1, 1)
  -- e₇ row:  −e₆, e₅, e₄, −e₃, −e₂, e₁, −1
  | 7, 1 => (-1, 6) | 7, 2 => (1, 5) | 7, 3 => (1, 4) | 7, 4 => (-1, 3)
  | 7, 5 => (-1, 2) | 7, 6 => (1, 1) | 7, 7 => (-1, 0)
  | _, _ => (0, 0)   -- unreachable for Fin 8 × Fin 8 (all entries covered above)

/-! ## 3. Theorems (kernel `decide`).

Names state exactly what the kernel proves — no smuggled classifications. -/

/-- **Provenance result.**  The literal F4 doc table equals the F3 Cayley–Dickson
    products on all 64 basis pairs: for every `i j : Fin 8`,
    `eᵢ · e_j = signedBasis (fanoTableF4 i j)` under the F3 doubling product.
    Hence the F4 orientation is *forced* by F3, not independently chosen. -/
theorem fanoTableF4_eq_cayleyDickson :
    ∀ i j : Fin 8, Omul (e i) (e j) = signedBasis (fanoTableF4 i j) := by
  decide

/-- **Squares of imaginary units.**  For each imaginary index `i ∈ {1,…,7}`,
    `eᵢ · eᵢ = −e₀` under the F3 doubling product. -/
theorem cayleyDickson8_sq_neg_one :
    ∀ i : Fin 8, i.val ≠ 0 → Omul (e i) (e i) = Oneg (e 0) := by
  decide

/-- **Alternativity on basis triples.**  The F3-derived octonion product is
    left- and right-alternative on all basis elements:
    `(eᵢ·eᵢ)·e_j = eᵢ·(eᵢ·e_j)` and `(eᵢ·e_j)·e_j = eᵢ·(e_j·e_j)` for all `i, j`.
    (Equivalently: the associator `[eᵢ, eᵢ, e_j]` and `[eᵢ, e_j, e_j]` vanish, i.e.
    the associator is alternating in repeated-argument basis pairs.)  This is the
    property the broken archive table FAILS — see issue #472. -/
theorem cayleyDickson8_alternative_on_basis :
    ∀ i j : Fin 8,
      Omul (Omul (e i) (e i)) (e j) = Omul (e i) (Omul (e i) (e j)) ∧
      Omul (Omul (e i) (e j)) (e j) = Omul (e i) (Omul (e j) (e j)) := by
  decide

/-- Fano triple {1,2,3}: `e₁·e₂ = e₃` (sign +1) under F3. -/
theorem fanoTriple_oriented_123 : Omul (e 1) (e 2) = e 3 := by decide
/-- Fano triple {1,4,5}: `e₁·e₄ = e₅` (sign +1) under F3. -/
theorem fanoTriple_oriented_145 : Omul (e 1) (e 4) = e 5 := by decide
/-- Fano triple {1,6,7}: `e₁·e₇ = e₆` (sign +1) under F3 (F3-induced orientation). -/
theorem fanoTriple_oriented_167 : Omul (e 1) (e 7) = e 6 := by decide
/-- Fano triple {2,4,6}: `e₂·e₄ = e₆` (sign +1) under F3. -/
theorem fanoTriple_oriented_246 : Omul (e 2) (e 4) = e 6 := by decide
/-- Fano triple {2,5,7}: `e₂·e₅ = e₇` (sign +1) under F3. -/
theorem fanoTriple_oriented_257 : Omul (e 2) (e 5) = e 7 := by decide
/-- Fano triple {3,4,7}: `e₃·e₄ = e₇` (sign +1) under F3. -/
theorem fanoTriple_oriented_347 : Omul (e 3) (e 4) = e 7 := by decide
/-- Fano triple {3,5,6}: `e₃·e₆ = e₅` (sign +1) under F3 (F3-induced orientation). -/
theorem fanoTriple_oriented_356 : Omul (e 3) (e 6) = e 5 := by decide

/-- **The 7 oriented Fano triples**, collected.  Each of the 7 positive triple
    mnemonics declared in the F4 doc holds with sign +1 under the F3 doubling
    product:  `e₁e₂=e₃, e₁e₄=e₅, e₁e₇=e₆, e₂e₄=e₆, e₂e₅=e₇, e₃e₄=e₇, e₃e₆=e₅`. -/
theorem fanoTriples_oriented :
    Omul (e 1) (e 2) = e 3 ∧
    Omul (e 1) (e 4) = e 5 ∧
    Omul (e 1) (e 7) = e 6 ∧
    Omul (e 2) (e 4) = e 6 ∧
    Omul (e 2) (e 5) = e 7 ∧
    Omul (e 3) (e 4) = e 7 ∧
    Omul (e 3) (e 6) = e 5 :=
  ⟨fanoTriple_oriented_123, fanoTriple_oriented_145, fanoTriple_oriented_167,
   fanoTriple_oriented_246, fanoTriple_oriented_257, fanoTriple_oriented_347,
   fanoTriple_oriented_356⟩

/-! ## 4. Witnessed refutation of the broken archive table (issue #472)

`archive/QBP_Octonion.lean::octonionMul` claims `e₁ · e₆ = +e₇`.  The F3
construction gives `e₁ · e₆ = −e₇` (one of the 18 imaginary entries on which the
archive table disagrees with F3; the archive table is non-alternative and is NOT a
valid octonion — see issue #472).  We exhibit this single disagreement as a
concrete, kernel-checked inequality so the refutation is witnessed, not asserted. -/

/-- The F3 product `e₁ · e₆ = −e₇`, contradicting the archive table's `+e₇`.
    A concrete witness that `archive/QBP_Octonion.lean::octonionMul` is not the
    F3-forced octonion (issue #472). -/
theorem archiveTable_disagrees_cd :
    Omul (e 1) (e 6) = signedBasis (-1, 7) ∧
    Omul (e 1) (e 6) ≠ signedBasis (1, 7) := by
  decide

end QBP.Foundations.FanoOrientationF3
