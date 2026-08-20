/-
  QBP.Foundations.FanoSubalgebras
  ===============================

  The quaternionic (4-dimensional associative) subalgebra structure of
  𝕆 = `CDAlg ℝ 3`, and the action of the (signed-basis) automorphism group on it.
  This is the math scaffold for the crystallisation-bridge research thread
  (#539, "Strategy B"): it turns the previously *asserted* facts behind
  `QBP.Cosmo.FanoChoiceInformation.numFanoLines := 7` into kernel-checked theorems,
  and answers the gauge question — does Aut(𝕆) act transitively on the 7
  subalgebras? — for the concrete signed-basis automorphism subgroup.

  ## What is proved (all kernel `decide`, NO `native_decide`, NO `sorry`, NO `True`)

  * **AC-B2 — the 7-count** (`fanoTriples_card`): there are exactly seven
    XOR-closed imaginary index triples `{i,j,k} ⊆ {1,…,7}`.  These index the seven
    candidate 4-dimensional subspaces `span{e₀, eᵢ, e_j, e_k}` of 𝕆.

  * **AC-B2 — closure & associativity** (`fanoTriple_xor_closed`,
    `fanoTriple_associative`): each Fano triple is XOR-closed (so the spanned
    subspace is closed under the basis product) AND the octonion associator
    coefficient `assocCoeffZ 3` vanishes on every triple drawn from `{0,i,j,k}`.
    Hence each `span{e₀, eᵢ, e_j, e_k}` is a genuinely *associative* subalgebra —
    a copy of ℍ inside 𝕆.

  * **Non-vacuity** (`exists_imaginary_triple_nonassociative`): NOT every imaginary
    triple is associative — there is a concrete `(a,b,c)` with all indices
    imaginary and `assocCoeffZ 3 a b c ≠ 0`.  The associativity result above is
    therefore a real constraint that singles the seven Fano triples out, not a
    statement that holds trivially for all triples.

  * **AC-B3 — transitivity / the gauge answer** (`basisAuto_transitive_on_triples`):
    the signed-basis automorphism group of 𝕆 acts transitively on the seven Fano
    triples.  We exhibit, for each of the seven triples, an EXPLICIT signed basis
    permutation `φ(eᵢ) = sgn i • e_{perm i}` that (a) is an octonion automorphism
    (preserves the structure constant `mulCoeff 3` and is XOR-additive on indices,
    `IsBasisAuto`, kernel-checked over all 64 basis pairs) and (b) carries the base
    triple `{1,2,3}` to that triple.  Consequently the discrete choice of *which*
    quaternionic subalgebra is an automorphism-orbit of size one: it is pure gauge
    with respect to this subgroup of Aut(𝕆).

  ## Scope / honesty notes (see the report accompanying #539)

  * The automorphism group used here is the finite **signed-basis** subgroup of
    Aut(𝕆) (the subgroup of automorphisms permuting the basis up to sign).  This
    subgroup alone already acts transitively on the seven subalgebras, which is all
    the gauge conclusion needs.  Its order is 1344 = 2³·|GL₃(𝔽₂)| = 2³·168
    (verified by exhaustive enumeration during development; not asserted as a Lean
    theorem here).  The full continuous group Aut(𝕆) ≅ G₂ is a strictly larger,
    14-dimensional Lie group; that identification (Cartan) is NOT formalized — see
    the AC-B1 feasibility verdict in the report.  Transitivity for the signed-basis
    subgroup *implies* transitivity for the full G₂ (a subgroup acting transitively
    forces the overgroup to), so the gauge conclusion is not weakened by working
    with the subgroup.

  * `IsBasisAuto` checks that a signed basis permutation preserves `mulCoeff` and
    XOR-additivity.  This is exactly the condition for the induced linear map
    `eᵢ ↦ sgn i • e_{perm i}` to be a multiplicative automorphism of `CDAlg ℝ 3`
    on basis elements (and hence, by bilinearity, everywhere); the bilinear
    extension is standard and not re-derived here — the file's claims are about the
    basis-level structure constants, which is where the Fano/gauge content lives.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.  Every
  `decide` is the kernel `decide`.  `#print axioms` audit at the bottom — every main
  result depends only on `{propext, Classical.choice, Quot.sound}`.

  Best-practices: ~/Documents/inter/lean-proof-best-practices.md.
-/
import QBP.Foundations.CDLifting

namespace QBP.Foundations.CDAlg.Fano

open QBP.Foundations.CDAlg

/- The finite `decide`s below enumerate over `Finset`s of `Fin 8 × Fin 8 × Fin 8`
   (512 elements) and `8 × 8` structure-constant tables; the `Decidable`-instance
   reduction nests deeply, so we raise the elaboration recursion limit.  This is
   ELABORATION depth only — every proof term is checked by the Lean *kernel* with the
   standard three axioms (`#print axioms` audit at the bottom confirms no `sorryAx`,
   no native axiom).  A too-low `maxRecDepth` makes `decide` ABORT and silently emit
   `sorryAx`; the audit is exactly what catches that, and here it is clean. -/
set_option maxRecDepth 8000

/-! ## 1. The seven Fano triples (AC-B2: the 7-count) -/

/-- A candidate quaternionic-subalgebra index triple: an ordered `(i,j,k)` with
    `0 < i < j < k ≤ 7`, all imaginary, that is XOR-closed (`eᵢ·e_j = ± e_k`,
    i.e. `i ⊕ j = k`).  XOR-closure is precisely the condition that
    `span{e₀, eᵢ, e_j, e_k}` is closed under the basis product (the fourth basis
    element produced by any product of two of `e₀,eᵢ,e_j,e_k` lands back in the
    set, since `i⊕j=k`, `j⊕k=i`, `i⊕k=j`, and `x⊕0=x`). -/
def isFanoTriple (t : Fin 8 × Fin 8 × Fin 8) : Bool :=
  let i := t.1; let j := t.2.1; let k := t.2.2
  (i.val ≠ 0) && (j.val ≠ 0) && (k.val ≠ 0) &&
  (i.val < j.val) && (j.val < k.val) &&
  ((i ^^^ j : Fin 8) == k)

/-- The `Finset` of canonical (ordered `i<j<k`) XOR-closed imaginary triples of 𝕆.
    Each indexes a 4-dimensional associative subalgebra `span{e₀, eᵢ, e_j, e_k}`. -/
def fanoTriples : Finset (Fin 8 × Fin 8 × Fin 8) :=
  Finset.univ.filter (fun t => isFanoTriple t)

/-- **AC-B2 (the 7-count).**  𝕆 has exactly seven XOR-closed imaginary index
    triples — equivalently, exactly seven candidate 4-dimensional quaternionic
    subalgebras `span{e₀, eᵢ, e_j, e_k}`, indexed by the seven Fano lines.  Kernel
    `decide` over all `8³` ordered index triples. -/
theorem fanoTriples_card : fanoTriples.card = 7 := by decide

/-- The seven Fano triples, listed explicitly (the F4 Fano lines, cf.
    `FanoOrientationF3.fanoTriples_oriented`):
    `{1,2,3}, {1,4,5}, {1,6,7}, {2,4,6}, {2,5,7}, {3,4,7}, {3,5,6}`. -/
def fanoTripleList : List (Fin 8 × Fin 8 × Fin 8) :=
  [(1,2,3),(1,4,5),(1,6,7),(2,4,6),(2,5,7),(3,4,7),(3,5,6)]

/-- The explicit membership of `fanoTriples`: it is exactly the seven triples of
    `fanoTripleList`.  Kernel `decide`. -/
theorem fanoTriples_eq : fanoTriples = fanoTripleList.toFinset := by decide

/-! ## 2. Closure and associativity of each subalgebra (AC-B2) -/

/-- The four basis indices spanning the subalgebra of a triple: `{0, i, j, k}`. -/
def subalgIdx (t : Fin 8 × Fin 8 × Fin 8) : List (Fin 8) := [0, t.1, t.2.1, t.2.2]

/-- **XOR-closure of each Fano subalgebra.**  For every Fano triple and every pair
    of indices `a, b` drawn from `{0, i, j, k}`, the product index `a ⊕ b` is again
    in `{0, i, j, k}`.  Hence `span{e₀, eᵢ, e_j, e_k}` is closed under the basis
    product: it is a subalgebra (not merely a subspace).  Kernel `decide`. -/
theorem fanoTriple_xor_closed :
    ∀ t ∈ fanoTriples, ∀ a ∈ subalgIdx t, ∀ b ∈ subalgIdx t,
      (a ^^^ b : Fin 8) ∈ subalgIdx t := by decide

/-- **Associativity of each Fano subalgebra.**  For every Fano triple, the octonion
    associator coefficient `assocCoeffZ 3` vanishes on every ordered triple of
    indices drawn from `{0, i, j, k}`.  Since `[eₐ, e_b, e_c] = assocCoeffZ 3 a b c
    • e_{a⊕b⊕c}` (`assoc_e`), this says the associator vanishes on all of
    `span{e₀, eᵢ, e_j, e_k}` on basis elements: the subalgebra is genuinely
    ASSOCIATIVE — a copy of ℍ inside 𝕆.  Kernel `decide`. -/
theorem fanoTriple_associative :
    ∀ t ∈ fanoTriples, ∀ a ∈ subalgIdx t, ∀ b ∈ subalgIdx t, ∀ c ∈ subalgIdx t,
      assocCoeffZ 3 a b c = 0 := by decide

/-- **Non-vacuity of the associativity result.**  There exists an imaginary index
    triple `(a,b,c)` (all of `a,b,c ≠ 0`) whose octonion associator coefficient is
    NONZERO.  So `fanoTriple_associative` is a genuine constraint selecting the
    seven Fano triples — it is false that every imaginary triple associates.  (The
    associator obstruction is exactly what distinguishes a Fano line from a generic
    imaginary triple.)  Kernel `decide` exhibits the witness. -/
theorem exists_imaginary_triple_nonassociative :
    ∃ a b c : Fin 8, a.val ≠ 0 ∧ b.val ≠ 0 ∧ c.val ≠ 0 ∧ assocCoeffZ 3 a b c ≠ 0 := by
  decide

/-! ## 3. Signed-basis automorphisms and transitivity (AC-B3: the gauge answer)

A signed basis permutation `φ(eᵢ) = sgn i • e_{perm i}` of 𝕆 is an algebra
automorphism iff it fixes the unit, is XOR-additive on indices (`perm (i⊕j) =
perm i ⊕ perm j`), and preserves the structure constant in the signed sense
`sgn i · sgn j · mulCoeff 3 (perm i) (perm j) = sgn (i⊕j) · mulCoeff 3 i j`
for all basis pairs.  This is the basis-level automorphism condition; by
bilinearity it extends to a genuine multiplicative automorphism of `CDAlg ℝ 3`. -/

/-- A signed basis permutation of 𝕆's basis: `φ(eᵢ) = sgn i • e_{perm i}`. -/
structure SignedBasisMap where
  /-- The underlying index permutation. -/
  perm : Fin 8 → Fin 8
  /-- The per-index sign `∈ {±1}`. -/
  sgn  : Fin 8 → Int

/-- `φ` is an octonion basis automorphism: it fixes the unit (`perm 0 = 0`,
    `sgn 0 = 1`), every sign is `±1`, `perm` is a bijection and XOR-additive, and
    the signed structure-constant condition holds on all `8 × 8` basis pairs.  This
    is exactly the condition for `eᵢ ↦ sgn i • e_{perm i}` to extend (bilinearly)
    to an automorphism of `CDAlg ℝ 3`. -/
def IsBasisAuto (φ : SignedBasisMap) : Prop :=
  φ.perm 0 = 0 ∧ φ.sgn 0 = 1 ∧
  (∀ i : Fin 8, φ.sgn i = 1 ∨ φ.sgn i = -1) ∧
  Function.Bijective φ.perm ∧
  (∀ i j : Fin 8, (φ.perm i ^^^ φ.perm j : Fin 8) = φ.perm (i ^^^ j)) ∧
  (∀ i j : Fin 8,
    φ.sgn i * φ.sgn j * mulCoeff 3 (φ.perm i) (φ.perm j)
      = φ.sgn (i ^^^ j) * mulCoeff 3 i j)

instance (φ : SignedBasisMap) : Decidable (IsBasisAuto φ) := by
  unfold IsBasisAuto; infer_instance

/-- The index set `{i, j, k}` of a triple — the imaginary part of the spanned
    subalgebra `span{e₀, eᵢ, e_j, e_k}`.  Two triples span the same subalgebra iff
    they have the same index set, so we compare subalgebras as `Finset (Fin 8)`. -/
def idxSet (t : Fin 8 × Fin 8 × Fin 8) : Finset (Fin 8) := {t.1, t.2.1, t.2.2}

/-- The (unordered, index-level) action of a signed basis map on a triple: the
    image index set `{perm i, perm j, perm k}`.  Since an automorphism sends
    `span{e₀, eᵢ, e_j, e_k}` to `span{e₀, e_{perm i}, e_{perm j}, e_{perm k}}`,
    this is the index set of the image subalgebra. -/
def actTriple (φ : SignedBasisMap) (t : Fin 8 × Fin 8 × Fin 8) : Finset (Fin 8) :=
  {φ.perm t.1, φ.perm t.2.1, φ.perm t.2.2}

/-! ### 3a. Seven explicit automorphism witnesses

For each Fano triple `T`, an explicit `SignedBasisMap φ_T` that is a basis
automorphism (`IsBasisAuto`) and carries the base triple `{1,2,3}` to `T`.  The
underlying permutations are XOR-additive bijections fixing 0 (generated by the
images of the index basis `{1,2,4}`); the signs are the kernel-found patterns
making each an octonion automorphism.  Witnesses were located by exhaustive search
over the 1344-element signed-basis automorphism group during development; here they
are fixed data and every automorphism/orbit claim is re-checked by kernel `decide`. -/

/-- Build the XOR-additive permutation fixing 0 from the images `a,b,c` of the index
    basis `1,2,4`. -/
def fromGens (a b c : Fin 8) : Fin 8 → Fin 8 := fun i =>
  let v := (if i.val &&& 1 ≠ 0 then a.val else 0) ^^^
           (if i.val &&& 2 ≠ 0 then b.val else 0) ^^^
           (if i.val &&& 4 ≠ 0 then c.val else 0)
  ⟨v % 8, Nat.mod_lt _ (by norm_num)⟩

/-- Build a sign function from a 7-bit pattern `n` (bit `i-1` = sign of index `i`;
    sign of index 0 is `+1`). -/
def mkSgn (n : Nat) : Fin 8 → Int := fun i =>
  if i.val = 0 then 1 else if Nat.testBit n (i.val - 1) then 1 else -1

/-- Identity-permutation automorphism (the sign pattern `mkSgn 7` = all `+1` on the
    base triple's indices makes it a genuine automorphism); witness for the base
    triple `{1,2,3}` itself. -/
def auto123 : SignedBasisMap := ⟨fromGens 1 2 4, mkSgn 7⟩
/-- Automorphism carrying `{1,2,3}` to `{1,4,5}`. -/
def auto145 : SignedBasisMap := ⟨fromGens 1 4 2, mkSgn 1⟩
/-- Automorphism carrying `{1,2,3}` to `{1,6,7}`. -/
def auto167 : SignedBasisMap := ⟨fromGens 1 6 2, mkSgn 8⟩
/-- Automorphism carrying `{1,2,3}` to `{2,4,6}`. -/
def auto246 : SignedBasisMap := ⟨fromGens 2 4 1, mkSgn 4⟩
/-- Automorphism carrying `{1,2,3}` to `{2,5,7}`. -/
def auto257 : SignedBasisMap := ⟨fromGens 2 5 1, mkSgn 2⟩
/-- Automorphism carrying `{1,2,3}` to `{3,4,7}`. -/
def auto347 : SignedBasisMap := ⟨fromGens 3 4 1, mkSgn 1⟩
/-- Automorphism carrying `{1,2,3}` to `{3,5,6}`. -/
def auto356 : SignedBasisMap := ⟨fromGens 3 5 1, mkSgn 8⟩

/-- The seven witnesses, paired with the triple each one reaches from `{1,2,3}`. -/
def autoWitnesses : List (SignedBasisMap × (Fin 8 × Fin 8 × Fin 8)) :=
  [(auto123,(1,2,3)), (auto145,(1,4,5)), (auto167,(1,6,7)), (auto246,(2,4,6)),
   (auto257,(2,5,7)), (auto347,(3,4,7)), (auto356,(3,5,6))]

/-- **Each witness is a genuine octonion basis automorphism.**  For all seven
    witnesses, `IsBasisAuto` holds — the signed basis permutation preserves the
    structure constant `mulCoeff 3` on every basis pair and is an XOR-additive
    bijection fixing the unit.  Kernel `decide` (7 × 64 signed structure-constant
    checks plus the bijection/XOR conditions). -/
theorem autoWitnesses_isAuto : ∀ p ∈ autoWitnesses, IsBasisAuto p.1 := by decide

/-- **Each witness carries the base subalgebra to its target subalgebra.**  For all
    seven witnesses, the image index set `actTriple φ {1,2,3}` equals the index set
    `idxSet T` of the paired target triple `T`.  Kernel `decide`. -/
theorem autoWitnesses_act : ∀ p ∈ autoWitnesses, actTriple p.1 (1,2,3) = idxSet p.2 := by
  decide

/-- The seven target index sets reached from `{1,2,3}` are exactly the index sets
    of the seven Fano triples. -/
theorem autoWitnesses_targets_eq_fano :
    (autoWitnesses.map (fun p => idxSet p.2)).toFinset
      = (fanoTripleList.map idxSet).toFinset := by decide

/-- Individual witness facts, packaged for the transitivity proof: each `auto*` is
    an automorphism carrying the base subalgebra `{1,2,3}` to the named one. -/
theorem auto123_spec : IsBasisAuto auto123 ∧ actTriple auto123 (1,2,3) = idxSet (1,2,3) := by
  exact ⟨by decide, by decide⟩
theorem auto145_spec : IsBasisAuto auto145 ∧ actTriple auto145 (1,2,3) = idxSet (1,4,5) := by
  exact ⟨by decide, by decide⟩
theorem auto167_spec : IsBasisAuto auto167 ∧ actTriple auto167 (1,2,3) = idxSet (1,6,7) := by
  exact ⟨by decide, by decide⟩
theorem auto246_spec : IsBasisAuto auto246 ∧ actTriple auto246 (1,2,3) = idxSet (2,4,6) := by
  exact ⟨by decide, by decide⟩
theorem auto257_spec : IsBasisAuto auto257 ∧ actTriple auto257 (1,2,3) = idxSet (2,5,7) := by
  exact ⟨by decide, by decide⟩
theorem auto347_spec : IsBasisAuto auto347 ∧ actTriple auto347 (1,2,3) = idxSet (3,4,7) := by
  exact ⟨by decide, by decide⟩
theorem auto356_spec : IsBasisAuto auto356 ∧ actTriple auto356 (1,2,3) = idxSet (3,5,6) := by
  exact ⟨by decide, by decide⟩

/-- **AC-B3 (the gauge answer): the signed-basis automorphism group acts
    transitively on the seven quaternionic subalgebras.**  For every Fano triple
    `T`, there is a signed basis automorphism `φ` of 𝕆 (`IsBasisAuto φ`) carrying
    the base subalgebra `{1,2,3}` to `T`: the image index set `actTriple φ {1,2,3}`
    equals `idxSet T`.

    Interpretation for the crystallisation bridge: the discrete choice of *which*
    quaternionic subalgebra (equivalently, which Fano line) is a single
    automorphism orbit.  It is therefore **pure gauge** with respect to Aut(𝕆) —
    no automorphism-invariant observable can distinguish the seven subalgebras.
    (Proved for the signed-basis subgroup, which is enough: a subgroup acting
    transitively forces the full G₂ to act transitively.) -/
theorem basisAuto_transitive_on_triples :
    ∀ T ∈ fanoTriples,
      ∃ φ : SignedBasisMap, IsBasisAuto φ ∧ actTriple φ (1,2,3) = idxSet T := by
  intro T hT
  rw [fanoTriples_eq, List.mem_toFinset] at hT
  simp only [fanoTripleList, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with h|h|h|h|h|h|h <;> subst h
  · exact ⟨auto123, auto123_spec.1, auto123_spec.2⟩
  · exact ⟨auto145, auto145_spec.1, auto145_spec.2⟩
  · exact ⟨auto167, auto167_spec.1, auto167_spec.2⟩
  · exact ⟨auto246, auto246_spec.1, auto246_spec.2⟩
  · exact ⟨auto257, auto257_spec.1, auto257_spec.2⟩
  · exact ⟨auto347, auto347_spec.1, auto347_spec.2⟩
  · exact ⟨auto356, auto356_spec.1, auto356_spec.2⟩

/-! ## 4. Completeness audit — `#print axioms` -/

#print axioms fanoTriples_card
#print axioms fanoTriples_eq
#print axioms fanoTriple_xor_closed
#print axioms fanoTriple_associative
#print axioms exists_imaginary_triple_nonassociative
#print axioms autoWitnesses_isAuto
#print axioms autoWitnesses_act
#print axioms autoWitnesses_targets_eq_fano
#print axioms basisAuto_transitive_on_triples

end QBP.Foundations.CDAlg.Fano
