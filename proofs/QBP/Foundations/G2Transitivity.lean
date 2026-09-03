/-
  QBP.Foundations.G2Transitivity — genuine octonion automorphisms and transitivity
  ================================================================================

  Anchor for `PROOF-g2` (CTH inventory; FAULT-S4-005 burn-down, #620).  The anchor
  claims "G₂ = Aut(𝕆) acts transitively on the seven quaternionic subalgebras of 𝕆
  (the ZD/Fano locus)", currently backed only by a numerical Python check.

  ## What this file adds over `FanoSubalgebras.lean`

  `FanoSubalgebras.basisAuto_transitive_on_triples` already proves, by kernel
  `decide`, that for each of the seven Fano triples there is a signed-basis
  permutation `φ` (an `IsBasisAuto`) carrying the base triple `{1,2,3}` to it.  BUT
  that file's `IsBasisAuto` only asserts preservation of the **structure constants**
  `mulCoeff 3` on basis pairs; it explicitly leaves the *bilinear extension* — the
  claim that `φ` really is a multiplicative map of the algebra `CDAlg ℝ 3` — as
  "standard and not re-derived here."

  This file CLOSES that gap.  From a `SignedBasisMap φ` we build the actual induced
  ℝ-linear map `inducedMap φ : 𝕆 → 𝕆` (`Φ(eᵢ) = sgn i • e_{perm i}`) and prove, when
  `IsBasisAuto φ` holds, that `Φ` is a genuine, **bijective, unital ℝ-algebra
  homomorphism**:
    * additive and ℝ-homogeneous (linearity) — `inducedMap_add`, `inducedMap_smul`;
    * MULTIPLICATIVE ON ALL ELEMENTS `Φ(x·y) = Φ(x)·Φ(y)` — `inducedMap_mul`
      (proved by bilinear extension from the basis identity, NOT asserted);
    * unit-preserving `Φ(1) = 1` — `inducedMap_one`;
    * bijective — `inducedMap_bijective` (explicit two-sided inverse from `perm⁻¹`).
  Hence each of the seven witnesses is a genuine **automorphism** of 𝕆, and the
  concrete automorphism group Aut(𝕆) acts transitively on the seven quaternionic
  subalgebras (`g2_transitive_genuine_automorphisms`).

  ## Honesty / scope (what is NOT claimed)

  * The abstract identification `Aut(𝕆) ≅ G₂` (Cartan) is a *name*, not formalized
    here.  We prove transitivity of the concrete automorphism group of `CDAlg ℝ 3`;
    the label "G₂" and the "ZD locus" framing are the mathematical identification of
    that group and of the seven subalgebras, which this file does not formalize.
    See the ESCALATE note in the accompanying report.
  * We prove genuine automorphisms exist for the SEVEN signed-basis witnesses (which
    is all transitivity needs); we do not enumerate the full 1344-element group as
    Lean objects.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.

  Best-practices: ~/Documents/inter/lean-proof-best-practices.md,
  ~/Documents/QBP-implementor/docs/cth/proof-anchor-best-practices.md.
-/
import Mathlib.Tactic
import QBP.Foundations.FanoSubalgebras

namespace QBP.Foundations.G2Transitivity

open QBP.Foundations.CDAlg
open QBP.Foundations.CDAlg.Fano

/-! ## 1. The induced ℝ-linear map of a signed-basis map -/

/-- The ℝ-linear map on 𝕆 = `CDAlg ℝ 3` induced by a signed basis map `φ`:
    `Φ(x) = ∑ i, x_i • (sgn i • e_{perm i})`.  On basis elements it is
    `Φ(eᵢ) = sgn i • e_{perm i}` (see `inducedMap_e`). -/
noncomputable def inducedMap (φ : SignedBasisMap) (x : CDAlg ℝ 3) : CDAlg ℝ 3 :=
  ∑ i : Fin 8, x.coord i • (((φ.sgn i : ℝ)) • e (φ.perm i))

/-- `Φ(eᵢ) = sgn i • e_{perm i}`. -/
theorem inducedMap_e (φ : SignedBasisMap) (i : Fin 8) :
    inducedMap φ (e i) = (φ.sgn i : ℝ) • e (φ.perm i) := by
  unfold inducedMap
  rw [Finset.sum_eq_single i]
  · rw [e_coord]; simp
  · intro b _ hb; rw [e_coord, if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `Φ(0) = 0`. -/
theorem inducedMap_zero (φ : SignedBasisMap) : inducedMap φ (0 : CDAlg ℝ 3) = 0 := by
  unfold inducedMap; simp

/-- `Φ` is additive. -/
theorem inducedMap_add (φ : SignedBasisMap) (x y : CDAlg ℝ 3) :
    inducedMap φ (x + y) = inducedMap φ x + inducedMap φ y := by
  unfold inducedMap
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [add_coord, add_smul]

/-- `Φ` is ℝ-homogeneous. -/
theorem inducedMap_smul (φ : SignedBasisMap) (r : ℝ) (x : CDAlg ℝ 3) :
    inducedMap φ (r • x) = r • inducedMap φ x := by
  unfold inducedMap
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_coord, mul_smul]

/-- `Φ` commutes with finite sums. -/
theorem inducedMap_sum (φ : SignedBasisMap) {ι : Type*} (s : Finset ι)
    (f : ι → CDAlg ℝ 3) :
    inducedMap φ (∑ i ∈ s, f i) = ∑ i ∈ s, inducedMap φ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [inducedMap_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, inducedMap_add, ih, Finset.sum_insert ha]

/-- Basis expansion pushed through `Φ`: `Φ(x) = ∑ i, x_i • Φ(eᵢ)`. -/
theorem inducedMap_expansion (φ : SignedBasisMap) (x : CDAlg ℝ 3) :
    inducedMap φ x = ∑ i, x.coord i • inducedMap φ (e i) := by
  conv_lhs => rw [basis_expansion x]
  rw [inducedMap_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inducedMap_smul]

/-! ## 2. Multiplication vs. finite sums in `CDAlg ℝ 3` (bilinear scaffolding) -/

/-- `0 · y = 0` in `CDAlg ℝ 3`. -/
theorem cd_zero_mul (y : CDAlg ℝ 3) : (0 : CDAlg ℝ 3) * y = 0 := by
  ext k
  simp only [mul_coord, zero_coord, zero_mul, mul_zero, ite_self, Finset.sum_const_zero]

/-- `x · 0 = 0` in `CDAlg ℝ 3`. -/
theorem cd_mul_zero (x : CDAlg ℝ 3) : x * (0 : CDAlg ℝ 3) = 0 := by
  ext k
  simp only [mul_coord, zero_coord, mul_zero, ite_self, Finset.sum_const_zero]

/-- Left-distribution of `·` over a finite sum. -/
theorem cd_sum_mul {ι : Type*} (s : Finset ι) (f : ι → CDAlg ℝ 3) (y : CDAlg ℝ 3) :
    (∑ i ∈ s, f i) * y = ∑ i ∈ s, f i * y := by
  classical
  induction s using Finset.induction with
  | empty => simp [cd_zero_mul]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, mul_add_left, ih, Finset.sum_insert ha]

/-- Right-distribution of `·` over a finite sum. -/
theorem cd_mul_sum {ι : Type*} (s : Finset ι) (x : CDAlg ℝ 3) (g : ι → CDAlg ℝ 3) :
    x * (∑ j ∈ s, g j) = ∑ j ∈ s, x * g j := by
  classical
  induction s using Finset.induction with
  | empty => simp [cd_mul_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, mul_add_right, ih, Finset.sum_insert ha]

/-- Product of two scalar-weighted finite sums expands to the double sum
    (index-generic, so it matches sums over `Fin (2^3)` produced by
    `basis_expansion` as well as over `Fin 8`). -/
theorem cd_smul_sum_mul_smul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (u : ι → CDAlg ℝ 3) (v : κ → CDAlg ℝ 3) :
    (∑ i, a i • u i) * (∑ j, b j • v j)
      = ∑ i, ∑ j, (a i * b j) • (u i * v j) := by
  rw [cd_sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cd_mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_left, mul_smul_right, smul_smul]

/-- Basis expansion of a product: `x·y = ∑ i, ∑ j, (x_i y_j) • (eᵢ·e_j)`. -/
theorem cd_prod_expansion (x y : CDAlg ℝ 3) :
    x * y = ∑ i, ∑ j, (x.coord i * y.coord j) • (e i * e j) := by
  have hbil := cd_smul_sum_mul_smul_sum x.coord y.coord (fun i => e i) (fun j => e j)
  rw [← basis_expansion x, ← basis_expansion y] at hbil
  exact hbil

/-! ## 3. `Φ` is a genuine unital ℝ-algebra homomorphism (when `IsBasisAuto φ`) -/

/-- **Multiplicativity on basis elements.**  For an octonion basis automorphism `φ`,
    `Φ(eᵢ·e_j) = Φ(eᵢ)·Φ(e_j)`.  This is where the `IsBasisAuto` structure-constant
    and XOR-additivity conditions are actually consumed to produce a multiplicative
    identity among *elements* of `CDAlg ℝ 3` (not merely among `mulCoeff` values). -/
theorem inducedMap_mul_basis (φ : SignedBasisMap) (h : IsBasisAuto φ) (i j : Fin 8) :
    inducedMap φ (e i * e j) = inducedMap φ (e i) * inducedMap φ (e j) := by
  obtain ⟨_, _, _, _, hxor, hstruct⟩ := h
  rw [e_mul_e, inducedMap_smul, inducedMap_e, inducedMap_e, inducedMap_e,
      mul_smul_left, mul_smul_right, e_mul_e, hxor i j,
      smul_smul, smul_smul, smul_smul]
  congr 1
  have hsR : (↑(φ.sgn i) : ℝ) * ↑(φ.sgn j) * ↑(mulCoeff 3 (φ.perm i) (φ.perm j))
      = (↑(φ.sgn (i ^^^ j)) : ℝ) * ↑(mulCoeff 3 i j) := by
    exact_mod_cast hstruct i j
  rw [mul_comm (↑(mulCoeff 3 i j) : ℝ), ← hsR]

/-- **Multiplicativity on ALL elements.**  For an octonion basis automorphism `φ`,
    `Φ(x·y) = Φ(x)·Φ(y)` for every `x, y ∈ 𝕆`.  Proved by bilinear extension of
    `inducedMap_mul_basis` — the "standard extension" `FanoSubalgebras` left implicit
    is here fully carried out in the kernel. -/
theorem inducedMap_mul (φ : SignedBasisMap) (h : IsBasisAuto φ) (x y : CDAlg ℝ 3) :
    inducedMap φ (x * y) = inducedMap φ x * inducedMap φ y := by
  calc inducedMap φ (x * y)
      = ∑ i, ∑ j, (x.coord i * y.coord j)
                    • (inducedMap φ (e i) * inducedMap φ (e j)) := by
        rw [cd_prod_expansion x y, inducedMap_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inducedMap_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [inducedMap_smul, inducedMap_mul_basis φ h]
    _ = inducedMap φ x * inducedMap φ y := by
        rw [inducedMap_expansion φ x, inducedMap_expansion φ y]
        exact (cd_smul_sum_mul_smul_sum x.coord y.coord
          (fun i => inducedMap φ (e i)) (fun j => inducedMap φ (e j))).symm

/-- **Unit preservation.**  `Φ(1) = 1`. -/
theorem inducedMap_one (φ : SignedBasisMap) (h : IsBasisAuto φ) :
    inducedMap φ (1 : CDAlg ℝ 3) = 1 := by
  obtain ⟨hp0, hs0, _, _, _, _⟩ := h
  rw [one_def, inducedMap_e, hp0, hs0, Int.cast_one, one_smul]

/-- `Φ` is a unital ℝ-algebra homomorphism of 𝕆: additive, ℝ-homogeneous,
    multiplicative, unit-preserving.  (Packaged as a proposition since `CDAlg ℝ 3`
    is deliberately not a `Ring`/`Algebra` instance — 𝕆 is non-associative.) -/
def IsAlgHom (Φ : CDAlg ℝ 3 → CDAlg ℝ 3) : Prop :=
  (∀ x y, Φ (x + y) = Φ x + Φ y) ∧
  (∀ (r : ℝ) x, Φ (r • x) = r • Φ x) ∧
  (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
  Φ 1 = 1

/-- **Each octonion basis automorphism `φ` induces a genuine unital ℝ-algebra
    homomorphism of 𝕆.** -/
theorem inducedMap_isAlgHom (φ : SignedBasisMap) (h : IsBasisAuto φ) :
    IsAlgHom (inducedMap φ) :=
  ⟨inducedMap_add φ, inducedMap_smul φ, inducedMap_mul φ h, inducedMap_one φ h⟩

/-! ## 4. Bijectivity via the inverse signed-basis map -/

/-- The inverse signed-basis map: invert the permutation, carry the signs along.
    `ψ.perm = perm⁻¹`, `ψ.sgn k = sgn (perm⁻¹ k)`.  (`ψ` need not itself satisfy
    `IsBasisAuto`; it is used only as the ℝ-linear inverse of `Φ`.) -/
noncomputable def invMap (φ : SignedBasisMap) (h : IsBasisAuto φ) : SignedBasisMap where
  perm := (Equiv.ofBijective φ.perm h.2.2.2.1).symm
  sgn := fun k => φ.sgn ((Equiv.ofBijective φ.perm h.2.2.2.1).symm k)

/-- Signs are `±1`, hence square to `1` in ℝ. -/
theorem sgn_sq_one (φ : SignedBasisMap) (h : IsBasisAuto φ) (i : Fin 8) :
    (φ.sgn i : ℝ) * (φ.sgn i : ℝ) = 1 := by
  rcases h.2.2.1 i with hh | hh <;> rw [hh] <;> norm_num

/-- `Φ⁻¹ ∘ Φ = id` on basis elements. -/
theorem invMap_e_leftInv (φ : SignedBasisMap) (h : IsBasisAuto φ) (i : Fin 8) :
    inducedMap (invMap φ h) (inducedMap φ (e i)) = e i := by
  rw [inducedMap_e, inducedMap_smul, inducedMap_e]
  have hp : (invMap φ h).perm (φ.perm i) = i :=
    (Equiv.ofBijective φ.perm h.2.2.2.1).symm_apply_apply i
  have hs : (invMap φ h).sgn (φ.perm i) = φ.sgn i :=
    congrArg φ.sgn ((Equiv.ofBijective φ.perm h.2.2.2.1).symm_apply_apply i)
  rw [hp, hs, smul_smul, sgn_sq_one φ h i, one_smul]

/-- `Φ ∘ Φ⁻¹ = id` on basis elements. -/
theorem invMap_e_rightInv (φ : SignedBasisMap) (h : IsBasisAuto φ) (k : Fin 8) :
    inducedMap φ (inducedMap (invMap φ h) (e k)) = e k := by
  rw [inducedMap_e, inducedMap_smul, inducedMap_e]
  have hp : φ.perm ((invMap φ h).perm k) = k :=
    (Equiv.ofBijective φ.perm h.2.2.2.1).apply_symm_apply k
  have hs : (invMap φ h).sgn k = φ.sgn ((invMap φ h).perm k) := rfl
  rw [hp, hs, smul_smul, sgn_sq_one φ h ((invMap φ h).perm k), one_smul]

/-- `Φ⁻¹` is a genuine left inverse of `Φ` on all of 𝕆. -/
theorem invMap_leftInverse (φ : SignedBasisMap) (h : IsBasisAuto φ) (x : CDAlg ℝ 3) :
    inducedMap (invMap φ h) (inducedMap φ x) = x := by
  have hx : inducedMap (invMap φ h) (inducedMap φ x) = ∑ i, x.coord i • e i := by
    rw [inducedMap_expansion φ x, inducedMap_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inducedMap_smul, invMap_e_leftInv φ h i]
  rw [hx, ← basis_expansion]

/-- `Φ⁻¹` is a genuine right inverse of `Φ` on all of 𝕆. -/
theorem invMap_rightInverse (φ : SignedBasisMap) (h : IsBasisAuto φ) (x : CDAlg ℝ 3) :
    inducedMap φ (inducedMap (invMap φ h) x) = x := by
  have hx : inducedMap φ (inducedMap (invMap φ h) x) = ∑ i, x.coord i • e i := by
    rw [inducedMap_expansion (invMap φ h) x, inducedMap_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inducedMap_smul, invMap_e_rightInv φ h i]
  rw [hx, ← basis_expansion]

/-- **`Φ` is bijective.**  With `inducedMap_isAlgHom`, each of the seven witnesses is
    a genuine *automorphism* of 𝕆 (bijective unital ℝ-algebra homomorphism). -/
theorem inducedMap_bijective (φ : SignedBasisMap) (h : IsBasisAuto φ) :
    Function.Bijective (inducedMap φ) :=
  ⟨Function.LeftInverse.injective (invMap_leftInverse φ h),
   Function.RightInverse.surjective (invMap_rightInverse φ h)⟩

/-! ## 5. Transitivity by genuine automorphisms (the `PROOF-g2` content) -/

/-- **Aut(𝕆) acts transitively on the seven quaternionic subalgebras, by genuine
    automorphisms.**  For every Fano triple `T`, there is a signed-basis map `φ` whose
    induced map `Φ = inducedMap φ` is a **bijective unital ℝ-algebra homomorphism** of
    𝕆 = `CDAlg ℝ 3` carrying the base subalgebra `{1,2,3}` to `T`
    (`actTriple φ (1,2,3) = idxSet T`).

    This upgrades `FanoSubalgebras.basisAuto_transitive_on_triples` from a
    structure-constant statement to a statement about genuine automorphisms: the
    discrete choice of quaternionic subalgebra is a single orbit of the concrete
    automorphism group of 𝕆 — pure gauge.  (The identification of that group with the
    named Lie group G₂, and of the seven subalgebras with the "ZD locus", is a
    standard but here-unformalized labelling — see the report's ESCALATE note.) -/
theorem g2_transitive_genuine_automorphisms :
    ∀ T ∈ fanoTriples, ∃ φ : SignedBasisMap,
      IsAlgHom (inducedMap φ) ∧
      Function.Bijective (inducedMap φ) ∧
      actTriple φ (1, 2, 3) = idxSet T := by
  intro T hT
  obtain ⟨φ, hφauto, hφact⟩ := basisAuto_transitive_on_triples T hT
  exact ⟨φ, inducedMap_isAlgHom φ hφauto, inducedMap_bijective φ hφauto, hφact⟩

/-! ## 6. Completeness audit — `#print axioms` -/

#print axioms inducedMap_e
#print axioms inducedMap_add
#print axioms inducedMap_smul
#print axioms inducedMap_mul_basis
#print axioms inducedMap_mul
#print axioms inducedMap_one
#print axioms inducedMap_isAlgHom
#print axioms inducedMap_bijective
#print axioms g2_transitive_genuine_automorphisms

end QBP.Foundations.G2Transitivity
