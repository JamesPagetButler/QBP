/-
  QBP.Foundations.CDDimension — dim Im 𝒜_{2a} = 2^(2a) − 1 (CD tower identity)
  ===========================================================================

  Anchor for #466 item 2 (paper §IX.B, `CONV-cd-tower-in-zeta-moments`): the
  imaginary subspace of the level-`n` Cayley–Dickson algebra has real
  dimension `2^n − 1`, so along the EVEN tower (n = 2a) it is `2^(2a) − 1` —
  the algebraic pre-factor of the CCvS entropy coefficients γ(−a):

      a = 1, n = 2:  𝒜₂ = ℍ,  dim Im ℍ  =  3 = 2² − 1
      a = 2, n = 4:  𝒜₄ = 𝕊,  dim Im 𝕊  = 15 = 2⁴ − 1
      a = 3, n = 6:  𝒜₆ (64-dim), dim Im 𝒜₆ = 63 = 2⁶ − 1

  This is NOT stated as the vacuous numeric identity `2^(2a) − 1 = 2^(2a) − 1`.
  The content is anchored to the `CDAlg` carrier of `CDAlg.lean`:

  * `coordEquiv` — `CDAlg ℝ n ≃ₗ[ℝ] (Fin (2^n) → ℝ)`, giving the standard
    basis `cdBasis` via `Basis.ofEquivFun` (whose vectors are exactly the
    `CDAlg.e i`).
  * `finrank_cdAlg` — `finrank ℝ (CDAlg ℝ n) = 2^n`.
  * `ImSubmodule`  — the span of the imaginary basis vectors `{e i | i ≠ 0}`.
  * `finrank_imSubmodule` — `finrank ℝ (Im (CDAlg ℝ n)) = 2^n − 1` (genuine
    linear algebra: the imaginary basis vectors are linearly independent, and
    there are `2^n − 1` of them).
  * `even_tower_imDim` — the even-tower instance `2^(2a) − 1`, with the three
    CCvS anchor values 3, 15, 63 as corollaries.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import QBP.Foundations.CDAlg

namespace QBP.Foundations.CDDimension

open QBP.Foundations.CDAlg Module Submodule

variable (n : ℕ)

/-! ## 1. The coordinate linear equivalence and standard basis -/

/-- `CDAlg ℝ n` is linearly equivalent to `Fin (2^n) → ℝ` via its coordinates. -/
def coordEquiv : CDAlg ℝ n ≃ₗ[ℝ] (Fin (2^n) → ℝ) where
  toFun x := x.coord
  invFun c := ⟨c⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The standard basis of `CDAlg ℝ n`, indexed by `Fin (2^n)`. -/
noncomputable def cdBasis : Basis (Fin (2^n)) ℝ (CDAlg ℝ n) :=
  Basis.ofEquivFun (coordEquiv n)

/-- The basis vectors of `cdBasis` are exactly the `CDAlg.e i`. -/
theorem cdBasis_eq_e (i : Fin (2^n)) : cdBasis n i = (e i : CDAlg ℝ n) := by
  classical
  rw [cdBasis, Basis.coe_ofEquivFun]
  ext j
  rw [e_coord]
  exact Pi.single_apply i (1:ℝ) j

/-- **Total dimension:** `dim (CDAlg ℝ n) = 2^n`. -/
theorem finrank_cdAlg : finrank ℝ (CDAlg ℝ n) = 2^n := by
  rw [finrank_eq_card_basis (cdBasis n), Fintype.card_fin]

/-! ## 2. The imaginary subspace and its dimension -/

/-- The imaginary subspace `Im (CDAlg ℝ n)`: the span of the non-real basis
    vectors `{e i | i ≠ 0}` (all coordinates except the real unit `e 0`). -/
def ImSubmodule : Submodule ℝ (CDAlg ℝ n) :=
  span ℝ (Set.range (fun i : {i : Fin (2^n) // i ≠ 0} => (e i.val : CDAlg ℝ n)))

/-- The full family `e i` is linearly independent (it is a basis). -/
theorem e_linearIndependent :
    LinearIndependent ℝ (fun i : Fin (2^n) => (e i : CDAlg ℝ n)) := by
  have h := (cdBasis n).linearIndependent
  have heq : (fun i : Fin (2^n) => (e i : CDAlg ℝ n)) = ⇑(cdBasis n) := by
    funext i; rw [cdBasis_eq_e]
  rw [heq]
  exact h

/-- The imaginary basis vectors are linearly independent (subfamily of a
    basis along the injective inclusion `{i // i ≠ 0} ↪ Fin (2^n)`). -/
theorem e_im_linearIndependent :
    LinearIndependent ℝ
      (fun i : {i : Fin (2^n) // i ≠ 0} => (e i.val : CDAlg ℝ n)) :=
  (e_linearIndependent n).comp Subtype.val Subtype.val_injective

/-- There are `2^n − 1` imaginary basis directions. -/
theorem card_im_index : Fintype.card {i : Fin (2^n) // i ≠ 0} = 2^n - 1 := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq (0 : Fin (2^n)),
    Fintype.card_fin]

/-- **Imaginary dimension (general CD level):**
    `dim Im (CDAlg ℝ n) = 2^n − 1`. -/
theorem finrank_imSubmodule : finrank ℝ (ImSubmodule n) = 2^n - 1 := by
  rw [ImSubmodule, finrank_span_eq_card (e_im_linearIndependent n), card_im_index]

/-! ## 3. The even Cayley–Dickson tower (the CCvS pre-factor `2^(2a) − 1`)

The CCvS entropy coefficients γ(−a) carry the algebraic pre-factor
`2^(2a) − 1`, which is exactly the imaginary dimension of the level-`2a`
(even-tower) Cayley–Dickson algebra — skipping the odd levels 𝕆 (n = 3)
and the 32-dim n = 5 algebra.  See `SpectralMoments.lean` for the γ(−a)
formula side of this identity. -/

/-- **Even-tower imaginary dimension:** for every `a`,
    `dim Im (CDAlg ℝ (2a)) = 2^(2a) − 1`. -/
theorem even_tower_imDim (a : ℕ) :
    finrank ℝ (ImSubmodule (2*a)) = 2^(2*a) - 1 :=
  finrank_imSubmodule (2*a)

/-- a = 1: `dim Im ℍ = 3` (`CDAlg ℝ 2` is the quaternion level). -/
theorem imDim_quaternion : finrank ℝ (ImSubmodule 2) = 3 := by
  rw [finrank_imSubmodule]; norm_num

/-- a = 2: `dim Im 𝕊 = 15` (`CDAlg ℝ 4` is the sedenion level). -/
theorem imDim_sedenion : finrank ℝ (ImSubmodule 4) = 15 := by
  rw [finrank_imSubmodule]; norm_num

/-- a = 3: `dim Im 𝒜₆ = 63` (the 64-dimensional level-6 CD algebra). -/
theorem imDim_level_six : finrank ℝ (ImSubmodule 6) = 63 := by
  rw [finrank_imSubmodule]; norm_num

/-! ## Completeness audit — `#print axioms` -/

#print axioms finrank_cdAlg
#print axioms finrank_imSubmodule
#print axioms even_tower_imDim
#print axioms imDim_quaternion
#print axioms imDim_sedenion
#print axioms imDim_level_six

end QBP.Foundations.CDDimension
