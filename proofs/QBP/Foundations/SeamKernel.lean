/-
  QBP.Foundations.SeamKernel
  ==========================

  **Does multiplication in 𝕊 delete information?**  The black-hole-spike critique
  asks whether the QBP substrate's own operations can destroy state.  This file
  answers the algebraic half of that question exactly, for the Cayley–Dickson
  sedenions 𝕊 = `CDAlg ℝ 4`.

  The results, in plain mathematics:

  * **The loss is real but thin.**  For the seam witness `x = e₁ + e₁₀` (one leg in
    each Cayley–Dickson copy of 𝕆), left multiplication `L_x : y ↦ x·y` has a
    kernel of dimension EXACTLY 4 and rank EXACTLY 12 — `seam_finrank_ker_eq_four`,
    `seam_finrank_range_eq_twelve`.  The kernel is spanned by the four explicit
    signed basis pairs `k₁ = e₇+e₁₂`, `k₂ = e₆−e₁₃`, `k₃ = e₅+e₁₄`, `k₄ = e₄−e₁₅`.
  * **Left and right loss coincide** on this witness: the same four vectors are
    annihilated on the other side (`kᵢ·x = 0`), and in fact
    `ker L_x = ker R_x` exactly, both equal to that 4-plane
    (`zd_witness_kernels_coincide`, via `seamR_ker_eq`).
  * **The lost directions are not an algebra.**  `k₁·k₁ = −2·1` and `k₁·k₃ = −2(e₂+e₉)`
    both leave the 4-plane (`zd_witness_kernel_not_subalgebra`), so the "deleted"
    subspace is not closed under the operation that deletes it.  Sharper, and also
    proved: `k1_sq : k₁·k₁ = (−2)•1` puts that escaped product on the REAL SCALAR
    LINE `ℝ·1` — the escape is not merely out of the 4-plane, it lands in ℝ.
  * **Aggregate norm is preserved — for EVERY element, zero divisor or not.**
    `Σ_j N(x·e_j) = 16·N(x)` holds for all `x : CDAlg ℝ 4` (`sum_N_mul_basis_eq`,
    re-exporting `NoAutonomousDynamics.sum_N_mul_basis`); specialised to the seam
    witness it gives `32` (`zd_witness_frobenius_preserved`).  Because the identity
    is witness-independent it is BLIND to the kernel: aggregate norm preservation
    therefore cannot be read as preservation of information.
  * **The encoding copy never deletes, on either side.**  For a NONZERO element of
    the low Cayley–Dickson copy of 𝕆 — hypotheses `cdHi x = 0` and `x ≠ 0` — both
    left multiplication `y ↦ x·y` and right multiplication `y ↦ y·x` are INJECTIVE
    (`octonion_copy_mul_injective`, `octonion_copy_mul_injective_right`).

  ## What this file does NOT prove

  The bullets above are to be read narrowly.  None of the following is established
  here, and none of it should be cited from this file.

  * **Nothing here says multiplication is the seam's physical operation.**  `*` is
    the algebra's operation.  That it is what the seam physically *does* is an
    interpretation: the substrate's dynamics is not fixed by anything on the
    ledger, and choosing it is exactly the open question (#635 — the dynamics is
    the rule).  Every theorem below is a statement about `CDAlg ℝ 4`, full stop.
  * **Nothing here is about the flow.**  No evolution, no trajectory, no
    backward-uniqueness or reversibility claim appears anywhere in this file.
  * **The kernel facts are for ONE witness.**  `seamL_ker_eq`, `finrank = 4`,
    `ker L_x = ker R_x`, the not-a-subalgebra escapes and the Frobenius value `32`
    are proved for `x = e₁ + e₁₀` and for no other element.  They are NOT proved
    for the other 83 basis-sum zero divisors `eₐ ± e_b` (`a ∈ 1..7`, `b ∈ 9..15`),
    and NOT for the zero-divisor locus of 𝕊 at large.  Any uniformity over the
    seam is, as far as this file is concerned, unproven.
  * **The converse of TARGET 5 is NOT proved.**  What is proved is one direction:
    nonzero elements of the LOW copy (`cdHi x = 0`) annihilate nothing.  The mirror
    case `cdLo x = 0` — the high copy — is entirely uncovered, so the universal
    reading "only cross-copy (seam) elements can annihilate" does NOT follow from
    anything here.  Note that sedenion non-alternativity blocks the easy argument
    "nonzero norm ⇒ invertible", so this is a real gap, not a formality.
  * **The singular values of `L_x` are NOT proved.**  `zd_witness_frobenius_preserved`
    gives the trace `Σσ² = 32` and nothing finer.  How the surviving directions
    scale — numerically `σ = 2` (×4), `√2` (×8), `0` (×4) — is NOT established in
    this file, so no statement of the form "the 4 lost directions are compensated
    by 4 directions of gain" is supported by it.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom, covering every declaration in the file.
-/
import QBP.Foundations.Breakdown
import QBP.Foundations.CrystalHosting
import QBP.Foundations.CDDimension

namespace QBP.Foundations.SeamKernel

open QBP.Foundations.CDAlg
open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.SedenionOctonionCount
open Module

/-! ## 0. Finite-dimensionality of the carrier

`CDAlg ℝ n` has the standard coordinate basis (`CDDimension.cdBasis`), hence is
finite dimensional.  Needed for rank–nullity. -/

instance instFiniteDimensionalCDAlg (n : ℕ) : FiniteDimensional ℝ (CDAlg ℝ n) :=
  Module.Finite.of_basis (CDDimension.cdBasis n)

/-! ## 1. Signed basis pairs

Every vector in this file is a signed sum of two basis vectors, `eₐ + s·e_b` with
`s = ±1`.  Writing them in the single shape `sbp a b s` lets the `Breakdown`
formal bridge `prodIsZero_iff_cdAlg_mul_eq_zero` decide each product identity by
kernel `decide` against the provenance-pinned sedenion sign table. -/

/-- A signed basis pair `eₐ + s·e_b` in 𝕊 = `CDAlg ℝ 4`. -/
def sbp (a b : Fin 16) (s : Int) : CDAlg ℝ 4 := e a + (s : ℝ) • e b

@[simp] theorem sbp_coord (a b : Fin 16) (s : Int) (k : Fin 16) :
    (sbp a b s).coord k = (if k = a then (1:ℝ) else 0) + (s : ℝ) * (if k = b then 1 else 0) :=
  rfl

/-- `eₐ + s·e_b ≠ 0` when `a ≠ b`: its `a`-coordinate is `1`. -/
theorem sbp_ne_zero (a b : Fin 16) (s : Int) (hab : a ≠ b) : sbp a b s ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : CDAlg ℝ 4 => z.coord a) h
  simp only [sbp_coord, zero_coord, if_neg hab] at h1
  norm_num at h1

/-- Products of signed basis pairs vanish exactly when the kernel-checked sign-table
    proxy says so.  A direct restatement of the `Breakdown` formal bridge. -/
theorem sbp_mul_eq_zero_iff (a b c d : Fin 16) (sb sd : Int) :
    sbp a b sb * sbp c d sd = 0 ↔ prodIsZero [(1, a), (sb, b)] [(1, c), (sd, d)] :=
  (QBP.Foundations.Breakdown.prodIsZero_iff_cdAlg_mul_eq_zero a b c d sb sd).symm

/-! ## 2. The seam witness and the four kernel directions

`x = e₁ + e₁₀` is the lexicographically first basis-sum zero divisor of 𝕊 with one
index in `1..7` (the low 𝕆 copy) and one in `9..15` (the high copy).  Its left
kernel is computed below to be exactly `span{k₁,k₂,k₃,k₄}`. -/

/-- The seam witness `x = e₁ + e₁₀ : CDAlg ℝ 4`.  One leg in each 𝕆 copy. -/
def seamX : CDAlg ℝ 4 := sbp 1 10 1
/-- First kernel direction `k₁ = e₇ + e₁₂`. -/
def k1 : CDAlg ℝ 4 := sbp 7 12 1
/-- Second kernel direction `k₂ = e₆ − e₁₃`. -/
def k2 : CDAlg ℝ 4 := sbp 6 13 (-1)
/-- Third kernel direction `k₃ = e₅ + e₁₄`. -/
def k3 : CDAlg ℝ 4 := sbp 5 14 1
/-- Fourth kernel direction `k₄ = e₄ − e₁₅`. -/
def k4 : CDAlg ℝ 4 := sbp 4 15 (-1)

/-- The witness and the four kernel directions are genuinely nonzero, so none of
    the statements below is vacuous.  (Independence, `seamKer_linearIndependent`,
    re-proves this for the `kᵢ`; these are kept as the direct, cheap form and are
    audited in §10 with everything else.) -/
theorem seamX_ne_zero : seamX ≠ 0 := sbp_ne_zero 1 10 1 (by decide)
theorem k1_ne_zero : k1 ≠ 0 := sbp_ne_zero 7 12 1 (by decide)
theorem k2_ne_zero : k2 ≠ 0 := sbp_ne_zero 6 13 (-1) (by decide)
theorem k3_ne_zero : k3 ≠ 0 := sbp_ne_zero 5 14 1 (by decide)
theorem k4_ne_zero : k4 ≠ 0 := sbp_ne_zero 4 15 (-1) (by decide)

/-! ### 2a. `x·kᵢ = 0` — the four left-kernel witnesses -/

theorem seamX_mul_k1 : seamX * k1 = 0 := (sbp_mul_eq_zero_iff 1 10 7 12 1 1).mpr (by decide)
theorem seamX_mul_k2 : seamX * k2 = 0 := (sbp_mul_eq_zero_iff 1 10 6 13 1 (-1)).mpr (by decide)
theorem seamX_mul_k3 : seamX * k3 = 0 := (sbp_mul_eq_zero_iff 1 10 5 14 1 1).mpr (by decide)
theorem seamX_mul_k4 : seamX * k4 = 0 := (sbp_mul_eq_zero_iff 1 10 4 15 1 (-1)).mpr (by decide)

/-! ### 2b. `kᵢ·x = 0` — the SAME four vectors on the other side -/

theorem k1_mul_seamX : k1 * seamX = 0 := (sbp_mul_eq_zero_iff 7 12 1 10 1 1).mpr (by decide)
theorem k2_mul_seamX : k2 * seamX = 0 := (sbp_mul_eq_zero_iff 6 13 1 10 (-1) 1).mpr (by decide)
theorem k3_mul_seamX : k3 * seamX = 0 := (sbp_mul_eq_zero_iff 5 14 1 10 1 1).mpr (by decide)
theorem k4_mul_seamX : k4 * seamX = 0 := (sbp_mul_eq_zero_iff 4 15 1 10 (-1) 1).mpr (by decide)

/-! ## 3. Linear independence of the four kernel directions

`k₁,…,k₄` are supported on the pairwise-disjoint index pairs `{7,12}, {6,13},
{5,14}, {4,15}`, so a vanishing combination is killed coordinate by coordinate. -/

/-- Explicit-coefficient independence: `a·k₁ + b·k₂ + c·k₃ + d·k₄ = 0 ⟹ a=b=c=d=0`. -/
theorem seamKer_indep_explicit (a b c d : ℝ)
    (h : a • k1 + b • k2 + c • k3 + d • k4 = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h7 := congrArg (fun z : CDAlg ℝ 4 => z.coord 7) h
  have h6 := congrArg (fun z : CDAlg ℝ 4 => z.coord 6) h
  have h5 := congrArg (fun z : CDAlg ℝ 4 => z.coord 5) h
  have h4 := congrArg (fun z : CDAlg ℝ 4 => z.coord 4) h
  simp only [k1, k2, k3, k4, add_coord, smul_coord, sbp_coord, zero_coord] at h7 h6 h5 h4
  norm_num +decide at h7 h6 h5 h4
  exact ⟨h7, h6, h5, h4⟩

/-- The four kernel directions are linearly independent over ℝ. -/
theorem seamKer_linearIndependent : LinearIndependent ℝ ![k1, k2, k3, k4] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hg
  obtain ⟨a, b, c, d⟩ := seamKer_indep_explicit (g 0) (g 1) (g 2) (g 3) hg
  intro i
  fin_cases i <;> assumption

/-- The 4-plane of lost directions, as a submodule. -/
noncomputable def seamKerSpan : Submodule ℝ (CDAlg ℝ 4) :=
  Submodule.span ℝ (Set.range ![k1, k2, k3, k4])

theorem finrank_seamKerSpan : finrank ℝ seamKerSpan = 4 := by
  rw [seamKerSpan, finrank_span_eq_card seamKer_linearIndependent, Fintype.card_fin]

/-! ## 4. The exact left kernel of `L_x`

`L_x` is a signed-permutation-coupled system: coordinate `k` of `x·y` reads
`mulCoeff 4 1 (1⊕k)·y_{1⊕k} + mulCoeff 4 10 (10⊕k)·y_{10⊕k}`.  Since `(1⊕k)⊕(10⊕k)
= 11` for every `k`, the 16 equations decouple into eight 2×2 blocks on the index
pairs `{p, p⊕11}`.  Four blocks are invertible (those coordinates must vanish) and
four are rank-1 (giving the four kernel directions). -/

/-- `x = e₁ + e₁₀` as a plain sum of basis vectors. -/
theorem seamX_eq : seamX = e (1 : Fin 16) + e (10 : Fin 16) := by
  rw [seamX, sbp]; norm_num

/-- Coordinatewise action of `L_x` on an arbitrary sedenion. -/
theorem seamX_mul_coord (y : CDAlg ℝ 4) (k : Fin 16) :
    (seamX * y).coord k
      = (mulCoeff 4 1 ((1 : Fin 16) ^^^ k) : ℝ) * y.coord ((1 : Fin 16) ^^^ k)
        + (mulCoeff 4 10 ((10 : Fin 16) ^^^ k) : ℝ) * y.coord ((10 : Fin 16) ^^^ k) := by
  rw [seamX_eq, mul_add_left, add_coord, e_mul_coord, e_mul_coord]

/-- Exhaustive case split on a `Fin 16` index, in literal (`OfNat`) form — used so
    that the coordinate atoms in the case goals are syntactically the same numerals
    as in the sixteen linear equations below. -/
theorem fin16_cases : ∀ j : Fin (2^4),
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
    j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by decide

/-- One of the sixteen linear equations imposed by `x·y = 0`, with the index
    arithmetic and the two sign-table entries supplied by kernel `decide`. -/
theorem seam_eq_at (y : CDAlg ℝ 4) (hy : seamX * y = 0) (k p q : Fin 16) (sp sq : Int)
    (h1 : (1 : Fin 16) ^^^ k = p) (h2 : (10 : Fin 16) ^^^ k = q)
    (c1 : mulCoeff 4 1 p = sp) (c2 : mulCoeff 4 10 q = sq) :
    (sp : ℝ) * y.coord p + (sq : ℝ) * y.coord q = 0 := by
  have hk := congrArg (fun z : CDAlg ℝ 4 => z.coord k) hy
  simp only [zero_coord] at hk
  rw [seamX_mul_coord, h1, h2, c1, c2] at hk
  exact hk

/-- **The left kernel is contained in the 4-plane.**  Every `y` with `x·y = 0` is
    the explicit combination `y₇·k₁ + y₆·k₂ + y₅·k₃ + y₄·k₄`. -/
theorem seam_ker_subset (y : CDAlg ℝ 4) (hy : seamX * y = 0) :
    y = (y.coord 7) • k1 + (y.coord 6) • k2 + (y.coord 5) • k3 + (y.coord 4) • k4 := by
  have E0 := seam_eq_at y hy 0 1 10 (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  have E1 := seam_eq_at y hy 1 0 11 1 (-1) (by decide) (by decide) (by decide) (by decide)
  have E2 := seam_eq_at y hy 2 3 8 (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  have E3 := seam_eq_at y hy 3 2 9 1 1 (by decide) (by decide) (by decide) (by decide)
  have E4 := seam_eq_at y hy 4 5 14 (-1) 1 (by decide) (by decide) (by decide) (by decide)
  have E5 := seam_eq_at y hy 5 4 15 1 1 (by decide) (by decide) (by decide) (by decide)
  have E6 := seam_eq_at y hy 6 7 12 1 (-1) (by decide) (by decide) (by decide) (by decide)
  have E7 := seam_eq_at y hy 7 6 13 (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  have E8 := seam_eq_at y hy 8 9 2 (-1) 1 (by decide) (by decide) (by decide) (by decide)
  have E9 := seam_eq_at y hy 9 8 3 1 (-1) (by decide) (by decide) (by decide) (by decide)
  have E10 := seam_eq_at y hy 10 11 0 1 1 (by decide) (by decide) (by decide) (by decide)
  have E11 := seam_eq_at y hy 11 10 1 (-1) 1 (by decide) (by decide) (by decide) (by decide)
  push_cast at E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
  ext k
  rcases fin16_cases k with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [k1, k2, k3, k4, add_coord, smul_coord, sbp_coord] <;>
    norm_num +decide <;>
    linarith

/-! ## 5. `L_x` as a linear map; rank and nullity -/

/-- Left multiplication by `x` on 𝕊, as an ℝ-linear endomorphism. -/
def seamL : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 4 where
  toFun y := seamX * y
  map_add' y z := mul_add_right seamX y z
  map_smul' r y := mul_smul_right r seamX y

@[simp] theorem seamL_apply (y : CDAlg ℝ 4) : seamL y = seamX * y := rfl

/-- **The left kernel of `L_x` is EXACTLY the 4-plane `span{k₁,k₂,k₃,k₄}`.** -/
theorem seamL_ker_eq : LinearMap.ker seamL = seamKerSpan := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker, seamL_apply] at hy
    rw [seam_ker_subset y hy]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rw [seamKerSpan, Submodule.span_le]
    rintro v ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, seamL_apply]
    fin_cases i
    · exact seamX_mul_k1
    · exact seamX_mul_k2
    · exact seamX_mul_k3
    · exact seamX_mul_k4

/-- **TARGET 1 (nullity).**  `dim ker L_x = 4`. -/
theorem seam_finrank_ker_eq_four : finrank ℝ (LinearMap.ker seamL) = 4 := by
  rw [seamL_ker_eq]; exact finrank_seamKerSpan

/-- **TARGET 1 (rank).**  `rank L_x = 12`: left multiplication by the seam witness
    loses exactly a 4-dimensional subspace out of 16, keeping 12. -/
theorem seam_finrank_range_eq_twelve : finrank ℝ (LinearMap.range seamL) = 12 := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := CDAlg ℝ 4) seamL
  rw [seam_finrank_ker_eq_four, CDDimension.finrank_cdAlg] at h
  omega

/-- **TARGET 1, packaged.**  Four explicit linearly independent vectors annihilated
    by `x`, and the loss is exactly 4-dimensional (equivalently rank 12). -/
theorem zd_witness_left_kernel_four :
    seamX ≠ 0 ∧
    (seamX * k1 = 0 ∧ seamX * k2 = 0 ∧ seamX * k3 = 0 ∧ seamX * k4 = 0) ∧
    LinearIndependent ℝ ![k1, k2, k3, k4] ∧
    finrank ℝ (LinearMap.ker seamL) = 4 ∧
    finrank ℝ (LinearMap.range seamL) = 12 :=
  ⟨seamX_ne_zero, ⟨seamX_mul_k1, seamX_mul_k2, seamX_mul_k3, seamX_mul_k4⟩,
    seamKer_linearIndependent, seam_finrank_ker_eq_four, seam_finrank_range_eq_twelve⟩

/-! ## 6. TARGET 2 — the right kernel contains (hence equals) the left kernel -/

/-- Right multiplication by `x` on 𝕊, as an ℝ-linear endomorphism. -/
def seamR : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 4 where
  toFun y := y * seamX
  map_add' y z := mul_add_left y z seamX
  map_smul' r y := mul_smul_left r y seamX

@[simp] theorem seamR_apply (y : CDAlg ℝ 4) : seamR y = y * seamX := rfl

/-- The 4-plane sits inside the RIGHT kernel as well. -/
theorem seamKerSpan_le_ker_seamR : seamKerSpan ≤ LinearMap.ker seamR := by
  rw [seamKerSpan, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, seamR_apply]
  fin_cases i
  · exact k1_mul_seamX
  · exact k2_mul_seamX
  · exact k3_mul_seamX
  · exact k4_mul_seamX

/-- Coordinatewise action of `R_x` on an arbitrary sedenion. -/
theorem seamX_rmul_coord (y : CDAlg ℝ 4) (k : Fin 16) :
    (y * seamX).coord k
      = (mulCoeff 4 ((1 : Fin 16) ^^^ k) 1 : ℝ) * y.coord ((1 : Fin 16) ^^^ k)
        + (mulCoeff 4 ((10 : Fin 16) ^^^ k) 10 : ℝ) * y.coord ((10 : Fin 16) ^^^ k) := by
  rw [seamX_eq, mul_add_right, add_coord, mul_e_coord, mul_e_coord]

/-- One of the sixteen linear equations imposed by `y·x = 0`. -/
theorem seam_req_at (y : CDAlg ℝ 4) (hy : y * seamX = 0) (k p q : Fin 16) (sp sq : Int)
    (h1 : (1 : Fin 16) ^^^ k = p) (h2 : (10 : Fin 16) ^^^ k = q)
    (c1 : mulCoeff 4 p 1 = sp) (c2 : mulCoeff 4 q 10 = sq) :
    (sp : ℝ) * y.coord p + (sq : ℝ) * y.coord q = 0 := by
  have hk := congrArg (fun z : CDAlg ℝ 4 => z.coord k) hy
  simp only [zero_coord] at hk
  rw [seamX_rmul_coord, h1, h2, c1, c2] at hk
  exact hk

/-- **The RIGHT kernel is contained in the same 4-plane.** -/
theorem seam_rker_subset (y : CDAlg ℝ 4) (hy : y * seamX = 0) :
    y = (y.coord 7) • k1 + (y.coord 6) • k2 + (y.coord 5) • k3 + (y.coord 4) • k4 := by
  have E0 := seam_req_at y hy 0 1 10 (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  have E1 := seam_req_at y hy 1 0 11 1 1 (by decide) (by decide) (by decide) (by decide)
  have E2 := seam_req_at y hy 2 3 8 1 1 (by decide) (by decide) (by decide) (by decide)
  have E3 := seam_req_at y hy 3 2 9 (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  have E4 := seam_req_at y hy 4 5 14 1 (-1) (by decide) (by decide) (by decide) (by decide)
  have E5 := seam_req_at y hy 5 4 15 (-1) (-1) (by decide) (by decide) (by decide) (by decide)
  have E6 := seam_req_at y hy 6 7 12 (-1) 1 (by decide) (by decide) (by decide) (by decide)
  have E7 := seam_req_at y hy 7 6 13 1 1 (by decide) (by decide) (by decide) (by decide)
  have E8 := seam_req_at y hy 8 9 2 1 (-1) (by decide) (by decide) (by decide) (by decide)
  have E9 := seam_req_at y hy 9 8 3 (-1) 1 (by decide) (by decide) (by decide) (by decide)
  have E10 := seam_req_at y hy 10 11 0 (-1) 1 (by decide) (by decide) (by decide) (by decide)
  have E11 := seam_req_at y hy 11 10 1 1 (-1) (by decide) (by decide) (by decide) (by decide)
  push_cast at E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
  ext k
  rcases fin16_cases k with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [k1, k2, k3, k4, add_coord, smul_coord, sbp_coord] <;>
    norm_num +decide <;>
    linarith

/-- **The right kernel of `R_x` is EXACTLY the same 4-plane.** -/
theorem seamR_ker_eq : LinearMap.ker seamR = seamKerSpan := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker, seamR_apply] at hy
    rw [seam_rker_subset y hy]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · exact seamKerSpan_le_ker_seamR

/-- **TARGET 2.**  The four vectors annihilated on the left by the seam witness are
    annihilated on the right by it too, and the two kernels are EQUAL — both are the
    4-plane `span{k₁,k₂,k₃,k₄}`, of dimension exactly 4.  Left-deletion and
    right-deletion destroy literally the same information. -/
theorem zd_witness_kernels_coincide :
    (k1 * seamX = 0 ∧ k2 * seamX = 0 ∧ k3 * seamX = 0 ∧ k4 * seamX = 0) ∧
    LinearMap.ker seamL = LinearMap.ker seamR ∧
    finrank ℝ (LinearMap.ker seamR) = 4 := by
  refine ⟨⟨k1_mul_seamX, k2_mul_seamX, k3_mul_seamX, k4_mul_seamX⟩, ?_, ?_⟩
  · rw [seamL_ker_eq, seamR_ker_eq]
  · rw [seamR_ker_eq]; exact finrank_seamKerSpan

/-! ## 7. TARGET 3 — the lost 4-plane is NOT closed under multiplication -/

/-- The coordinate-0 functional, used to certify escape from the 4-plane. -/
def coord0 : CDAlg ℝ 4 →ₗ[ℝ] ℝ where
  toFun z := z.coord 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate-2 functional, used to certify escape from the 4-plane. -/
def coord2 : CDAlg ℝ 4 →ₗ[ℝ] ℝ where
  toFun z := z.coord 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every element of the 4-plane has vanishing `e₀` and `e₂` coordinates. -/
theorem seamKerSpan_flat : seamKerSpan ≤ LinearMap.ker coord0 ⊓ LinearMap.ker coord2 := by
  rw [seamKerSpan, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, LinearMap.mem_ker] <;>
    fin_cases i <;>
    simp only [coord0, coord2, LinearMap.coe_mk, AddHom.coe_mk, k1, k2, k3, k4] <;>
    norm_num +decide

/-- `k₁·k₁ = (−2)•1`: the square of a lost direction lands on the REAL SCALAR LINE
    `ℝ·1 ⊆ 𝕊`.  This is a proved fact and is stronger than "outside the 4-plane":
    a product of two deleted directions is not merely elsewhere in 𝕊, it is a real
    multiple of the identity (and hence has nonzero `e₀`-coordinate, which is how
    the escape is certified below).  Nothing further is claimed — in particular
    this says nothing about products of the other `kᵢ` pairs. -/
theorem k1_sq : k1 * k1 = (-2 : ℝ) • (1 : CDAlg ℝ 4) := by
  have h := cdAlg_sq_eq (n := 4) k1
  have hre : k1.coord 0 = 0 := by simp only [k1, sbp_coord]; norm_num +decide
  have hN : N k1 = 2 := by
    rw [k1, sbp]
    have : ((1 : Int) : ℝ) • (e (12 : Fin 16) : CDAlg ℝ 4) = e (12 : Fin 16) := by norm_num
    rw [this]
    exact QBP.Foundations.Breakdown.N_e_add_e (n := 4) 7 12 (by decide)
  rw [hre, hN] at h
  rw [h]
  module

/-- `(k₁·k₃).coord 2 = −2`: the product of two DISTINCT lost directions also escapes
    the 4-plane.  Read off the genuine `CDAlg ℝ 4` product via the `Breakdown`
    per-coordinate bridge, whose value is a kernel `decide` on the sign table. -/
theorem k1_mul_k3_coord2 : (k1 * k3).coord 2 = (-2 : ℝ) := by
  have h := QBP.Foundations.Breakdown.cdAlg_mul_coord_eq_prodCoeff 7 12 5 14 1 1 2
  have hv : prodCoeff [(1, (7:Fin 16)), (1, (12:Fin 16))]
      [(1, (5:Fin 16)), (1, (14:Fin 16))] 2 = -2 := by decide
  rw [hv] at h
  rw [k1, k3, sbp, sbp]
  rw [h]
  norm_num

/-- **TARGET 3.**  The 4-dimensional space of directions deleted by the seam witness
    `x = e₁ + e₁₀` is NOT a subalgebra: both `k₁·k₁` and `k₁·k₃` leave it.  So the
    "lost" subspace is not closed under the operation that deletes it.

    Stronger, and proved separately as `k1_sq`: `k₁·k₁ = (−2)•1` lands on the real
    scalar line `ℝ·1`, i.e. this escaped product is a real multiple of the
    identity.  Claimed for this witness only; nothing is asserted about the other
    83 basis-sum zero divisors. -/
theorem zd_witness_kernel_not_subalgebra :
    k1 * k1 ∉ seamKerSpan ∧ k1 * k3 ∉ seamKerSpan := by
  constructor
  · intro hmem
    have h0 : coord0 (k1 * k1) = 0 := (seamKerSpan_flat hmem).1
    rw [k1_sq] at h0
    simp only [coord0, LinearMap.coe_mk, AddHom.coe_mk, smul_coord, one_coord] at h0
    norm_num at h0
  · intro hmem
    have h2 : coord2 (k1 * k3) = 0 := (seamKerSpan_flat hmem).2
    simp only [coord2, LinearMap.coe_mk, AddHom.coe_mk] at h2
    rw [k1_mul_k3_coord2] at h2
    norm_num at h2

/-! ## 8. TARGET 4 — the Frobenius trace identity, and why it is NOT information
conservation

`Σ_j N(t·e_j) = 16·N(t)` is `NoAutonomousDynamics.sum_N_mul_basis`, and it holds
for EVERY `t : CDAlg ℝ 4` — zero divisor or not.  It is therefore blind to the
kernel: the witness `x = e₁+e₁₀` has a 4-dimensional kernel and still satisfies it.
That blindness is the point.  Aggregate (Frobenius) norm preservation is a trace
statement and says nothing about which directions survive, so it must not be read
as conservation of information. -/

/-- `N(x) = 2` for the seam witness. -/
theorem N_seamX : N seamX = 2 := by
  rw [seamX_eq]
  exact QBP.Foundations.Breakdown.N_e_add_e (n := 4) 1 10 (by decide)

/-- The Frobenius trace identity `Σ_{j<16} N(x·e_j) = 16·N(x)`, stated here for
    EVERY `x : CDAlg ℝ 4`.  A re-export of `NoAutonomousDynamics.sum_N_mul_basis`,
    recorded in this file because its generality is the load-bearing part: the
    identity does not know whether `x` is a zero divisor. -/
theorem sum_N_mul_basis_eq (x : CDAlg ℝ 4) :
    (∑ j : Fin (2^4), N (x * e j)) = 16 * N x :=
  sum_N_mul_basis x

/-- **TARGET 4.**  For the seam witness, `Σ_{j<16} N(x·e_j) = 16·N(x) = 32`: the
    squared Frobenius norm of `L_x` is `32` even though `L_x` has a 4-dimensional
    kernel.

    What this does NOT show: how the 12 surviving directions scale.  The statement
    is a trace, `Σσ² = 32`; the singular values themselves (numerically `σ = 2`
    with multiplicity 4, `√2` with multiplicity 8, `0` with multiplicity 4) are NOT
    proved here, so no "4 lost directions compensated by 4 directions of gain"
    claim may be cited from this theorem.  Note also (`sum_N_mul_basis_eq`) that
    the first conjunct holds for every element of 𝕊, so it is not a fact about
    zero divisors at all. -/
theorem zd_witness_frobenius_preserved :
    (∑ j : Fin (2^4), N (seamX * e j)) = 16 * N seamX ∧
    (∑ j : Fin (2^4), N (seamX * e j)) = 32 := by
  have h := sum_N_mul_basis_eq seamX
  refine ⟨h, ?_⟩
  rw [h, N_seamX]; norm_num

/-! ## 9. TARGET 5 — nonzero elements of the octonion encoding copy never delete

Throughout this section the hypotheses are explicit and both are needed:
`cdHi x = 0` (`x` lies in the low Cayley–Dickson copy of 𝕆) and `x ≠ 0`.

For such an `x = (o, 0)` with `o ≠ 0`, the doubling formula gives, for `y = (c, d)`,
`x·y = (o·c, d·o)` and `y·x = (c·o, d·ō)`.  Every component is an octonion product
with the nonzero factor `o` (or its conjugate, of the same norm), and 𝕆 is a
composition algebra with a positive-definite norm form, so each vanishes only if
`c = d = 0`.  Hence BOTH `L_x` and `R_x` are injective.

What is NOT proved here: the converse.  The mirror hypothesis `cdLo x = 0` (the
high copy) is not treated anywhere in this file, so "only cross-copy — seam —
elements can annihilate" is an open universal, not a consequence of these
theorems.  Sedenion non-alternativity means it cannot be waved through by
"nonzero norm ⇒ invertible". -/

/-- The low-copy product rule (LEFT): if `cdHi x = 0` then
    `cdLo (x·y) = cdLo x · cdLo y`. -/
theorem cdLo_mul_of_lo {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (y : CDAlg ℝ 4) :
    cdLo (x * y) = cdLo x * cdLo y := by
  rw [cdLo_mul, hhi, alt_mul_zero, sub_zero]

/-- The high-copy product rule (LEFT): if `cdHi x = 0` then
    `cdHi (x·y) = cdHi y · cdLo x`. -/
theorem cdHi_mul_of_lo {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (y : CDAlg ℝ 4) :
    cdHi (x * y) = cdHi y * cdLo x := by
  rw [cdHi_mul, hhi, alt_zero_mul, add_zero]

/-- A nonzero element of the low copy has nonzero octonion part. -/
theorem cdLo_ne_zero_of_lo {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (hx : x ≠ 0) : cdLo x ≠ 0 := by
  intro h
  apply hx
  rw [← alt_N_eq_zero_iff, N_split x, h, hhi, N_zero]; ring

/-- **TARGET 5 (left).**  If `cdHi x = 0` and `x ≠ 0` then `x·y = 0 → y = 0`:
    a NONZERO element of the octonion encoding copy annihilates nothing on the
    left.  (The converse — that only seam elements can annihilate — is not proved;
    see the section header.) -/
theorem octonion_copy_mul_eq_zero_imp {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (hx : x ≠ 0)
    (y : CDAlg ℝ 4) (h : x * y = 0) : y = 0 := by
  have ho : cdLo x ≠ 0 := cdLo_ne_zero_of_lo hhi hx
  have hoN : N (cdLo x) ≠ 0 := fun hz => ho (alt_N_eq_zero_iff (cdLo x) |>.mp hz)
  -- low component: cdLo x · cdLo y = 0
  have hlo : cdLo x * cdLo y = 0 := by
    rw [← cdLo_mul_of_lo hhi y, h, QBP.Foundations.CrystalHosting.cdLo_zero]
  have hcy : cdLo y = 0 := by
    rw [← alt_N_eq_zero_iff]
    have := octonion_norm_composition (cdLo x) (cdLo y)
    rw [hlo, N_zero] at this
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact absurd h1 hoN
    · exact h1
  -- high component: cdHi y · cdLo x = 0
  have hhi2 : cdHi y * cdLo x = 0 := by rw [← cdHi_mul_of_lo hhi y, h, cdHi_zero]
  have hdy : cdHi y = 0 := by
    rw [← alt_N_eq_zero_iff]
    have := octonion_norm_composition (cdHi y) (cdLo x)
    rw [hhi2, N_zero] at this
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact h1
    · exact absurd h1 hoN
  rw [← alt_N_eq_zero_iff, N_split y, hcy, hdy, N_zero]; ring

/-- **TARGET 5, injectivity form (LEFT).**  For `x` with `cdHi x = 0` and `x ≠ 0`
    — a nonzero element of the low 𝕆 encoding copy — the map `y ↦ x·y` is injective
    on all of 𝕊: left multiplication by such an `x` loses nothing. -/
theorem octonion_copy_mul_injective {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (hx : x ≠ 0) :
    Function.Injective (fun y : CDAlg ℝ 4 => x * y) := by
  intro y z hyz
  have hyz' : x * y = x * z := hyz
  have hsub : x * (y - z) = 0 := by
    rw [QBP.Foundations.CrystalHosting.cd_mul_sub, hyz', sub_self]
  exact sub_eq_zero.mp (octonion_copy_mul_eq_zero_imp hhi hx (y - z) hsub)

/-! ### 9a. The right-multiplication twin -/

/-- The low-copy product rule (RIGHT): if `cdHi x = 0` then
    `cdLo (y·x) = cdLo y · cdLo x`. -/
theorem cdLo_mul_of_lo_right {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (y : CDAlg ℝ 4) :
    cdLo (y * x) = cdLo y * cdLo x := by
  rw [cdLo_mul, hhi, cd_conj_zero, alt_zero_mul, sub_zero]

/-- The high-copy product rule (RIGHT): if `cdHi x = 0` then
    `cdHi (y·x) = cdHi y · conj (cdLo x)`. -/
theorem cdHi_mul_of_lo_right {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (y : CDAlg ℝ 4) :
    cdHi (y * x) = cdHi y * conj (cdLo x) := by
  rw [cdHi_mul, hhi, alt_zero_mul, zero_add]

/-- **TARGET 5 (right).**  If `cdHi x = 0` and `x ≠ 0` then `y·x = 0 → y = 0`.
    Same hypotheses as the left case; the conjugate appearing in the high component
    is harmless because `N (conj z) = N z`. -/
theorem octonion_copy_mul_eq_zero_imp_right {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (hx : x ≠ 0)
    (y : CDAlg ℝ 4) (h : y * x = 0) : y = 0 := by
  have ho : cdLo x ≠ 0 := cdLo_ne_zero_of_lo hhi hx
  have hoN : N (cdLo x) ≠ 0 := fun hz => ho (alt_N_eq_zero_iff (cdLo x) |>.mp hz)
  -- low component: cdLo y · cdLo x = 0
  have hlo : cdLo y * cdLo x = 0 := by
    rw [← cdLo_mul_of_lo_right hhi y, h, QBP.Foundations.CrystalHosting.cdLo_zero]
  have hcy : cdLo y = 0 := by
    rw [← alt_N_eq_zero_iff]
    have := octonion_norm_composition (cdLo y) (cdLo x)
    rw [hlo, N_zero] at this
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact h1
    · exact absurd h1 hoN
  -- high component: cdHi y · conj (cdLo x) = 0
  have hhi2 : cdHi y * conj (cdLo x) = 0 := by
    rw [← cdHi_mul_of_lo_right hhi y, h, cdHi_zero]
  have hdy : cdHi y = 0 := by
    rw [← alt_N_eq_zero_iff]
    have := octonion_norm_composition (cdHi y) (conj (cdLo x))
    rw [hhi2, N_zero, N_conj] at this
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact h1
    · exact absurd h1 hoN
  rw [← alt_N_eq_zero_iff, N_split y, hcy, hdy, N_zero]; ring

/-- **TARGET 5, injectivity form (RIGHT).**  For `x` with `cdHi x = 0` and `x ≠ 0`,
    the map `y ↦ y·x` is injective on all of 𝕊.  Together with
    `octonion_copy_mul_injective` this makes TARGET 5 two-sided: nonzero elements
    of the octonion encoding copy delete nothing under LEFT or RIGHT
    multiplication.  The converse remains unproved (section header). -/
theorem octonion_copy_mul_injective_right {x : CDAlg ℝ 4} (hhi : cdHi x = 0) (hx : x ≠ 0) :
    Function.Injective (fun y : CDAlg ℝ 4 => y * x) := by
  intro y z hyz
  have hyz' : y * x = z * x := hyz
  have hsub : (y - z) * x = 0 := by
    rw [QBP.Foundations.CrystalHosting.cd_sub_mul, hyz', sub_self]
  exact sub_eq_zero.mp (octonion_copy_mul_eq_zero_imp_right hhi hx (y - z) hsub)

/-! ### 9b. The witness is not in the encoding copy -/

/-- The seam witness is NOT in the low copy (`cdHi (e₁+e₁₀) ≠ 0`), so it is outside
    the reach of the two injectivity theorems above — consistent with its having a
    4-dimensional kernel.  This is a consistency check, NOT a converse: it does not
    show that being off the low copy is what makes deletion possible. -/
theorem seamX_not_in_octonion_copy : cdHi seamX ≠ 0 := by
  intro h
  have h2 := congrArg (fun z : CDAlg ℝ 3 => z.coord 2) h
  simp only [cdHi_coord, hiIdx, seamX, sbp_coord, zero_coord] at h2
  norm_num +decide at h2

/-! ## 10. Completeness audit — `#print axioms`

Every declaration in this file is listed below; each must depend only on
`{propext, Classical.choice, Quot.sound}`.  The list is exhaustive — definitions
and the `FiniteDimensional` instance included — so no declaration is unaudited. -/

#print axioms instFiniteDimensionalCDAlg
#print axioms sbp
#print axioms sbp_coord
#print axioms sbp_ne_zero
#print axioms sbp_mul_eq_zero_iff
#print axioms seamX
#print axioms k1
#print axioms k2
#print axioms k3
#print axioms k4
#print axioms seamX_ne_zero
#print axioms k1_ne_zero
#print axioms k2_ne_zero
#print axioms k3_ne_zero
#print axioms k4_ne_zero
#print axioms seamX_mul_k1
#print axioms seamX_mul_k2
#print axioms seamX_mul_k3
#print axioms seamX_mul_k4
#print axioms k1_mul_seamX
#print axioms k2_mul_seamX
#print axioms k3_mul_seamX
#print axioms k4_mul_seamX
#print axioms seamKer_indep_explicit
#print axioms seamKer_linearIndependent
#print axioms seamKerSpan
#print axioms finrank_seamKerSpan
#print axioms seamX_eq
#print axioms seamX_mul_coord
#print axioms fin16_cases
#print axioms seam_eq_at
#print axioms seam_ker_subset
#print axioms seamL
#print axioms seamL_apply
#print axioms seamL_ker_eq
#print axioms seam_finrank_ker_eq_four
#print axioms seam_finrank_range_eq_twelve
#print axioms zd_witness_left_kernel_four
#print axioms seamR
#print axioms seamR_apply
#print axioms seamKerSpan_le_ker_seamR
#print axioms seamX_rmul_coord
#print axioms seam_req_at
#print axioms seam_rker_subset
#print axioms seamR_ker_eq
#print axioms zd_witness_kernels_coincide
#print axioms coord0
#print axioms coord2
#print axioms seamKerSpan_flat
#print axioms k1_sq
#print axioms k1_mul_k3_coord2
#print axioms zd_witness_kernel_not_subalgebra
#print axioms N_seamX
#print axioms sum_N_mul_basis_eq
#print axioms zd_witness_frobenius_preserved
#print axioms cdLo_mul_of_lo
#print axioms cdHi_mul_of_lo
#print axioms cdLo_ne_zero_of_lo
#print axioms octonion_copy_mul_eq_zero_imp
#print axioms octonion_copy_mul_injective
#print axioms cdLo_mul_of_lo_right
#print axioms cdHi_mul_of_lo_right
#print axioms octonion_copy_mul_eq_zero_imp_right
#print axioms octonion_copy_mul_injective_right
#print axioms seamX_not_in_octonion_copy

end QBP.Foundations.SeamKernel
