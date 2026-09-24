/-
  QBP.Foundations.SeamSpectrum
  ============================

  **What does left multiplication by a sedenion zero divisor actually do to the
  16 directions of 𝕊?**  `SeamKernel` answered the *kernel* half for the seam
  witness `z = e₁ + e₁₀`: a 4-dimensional loss, rank 12, left kernel = right
  kernel = `span{e₇+e₁₂, e₆−e₁₃, e₅+e₁₄, e₄−e₁₅}`.  It explicitly disclaimed the
  rest of the spectrum ("The singular values of `L_x` are NOT proved").  This file
  proves them, and the two ridge identities that go with them.

  The results, in plain mathematics (𝕊 = `CDAlg ℝ 4`, `N` = the Euclidean norm
  form, `bil` = its polar inner product):

  * **`L_z` is skew-adjoint** (`seamL_skew`), so the Gram operator `L_zᵀL_z` is
    literally `−L_z²`.  `seamGram_eq` states exactly that: `⟨L_z y, L_z w⟩ =
    ⟨y, G w⟩` with `G := −L_z∘L_z`.  No adjoint has to be postulated.
  * **Spectrum.**  `ℝ¹⁶ = T ⊕ M ⊕ K` with `G = 4` on `T` (dim 4), `2` on `M`
    (dim 8), `0` on `K` (dim 4) — singular values `2 (×4)`, `√2 (×8)`, `0 (×4)`
    for `L_z`.  Each eigenspace is identified EXACTLY, not merely contained:
    `seamEig_four_eq` (`= topSpan`), `seamEig_two_eq` (`= midSpan`),
    `seamEig_zero_eq` (`= seamKerSpan`), with dimensions 4/8/4
    (`finrank_seamEig_*`) summing to 16.  The list is also COMPLETE: `G` satisfies
    `G(G−2)(G−4) = 0` (`seamG_cubic`), so no other real number is an eigenvalue
    (`seamEig_eq_bot_of_ne`); packaged as `seam_gram_spectrum_exhaustive`.
  * **The top plane is `span{e₄+e₁₅, e₅−e₁₄, e₆+e₁₃, e₇−e₁₂}`** and it is the
    kernel of the OTHER sign of the same seam plane:
    `topSpan = ker L_{e₁−e₁₀}` (`seamLm_ker_eq`), i.e. the attack-2 identity
    `T(e₁+e₁₀) = K(e₁−e₁₀)`.
  * **Every nonzero element of the top plane is a two-sided zero divisor**
    (`top_plane_zero_divisor`) — annihilated on both sides by the single element
    `e₁ − e₁₀`.  So the top plane lies on the zero-divisor ridge, and
    quantitatively `V(t) = N(t)²` on it (`top_plane_on_ridge`), where
    `V(x) = ‖[cdLo x, cdHi x]‖²` is the attack-2 potential.  This DERIVES, for the
    canonical zero divisors, the property `NoAutonomousDynamics` could only record
    as OBSERVED ("the top singular subspace lies on the ridge V = 1 … observed for
    100/100 t, NOT derived").
  * **RIGHT multiplication has the SAME Gram operator** (§6).  `(x·z)·z = z·(z·x)`
    for every `x` and for both signs `z = e₁ ± e₁₀` (`seam_gram_lr`,
    `seam_gram_lr_m`) — a sign-table identity, not a formal consequence, since 𝕊 is
    neither associative nor alternative.  Hence `R_zᵀR_z = L_zᵀL_z`
    (`seamGR_eq_seamG`) and `R_z` has the identical spectrum on the identical
    eigenspaces (`seamR_gram_spectrum`); also `ker R_{z₋} = topSpan`
    (`seamRm_ker_eq`), so the top plane is annihilated by `z₋` on either side.
  * **Uniform over all 84 basis-sum zero divisors** (indeed over every pair of
    basis units `e_a, e_b`): `N(z₊·x) + N(z₋·x) = 4·N(x)` for `z± = e_a ± e_b`
    (`N_basisPair_split`).  Hence `N(z₊·x) ≤ 4 N(x)` always — the top singular
    value of `L_{z₊}` is at most `2` — with equality EXACTLY on `ker L_{z₋}`
    (`N_basisPair_eq_iff`).  The operator form `G₊ + G₋ = 4·id`
    (`basisPair_sq_split`) is proved for every such pair too.  So "the top plane
    of one sign is the kernel of the other sign" is uniform; what is proved for
    the witness only is the *multiplicity* count 4/8/4.

  ## What this file does NOT prove

  * **The 4/8/4 multiplicities are proved for `z = e₁ + e₁₀` ONLY.**  For the other
    83 basis-sum zero divisors the uniform facts above give `spec(G) ⊆ [0,4]`,
    `E₄(G₊) = ker L_{z₋}` and `E₀(G₊) = ker L_{z₊}`, but NOT that those kernels are
    4-dimensional, and NOT that the remaining spectrum is the single value 2.  The
    numerical claim (attack-2 §2: one spectrum `{2 ×4, √2 ×8, 0 ×4}` for all 84) is
    NOT established here.
  * **Nothing about `ad_z = L_z − R_z`.**  Attack 2 reports `ad_z` singular values
    `{4 ×4, 2√2 ×6, 0 ×6}` (dims 4/6/6, a DIFFERENT decomposition from `L_z`'s
    4/8/4).  Neither the `G₊ + G₋ = 4` mechanism nor the left/right Gram identity
    `(x·z)·z = z·(z·x)` transfers to `ad` — squaring `ad_z` produces the mixed term
    `z·(x·z) + (z·x)·z`, which the sign-table identities of §6 do not control.  No
    `ad` statement is made below; that spectrum remains numerical only.
  * **No dynamics, no substrate semantics.**  Every theorem is a statement about the
    real algebra `CDAlg ℝ 4`.  `V` is defined here as a coordinate/commutator norm;
    calling it a "potential" is commentary, not content.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom, covering every declaration in the file.
-/
import QBP.Foundations.SeamKernel

namespace QBP.Foundations.SeamSpectrum

open QBP.Foundations.CDAlg
open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.SeamKernel
open Module

/-! ## 1. Basis units act as skew-adjoint anti-involutions

Two kernel-`decide` facts about the sedenion sign table drive everything: for an
imaginary basis index `m ≠ 0`,

  `mulCoeff 4 m (m ⊕ k) · mulCoeff 4 m k = −1`      (left)
  `mulCoeff 4 (m ⊕ k) m · mulCoeff 4 k m = −1`      (right)

i.e. `e_m·(e_m·y) = −y` and `(y·e_m)·e_m = −y` for every `y`, even though 𝕊 is
neither associative nor alternative. -/

/-- Sign-table fact (kernel `decide`, 256 index pairs): for every imaginary basis
    index `m`, `mulCoeff 4 m (m ⊕ k) · mulCoeff 4 m k = −1`. -/
theorem mulCoeff_left_sq :
    ∀ m k : Fin 16, m = 0 ∨ mulCoeff 4 m (m ^^^ k) * mulCoeff 4 m k = -1 := by decide

/-- Sign-table fact (kernel `decide`, 256 index pairs), right-multiplication form. -/
theorem mulCoeff_right_sq :
    ∀ m k : Fin 16, m = 0 ∨ mulCoeff 4 (m ^^^ k) m * mulCoeff 4 k m = -1 := by decide

/-- `e_m·(e_m·y) = −y` for every imaginary basis unit `e_m` and every `y ∈ 𝕊`. -/
theorem e_sq_mul (m : Fin (2^4)) (hm : m ≠ 0) (y : CDAlg ℝ 4) :
    e m * (e m * y) = -y := by
  ext k
  rw [e_mul_coord, e_mul_coord, xor_cancel_left, neg_coord]
  rcases mulCoeff_left_sq m k with h | h
  · exact absurd h hm
  · have h' : ((mulCoeff 4 m (m ^^^ k) : ℝ)) * ((mulCoeff 4 m k : ℝ)) = -1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this
      exact this
    rw [← mul_assoc, h']
    ring

/-- `(y·e_m)·e_m = −y` for every imaginary basis unit `e_m` and every `y ∈ 𝕊`. -/
theorem mul_e_sq (m : Fin (2^4)) (hm : m ≠ 0) (y : CDAlg ℝ 4) :
    (y * e m) * e m = -y := by
  ext k
  rw [mul_e_coord, mul_e_coord, xor_cancel_left, neg_coord]
  rcases mulCoeff_right_sq m k with h | h
  · exact absurd h hm
  · have h' : ((mulCoeff 4 (m ^^^ k) m : ℝ)) * ((mulCoeff 4 k m : ℝ)) = -1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this
      exact this
    rw [← mul_assoc, h']
    ring

/-- `⟨x, 0⟩ = 0`. -/
theorem bil_zero_right (x : CDAlg ℝ 4) : bil x (0 : CDAlg ℝ 4) = 0 := by
  simp only [bil_def, zero_coord, mul_zero, Finset.sum_const_zero]

/-- `⟨x, −y⟩ = −⟨x,y⟩`. -/
theorem bil_neg_right (x y : CDAlg ℝ 4) : bil x (-y) = - bil x y := by
  rw [show (-y) = (-1 : ℝ) • y by rw [neg_one_smul], bil_smul_right]
  ring

/-- **Left multiplication by a basis unit is an isometry of the inner product.**
    Polarization of `N (e_m · x) = N x` (`NoAutonomousDynamics.N_basis_mul`). -/
theorem bil_basis_mul (m : Fin (2^4)) (x y : CDAlg ℝ 4) :
    bil (e m * x) (e m * y) = bil x y := by
  have h1 := QBP.Foundations.CrossProduct.N_add (e m * x) (e m * y)
  have h2 := QBP.Foundations.CrossProduct.N_add x y
  rw [← mul_add_right, N_basis_mul, N_basis_mul, N_basis_mul] at h1
  linarith

/-- **Left multiplication by an IMAGINARY basis unit is SKEW-ADJOINT:**
    `⟨e_m·x, y⟩ = −⟨x, e_m·y⟩`.  (Immediate from the isometry property together
    with `e_m·(e_m·y) = −y`.) -/
theorem bil_basis_skew (m : Fin (2^4)) (hm : m ≠ 0) (x y : CDAlg ℝ 4) :
    bil (e m * x) y = - bil x (e m * y) := by
  have h := bil_basis_mul m x (e m * y)
  rw [e_sq_mul m hm y, bil_neg_right] at h
  linarith

/-! ## 2. Uniform facts for EVERY basis-sum pair `e_a ± e_b`

Nothing in this section is special to the witness: `a` and `b` are arbitrary
imaginary basis indices, so the statements cover all 84 basis-sum zero divisors
(and every other basis pair besides). -/

/-- `(e_a + s·e_b)·x` split into basis-unit pieces, `s = +1`. -/
theorem sbp_one_mul (a b : Fin 16) (x : CDAlg ℝ 4) :
    sbp a b 1 * x = e a * x + e b * x := by
  rw [sbp, show ((1 : ℤ) : ℝ) = 1 by norm_num, one_smul, mul_add_left]

/-- `(e_a + s·e_b)·x` split into basis-unit pieces, `s = −1`. -/
theorem sbp_neg_one_mul (a b : Fin 16) (x : CDAlg ℝ 4) :
    sbp a b (-1) * x = e a * x - e b * x := by
  rw [sbp, show (((-1 : ℤ)) : ℝ) = -1 by norm_num, neg_one_smul, ← sub_eq_add_neg,
    QBP.Foundations.CrystalHosting.cd_sub_mul]

/-- **UNIFORM SPLIT IDENTITY (all basis pairs, hence all 84 basis-sum zero
    divisors).**  For `z± = e_a ± e_b`,

      `N(z₊·x) + N(z₋·x) = 4·N(x)`   for every `x ∈ 𝕊`.

    It is the parallelogram law applied to the two isometries `e_a·` and `e_b·`. -/
theorem N_basisPair_split (a b : Fin (2^4)) (x : CDAlg ℝ 4) :
    N (sbp a b 1 * x) + N (sbp a b (-1) * x) = 4 * N x := by
  rw [sbp_one_mul, sbp_neg_one_mul, QBP.Foundations.CrossProduct.N_add,
    QBP.Foundations.CrossProduct.N_sub, N_basis_mul, N_basis_mul]
  ring

/-- **The top singular value of `L_{e_a+e_b}` is at most 2**, uniformly:
    `N((e_a+e_b)·x) ≤ 4·N(x)`. -/
theorem N_basisPair_le (a b : Fin (2^4)) (x : CDAlg ℝ 4) :
    N (sbp a b 1 * x) ≤ 4 * N x := by
  have hsplit := N_basisPair_split a b x
  have hnn : 0 ≤ N (sbp a b (-1) * x) := by
    rw [N_def]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

/-- **The maximum is attained EXACTLY on the kernel of the other sign.**
    `N((e_a+e_b)·x) = 4·N(x) ↔ (e_a−e_b)·x = 0`. -/
theorem N_basisPair_eq_iff (a b : Fin (2^4)) (x : CDAlg ℝ 4) :
    N (sbp a b 1 * x) = 4 * N x ↔ sbp a b (-1) * x = 0 := by
  have hsplit := N_basisPair_split a b x
  constructor
  · intro h
    have : N (sbp a b (-1) * x) = 0 := by linarith
    exact (alt_N_eq_zero_iff _).mp this
  · intro h
    rw [h, N_zero] at hsplit
    linarith

/-- **UNIFORM OPERATOR IDENTITY.**  For `z± = e_a ± e_b` with `a, b` imaginary,
    `z₊·(z₊·y) + z₋·(z₋·y) = −4y`, i.e. the two Gram operators add to `4·id`:
    `G₊ + G₋ = 4·id`.  (The cross terms cancel; `e_a·(e_a·y) = e_b·(e_b·y) = −y`.) -/
theorem basisPair_sq_split (a b : Fin (2^4)) (ha : a ≠ 0) (hb : b ≠ 0) (y : CDAlg ℝ 4) :
    sbp a b 1 * (sbp a b 1 * y) + sbp a b (-1) * (sbp a b (-1) * y) = (-4 : ℝ) • y := by
  rw [sbp_one_mul a b y, sbp_neg_one_mul a b y, sbp_one_mul, sbp_neg_one_mul,
    mul_add_right, mul_add_right, QBP.Foundations.CrystalHosting.cd_mul_sub,
    QBP.Foundations.CrystalHosting.cd_mul_sub, e_sq_mul a ha y, e_sq_mul b hb y]
  module

/-- **Skew-adjointness for an arbitrary basis pair** `e_a + s·e_b`. -/
theorem sbp_skew (a b : Fin (2^4)) (ha : a ≠ 0) (hb : b ≠ 0) (s : ℤ) (y w : CDAlg ℝ 4) :
    bil (sbp a b s * y) w = - bil y (sbp a b s * w) := by
  rw [sbp, mul_add_left, mul_add_left, mul_smul_left, mul_smul_left, bil_add_left,
    bil_add_right, bil_smul_left, bil_smul_right, bil_basis_skew a ha,
    bil_basis_skew b hb]
  ring

/-- **`z·(z·x) = 0 ↔ z·x = 0`** for `z = e_a + s·e_b`: the Gram operator and the
    map itself have the same kernel (skew-adjointness + positive-definiteness). -/
theorem sbp_sq_eq_zero_iff (a b : Fin (2^4)) (ha : a ≠ 0) (hb : b ≠ 0) (s : ℤ)
    (x : CDAlg ℝ 4) : sbp a b s * (sbp a b s * x) = 0 ↔ sbp a b s * x = 0 := by
  constructor
  · intro h
    have hN : N (sbp a b s * x) = 0 := by
      rw [N_eq_bil, sbp_skew a b ha hb s x (sbp a b s * x), h, bil_zero_right]
      ring
    exact (alt_N_eq_zero_iff _).mp hN
  · intro h
    rw [h, alt_mul_zero]

/-! ## 3. The two signs of the seam plane

`z₊ = e₁ + e₁₀` is `SeamKernel.seamX`; `z₋ = e₁ − e₁₀` is its partner `seamXm`.
`SeamKernel` proved `ker L_{z₊} = ker R_{z₊} = span{k₁,k₂,k₃,k₄}`; this section
computes `ker L_{z₋}` and shows it is the top plane. -/

/-- The partner witness `z₋ = e₁ − e₁₀` — the other sign of the same seam plane. -/
def seamXm : CDAlg ℝ 4 := sbp 1 10 (-1)

theorem seamXm_ne_zero : seamXm ≠ 0 := sbp_ne_zero 1 10 (-1) (by decide)

/-- First top direction `t₁ = e₄ + e₁₅`. -/
def t1 : CDAlg ℝ 4 := sbp 4 15 1
/-- Second top direction `t₂ = e₅ − e₁₄`. -/
def t2 : CDAlg ℝ 4 := sbp 5 14 (-1)
/-- Third top direction `t₃ = e₆ + e₁₃`. -/
def t3 : CDAlg ℝ 4 := sbp 6 13 1
/-- Fourth top direction `t₄ = e₇ − e₁₂`. -/
def t4 : CDAlg ℝ 4 := sbp 7 12 (-1)

theorem t1_ne_zero : t1 ≠ 0 := sbp_ne_zero 4 15 1 (by decide)
theorem t2_ne_zero : t2 ≠ 0 := sbp_ne_zero 5 14 (-1) (by decide)
theorem t3_ne_zero : t3 ≠ 0 := sbp_ne_zero 6 13 1 (by decide)
theorem t4_ne_zero : t4 ≠ 0 := sbp_ne_zero 7 12 (-1) (by decide)

/-! ### 3a. `z₋·tᵢ = 0` and `tᵢ·z₋ = 0` — each top direction is a two-sided
zero divisor, all four with the SAME partner `z₋`. -/

theorem seamXm_mul_t1 : seamXm * t1 = 0 :=
  (sbp_mul_eq_zero_iff 1 10 4 15 (-1) 1).mpr (by decide)
theorem seamXm_mul_t2 : seamXm * t2 = 0 :=
  (sbp_mul_eq_zero_iff 1 10 5 14 (-1) (-1)).mpr (by decide)
theorem seamXm_mul_t3 : seamXm * t3 = 0 :=
  (sbp_mul_eq_zero_iff 1 10 6 13 (-1) 1).mpr (by decide)
theorem seamXm_mul_t4 : seamXm * t4 = 0 :=
  (sbp_mul_eq_zero_iff 1 10 7 12 (-1) (-1)).mpr (by decide)

theorem t1_mul_seamXm : t1 * seamXm = 0 :=
  (sbp_mul_eq_zero_iff 4 15 1 10 1 (-1)).mpr (by decide)
theorem t2_mul_seamXm : t2 * seamXm = 0 :=
  (sbp_mul_eq_zero_iff 5 14 1 10 (-1) (-1)).mpr (by decide)
theorem t3_mul_seamXm : t3 * seamXm = 0 :=
  (sbp_mul_eq_zero_iff 6 13 1 10 1 (-1)).mpr (by decide)
theorem t4_mul_seamXm : t4 * seamXm = 0 :=
  (sbp_mul_eq_zero_iff 7 12 1 10 (-1) (-1)).mpr (by decide)

/-! ### 3b. The top plane as a submodule -/

/-- Explicit-coefficient independence of `t₁,…,t₄` (disjoint index supports). -/
theorem topIndep_explicit (a b c d : ℝ)
    (h : a • t1 + b • t2 + c • t3 + d • t4 = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h4 := congrArg (fun z : CDAlg ℝ 4 => z.coord 4) h
  have h5 := congrArg (fun z : CDAlg ℝ 4 => z.coord 5) h
  have h6 := congrArg (fun z : CDAlg ℝ 4 => z.coord 6) h
  have h7 := congrArg (fun z : CDAlg ℝ 4 => z.coord 7) h
  simp only [t1, t2, t3, t4, add_coord, smul_coord, sbp_coord, zero_coord] at h4 h5 h6 h7
  norm_num +decide at h4 h5 h6 h7
  exact ⟨h4, h5, h6, h7⟩

theorem top_linearIndependent : LinearIndependent ℝ ![t1, t2, t3, t4] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hg
  obtain ⟨a, b, c, d⟩ := topIndep_explicit (g 0) (g 1) (g 2) (g 3) hg
  intro i
  fin_cases i <;> assumption

/-- **The top plane** `T = span{e₄+e₁₅, e₅−e₁₄, e₆+e₁₃, e₇−e₁₂}`. -/
noncomputable def topSpan : Submodule ℝ (CDAlg ℝ 4) :=
  Submodule.span ℝ (Set.range ![t1, t2, t3, t4])

theorem finrank_topSpan : finrank ℝ topSpan = 4 := by
  rw [topSpan, finrank_span_eq_card top_linearIndependent, Fintype.card_fin]

/-! ### 3c. `ker L_{z₋}` is exactly the top plane

Same mechanism as `SeamKernel` §4: the sixteen coordinate equations of `z₋·y = 0`
decouple into eight 2×2 blocks on the index pairs `{p, p⊕11}`. -/

/-- Coordinatewise action of `L_{e_a + s·e_b}` on an arbitrary sedenion. -/
theorem sbp_mul_coord (a b : Fin 16) (s : ℤ) (y : CDAlg ℝ 4) (k : Fin 16) :
    (sbp a b s * y).coord k
      = (mulCoeff 4 a (a ^^^ k) : ℝ) * y.coord (a ^^^ k)
        + (s : ℝ) * ((mulCoeff 4 b (b ^^^ k) : ℝ) * y.coord (b ^^^ k)) := by
  rw [sbp, mul_add_left, add_coord, e_mul_coord, mul_smul_left, smul_coord, e_mul_coord]

/-- One of the sixteen linear equations imposed by `(e_a + s·e_b)·y = 0`. -/
theorem sbp_eq_at (a b : Fin 16) (s : ℤ) (y : CDAlg ℝ 4) (hy : sbp a b s * y = 0)
    (k p q : Fin 16) (sp sq : ℤ)
    (h1 : a ^^^ k = p) (h2 : b ^^^ k = q)
    (c1 : mulCoeff 4 a p = sp) (c2 : mulCoeff 4 b q = sq) :
    (sp : ℝ) * y.coord p + (s : ℝ) * ((sq : ℝ) * y.coord q) = 0 := by
  have hk := congrArg (fun z : CDAlg ℝ 4 => z.coord k) hy
  simp only [zero_coord] at hk
  rw [sbp_mul_coord, h1, h2, c1, c2] at hk
  exact hk

/-- **The kernel of `L_{z₋}` is contained in the top plane.** -/
theorem seam_mker_subset (y : CDAlg ℝ 4) (hy : seamXm * y = 0) :
    y = (y.coord 4) • t1 + (y.coord 5) • t2 + (y.coord 6) • t3 + (y.coord 7) • t4 := by
  have hy' : sbp 1 10 (-1) * y = 0 := hy
  have E0 := sbp_eq_at 1 10 (-1) y hy' 0 1 10 (-1) (-1)
    (by decide) (by decide) (by decide) (by decide)
  have E1 := sbp_eq_at 1 10 (-1) y hy' 1 0 11 1 (-1)
    (by decide) (by decide) (by decide) (by decide)
  have E2 := sbp_eq_at 1 10 (-1) y hy' 2 3 8 (-1) (-1)
    (by decide) (by decide) (by decide) (by decide)
  have E3 := sbp_eq_at 1 10 (-1) y hy' 3 2 9 1 1
    (by decide) (by decide) (by decide) (by decide)
  have E4 := sbp_eq_at 1 10 (-1) y hy' 4 5 14 (-1) 1
    (by decide) (by decide) (by decide) (by decide)
  have E5 := sbp_eq_at 1 10 (-1) y hy' 5 4 15 1 1
    (by decide) (by decide) (by decide) (by decide)
  have E6 := sbp_eq_at 1 10 (-1) y hy' 6 7 12 1 (-1)
    (by decide) (by decide) (by decide) (by decide)
  have E7 := sbp_eq_at 1 10 (-1) y hy' 7 6 13 (-1) (-1)
    (by decide) (by decide) (by decide) (by decide)
  have E8 := sbp_eq_at 1 10 (-1) y hy' 8 9 2 (-1) 1
    (by decide) (by decide) (by decide) (by decide)
  have E9 := sbp_eq_at 1 10 (-1) y hy' 9 8 3 1 (-1)
    (by decide) (by decide) (by decide) (by decide)
  have E10 := sbp_eq_at 1 10 (-1) y hy' 10 11 0 1 1
    (by decide) (by decide) (by decide) (by decide)
  have E11 := sbp_eq_at 1 10 (-1) y hy' 11 10 1 (-1) 1
    (by decide) (by decide) (by decide) (by decide)
  push_cast at E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
  ext k
  rcases fin16_cases k with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [t1, t2, t3, t4, add_coord, smul_coord, sbp_coord] <;>
    norm_num +decide <;>
    linarith

/-- Left multiplication by `z₋ = e₁ − e₁₀`, as an ℝ-linear endomorphism. -/
def seamLm : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 4 where
  toFun y := seamXm * y
  map_add' y z := mul_add_right seamXm y z
  map_smul' r y := mul_smul_right r seamXm y

@[simp] theorem seamLm_apply (y : CDAlg ℝ 4) : seamLm y = seamXm * y := rfl

/-- **ATTACK-2 IDENTITY (3):** `T(e₁+e₁₀) = K(e₁−e₁₀)` — the top plane of one sign
    of the seam plane is EXACTLY the kernel of the other sign. -/
theorem seamLm_ker_eq : LinearMap.ker seamLm = topSpan := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker, seamLm_apply] at hy
    rw [seam_mker_subset y hy]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rw [topSpan, Submodule.span_le]
    rintro v ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, seamLm_apply]
    fin_cases i
    · exact seamXm_mul_t1
    · exact seamXm_mul_t2
    · exact seamXm_mul_t3
    · exact seamXm_mul_t4

/-- Right multiplication by `z₋ = e₁ − e₁₀`, as an ℝ-linear endomorphism. -/
def seamRm : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 4 where
  toFun y := y * seamXm
  map_add' y z := mul_add_left y z seamXm
  map_smul' r y := mul_smul_left r y seamXm

@[simp] theorem seamRm_apply (y : CDAlg ℝ 4) : seamRm y = y * seamXm := rfl

/-- The top plane also annihilates `z₋` on the RIGHT. -/
theorem topSpan_le_ker_seamRm : topSpan ≤ LinearMap.ker seamRm := by
  rw [topSpan, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, seamRm_apply]
  fin_cases i
  · exact t1_mul_seamXm
  · exact t2_mul_seamXm
  · exact t3_mul_seamXm
  · exact t4_mul_seamXm

theorem topSpan_mul_seamXm (y : CDAlg ℝ 4) (hy : y ∈ topSpan) : y * seamXm = 0 := by
  have h := topSpan_le_ker_seamRm hy
  rwa [LinearMap.mem_ker, seamRm_apply] at h

/-! ## 4. The Gram operator of `L_z` and its spectrum -/

/-- **`L_z` is skew-adjoint:** `⟨z·y, w⟩ = −⟨y, z·w⟩` for `z = e₁ + e₁₀`. -/
theorem seamL_skew (y w : CDAlg ℝ 4) : bil (seamL y) w = - bil y (seamL w) := by
  rw [seamL_apply, seamL_apply]
  exact sbp_skew 1 10 (by decide) (by decide) 1 y w

/-- **`L_{z₋}` is skew-adjoint.** -/
theorem seamLm_skew (y w : CDAlg ℝ 4) : bil (seamLm y) w = - bil y (seamLm w) := by
  rw [seamLm_apply, seamLm_apply]
  exact sbp_skew 1 10 (by decide) (by decide) (-1) y w

/-- The Gram operator `G := L_zᵀ L_z`, realised as `−L_z ∘ L_z`. -/
noncomputable def seamG : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 4 := -(seamL ∘ₗ seamL)

@[simp] theorem seamG_apply (y : CDAlg ℝ 4) : seamG y = -(seamX * (seamX * y)) := rfl

/-- **`seamG` IS the Gram operator `L_zᵀL_z`:** `⟨L_z y, L_z w⟩ = ⟨y, G w⟩`.  This
    is the statement that justifies calling the spectrum below "the spectrum of
    `L_zᵀ L_z`"; no adjoint is postulated, it is computed. -/
theorem seamGram_eq (y w : CDAlg ℝ 4) : bil (seamL y) (seamL w) = bil y (seamG w) := by
  rw [seamL_skew y (seamL w), seamG_apply, bil_neg_right]
  rfl

/-- Rayleigh form: `⟨y, G y⟩ = N(z·y)` — the Gram quadratic form IS the squared
    length of the image. -/
theorem seamG_rayleigh (y : CDAlg ℝ 4) : bil y (seamG y) = N (seamX * y) := by
  rw [← seamGram_eq, seamL_apply, ← N_eq_bil]

/-- The `c`-eigenspace of the Gram operator. -/
noncomputable def seamEig (c : ℝ) : Submodule ℝ (CDAlg ℝ 4) :=
  LinearMap.ker (seamG - c • LinearMap.id)

theorem mem_seamEig (c : ℝ) (x : CDAlg ℝ 4) : x ∈ seamEig c ↔ seamG x = c • x := by
  rw [seamEig, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- **Eigenvalue 0 — the kernel.**  `G x = 0 ↔ z·x = 0`. -/
theorem seamEig_zero_eq : seamEig 0 = seamKerSpan := by
  rw [← seamL_ker_eq]
  ext x
  rw [mem_seamEig, LinearMap.mem_ker, seamL_apply, seamG_apply, zero_smul, neg_eq_zero]
  exact sbp_sq_eq_zero_iff 1 10 (by decide) (by decide) 1 x

/-- The seam split identity for the witness: `G₊ + G₋ = 4·id`. -/
theorem seam_sq_split (y : CDAlg ℝ 4) :
    seamX * (seamX * y) + seamXm * (seamXm * y) = (-4 : ℝ) • y :=
  basisPair_sq_split 1 10 (by decide) (by decide) y

/-- **Eigenvalue 4 — the top plane.**  `G x = 4x ↔ z₋·x = 0`, so the 4-eigenspace
    of `L_zᵀL_z` is exactly `ker L_{z₋} = topSpan`. -/
theorem seamEig_four_eq : seamEig 4 = topSpan := by
  rw [← seamLm_ker_eq]
  ext x
  rw [mem_seamEig, LinearMap.mem_ker, seamLm_apply, seamG_apply]
  have hsplit := seam_sq_split x
  constructor
  · intro h
    rw [neg_eq_iff_eq_neg] at h
    have hA : seamX * (seamX * x) = (-4 : ℝ) • x := by rw [h]; module
    rw [hA, add_eq_left] at hsplit
    exact (sbp_sq_eq_zero_iff 1 10 (by decide) (by decide) (-1) x).mp hsplit
  · intro h
    have hB : seamXm * (seamXm * x) = 0 := by rw [h, alt_mul_zero]
    rw [hB, add_zero] at hsplit
    rw [hsplit]
    module

/-! ### 4a. The middle eigenspace

The eight basis directions `e₀,e₁,e₂,e₃,e₈,e₉,e₁₀,e₁₁` are fixed by `G` up to the
factor 2.  Each is a four-term product computation on the sign table. -/

/-- `z·e_p` in basis form. -/
theorem seamX_mul_e (p : Fin (2^4)) :
    seamX * e p = (mulCoeff 4 1 p : ℝ) • e ((1 : Fin (2^4)) ^^^ p)
      + (mulCoeff 4 10 p : ℝ) • e ((10 : Fin (2^4)) ^^^ p) := by
  rw [seamX_eq, mul_add_left, e_mul_e, e_mul_e]

/-- `z·(z·e_m)` in basis form, with all six index identities and six sign-table
    entries supplied by kernel `decide` at the call site. -/
theorem seamG_e_at (m p q r : Fin (2^4)) (c1 c2 d1 d2 d3 d4 : ℤ)
    (hp : (1 : Fin (2^4)) ^^^ m = p) (hq : (10 : Fin (2^4)) ^^^ m = q)
    (h1 : (1 : Fin (2^4)) ^^^ p = m) (h2 : (10 : Fin (2^4)) ^^^ p = r)
    (h3 : (1 : Fin (2^4)) ^^^ q = r) (h4 : (10 : Fin (2^4)) ^^^ q = m)
    (g1 : mulCoeff 4 1 m = c1) (g2 : mulCoeff 4 10 m = c2)
    (g3 : mulCoeff 4 1 p = d1) (g4 : mulCoeff 4 10 p = d2)
    (g5 : mulCoeff 4 1 q = d3) (g6 : mulCoeff 4 10 q = d4) :
    seamX * (seamX * e m)
      = ((c1 * d1 + c2 * d4 : ℤ) : ℝ) • e m + ((c1 * d2 + c2 * d3 : ℤ) : ℝ) • e r := by
  rw [seamX_mul_e m, hp, hq, g1, g2, mul_add_right, mul_smul_right, mul_smul_right,
    seamX_mul_e p, seamX_mul_e q, h1, h2, h3, h4, g3, g4, g5, g6]
  push_cast
  module

/-- Middle-block form: when the off-diagonal Gram entry vanishes, `e_m` is an
    eigenvector with `z·(z·e_m) = −2·e_m`. -/
theorem seamG_e_mid (m p q r : Fin (2^4)) (c1 c2 d1 d2 d3 d4 : ℤ)
    (hp : (1 : Fin (2^4)) ^^^ m = p) (hq : (10 : Fin (2^4)) ^^^ m = q)
    (h1 : (1 : Fin (2^4)) ^^^ p = m) (h2 : (10 : Fin (2^4)) ^^^ p = r)
    (h3 : (1 : Fin (2^4)) ^^^ q = r) (h4 : (10 : Fin (2^4)) ^^^ q = m)
    (g1 : mulCoeff 4 1 m = c1) (g2 : mulCoeff 4 10 m = c2)
    (g3 : mulCoeff 4 1 p = d1) (g4 : mulCoeff 4 10 p = d2)
    (g5 : mulCoeff 4 1 q = d3) (g6 : mulCoeff 4 10 q = d4)
    (hdiag : c1 * d1 + c2 * d4 = -2) (hoff : c1 * d2 + c2 * d3 = 0) :
    seamX * (seamX * e m) = (-2 : ℝ) • e m := by
  rw [seamG_e_at m p q r c1 c2 d1 d2 d3 d4 hp hq h1 h2 h3 h4 g1 g2 g3 g4 g5 g6,
    hdiag, hoff]
  push_cast
  module

theorem seamG_e0 : seamX * (seamX * e (0 : Fin (2^4))) = (-2 : ℝ) • e (0 : Fin (2^4)) :=
  seamG_e_mid 0 1 10 11 1 1 (-1) 1 (-1) (-1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e1 : seamX * (seamX * e (1 : Fin (2^4))) = (-2 : ℝ) • e (1 : Fin (2^4)) :=
  seamG_e_mid 1 0 11 10 (-1) 1 1 1 1 (-1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e2 : seamX * (seamX * e (2 : Fin (2^4))) = (-2 : ℝ) • e (2 : Fin (2^4)) :=
  seamG_e_mid 2 3 8 9 1 1 (-1) (-1) 1 (-1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e3 : seamX * (seamX * e (3 : Fin (2^4))) = (-2 : ℝ) • e (3 : Fin (2^4)) :=
  seamG_e_mid 3 2 9 8 (-1) (-1) 1 1 (-1) 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e8 : seamX * (seamX * e (8 : Fin (2^4))) = (-2 : ℝ) • e (8 : Fin (2^4)) :=
  seamG_e_mid 8 9 2 3 1 (-1) (-1) 1 1 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e9 : seamX * (seamX * e (9 : Fin (2^4))) = (-2 : ℝ) • e (9 : Fin (2^4)) :=
  seamG_e_mid 9 8 3 2 (-1) 1 1 (-1) (-1) (-1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e10 : seamX * (seamX * e (10 : Fin (2^4))) = (-2 : ℝ) • e (10 : Fin (2^4)) :=
  seamG_e_mid 10 11 0 1 (-1) (-1) 1 (-1) 1 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem seamG_e11 : seamX * (seamX * e (11 : Fin (2^4))) = (-2 : ℝ) • e (11 : Fin (2^4)) :=
  seamG_e_mid 11 10 1 0 1 (-1) (-1) (-1) (-1) 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- The eight middle index directions. -/
def midIdx : Fin 8 → Fin (2^4) := ![0, 1, 2, 3, 8, 9, 10, 11]

theorem midIdx_injective : Function.Injective midIdx := by decide

theorem mid_linearIndependent :
    LinearIndependent ℝ (fun j : Fin 8 => (e (midIdx j) : CDAlg ℝ 4)) :=
  (QBP.Foundations.CDDimension.e_linearIndependent 4).comp midIdx midIdx_injective

/-- **The middle space** `M = span{e₀,e₁,e₂,e₃,e₈,e₉,e₁₀,e₁₁}`. -/
noncomputable def midSpan : Submodule ℝ (CDAlg ℝ 4) :=
  Submodule.span ℝ (Set.range (fun j : Fin 8 => (e (midIdx j) : CDAlg ℝ 4)))

theorem finrank_midSpan : finrank ℝ midSpan = 8 := by
  rw [midSpan, finrank_span_eq_card mid_linearIndependent, Fintype.card_fin]

theorem seamG_e_mid_all (m : Fin (2^4))
    (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11) :
    seamX * (seamX * e m) = (-2 : ℝ) • e m := by
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact seamG_e0
  · exact seamG_e1
  · exact seamG_e2
  · exact seamG_e3
  · exact seamG_e8
  · exact seamG_e9
  · exact seamG_e10
  · exact seamG_e11

theorem midIdx_spec : ∀ j : Fin 8, midIdx j = 0 ∨ midIdx j = 1 ∨ midIdx j = 2 ∨
    midIdx j = 3 ∨ midIdx j = 8 ∨ midIdx j = 9 ∨ midIdx j = 10 ∨ midIdx j = 11 := by
  decide

theorem midSpan_le_seamEig_two : midSpan ≤ seamEig 2 := by
  rw [midSpan, Submodule.span_le]
  rintro v ⟨j, rfl⟩
  rw [SetLike.mem_coe, mem_seamEig, seamG_apply, seamG_e_mid_all _ (midIdx_spec j)]
  module

/-! ### 4b. The orthogonal decomposition `ℝ¹⁶ = M ⊕ T ⊕ K`

Explicit coordinate projections; `proj_decomp` is a coordinate identity. -/

/-- Projection onto the top plane. -/
noncomputable def projTop (x : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  ((x.coord 4 + x.coord 15) / 2) • t1 + ((x.coord 5 - x.coord 14) / 2) • t2
    + ((x.coord 6 + x.coord 13) / 2) • t3 + ((x.coord 7 - x.coord 12) / 2) • t4

/-- Projection onto the kernel plane. -/
noncomputable def projKer (x : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  ((x.coord 7 + x.coord 12) / 2) • k1 + ((x.coord 6 - x.coord 13) / 2) • k2
    + ((x.coord 5 + x.coord 14) / 2) • k3 + ((x.coord 4 - x.coord 15) / 2) • k4

/-- Projection onto the middle space. -/
noncomputable def projMid (x : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  x.coord 0 • e (0 : Fin (2^4)) + x.coord 1 • e (1 : Fin (2^4))
    + x.coord 2 • e (2 : Fin (2^4)) + x.coord 3 • e (3 : Fin (2^4))
    + x.coord 8 • e (8 : Fin (2^4)) + x.coord 9 • e (9 : Fin (2^4))
    + x.coord 10 • e (10 : Fin (2^4)) + x.coord 11 • e (11 : Fin (2^4))

/-- **The decomposition is exact:** every sedenion is the sum of its three
    eigen-components. -/
theorem proj_decomp (x : CDAlg ℝ 4) : x = projMid x + projTop x + projKer x := by
  ext k
  rcases fin16_cases k with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [projMid, projTop, projKer, t1, t2, t3, t4, k1, k2, k3, k4,
      add_coord, smul_coord, sbp_coord, e_coord] <;>
    norm_num +decide <;>
    ring

theorem projTop_mem (x : CDAlg ℝ 4) : projTop x ∈ topSpan := by
  rw [projTop, topSpan]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem projKer_mem (x : CDAlg ℝ 4) : projKer x ∈ seamKerSpan := by
  rw [projKer, seamKerSpan]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem e_mem_midSpan (j : Fin 8) : (e (midIdx j) : CDAlg ℝ 4) ∈ midSpan :=
  Submodule.subset_span ⟨j, rfl⟩

theorem e_mem_midSpan_of (m : Fin (2^4))
    (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11) :
    (e m : CDAlg ℝ 4) ∈ midSpan := by
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have h := e_mem_midSpan 0; rwa [show midIdx 0 = (0 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 1; rwa [show midIdx 1 = (1 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 2; rwa [show midIdx 2 = (2 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 3; rwa [show midIdx 3 = (3 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 4; rwa [show midIdx 4 = (8 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 5; rwa [show midIdx 5 = (9 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 6; rwa [show midIdx 6 = (10 : Fin (2^4)) from by decide] at h
  · have h := e_mem_midSpan 7; rwa [show midIdx 7 = (11 : Fin (2^4)) from by decide] at h

theorem projMid_mem (x : CDAlg ℝ 4) : projMid x ∈ midSpan := by
  rw [projMid]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (e_mem_midSpan_of _ (by decide))

/-- `G` acts as 4 on the top component. -/
theorem seamG_projTop (x : CDAlg ℝ 4) : seamG (projTop x) = (4 : ℝ) • projTop x := by
  have h : projTop x ∈ seamEig 4 := by rw [seamEig_four_eq]; exact projTop_mem x
  exact (mem_seamEig 4 _).mp h

/-- `G` annihilates the kernel component. -/
theorem seamG_projKer (x : CDAlg ℝ 4) : seamG (projKer x) = 0 := by
  have h : projKer x ∈ seamEig 0 := by rw [seamEig_zero_eq]; exact projKer_mem x
  have := (mem_seamEig 0 _).mp h
  rw [this, zero_smul]

/-- `G` acts as 2 on the middle component. -/
theorem seamG_projMid (x : CDAlg ℝ 4) : seamG (projMid x) = (2 : ℝ) • projMid x := by
  have h : projMid x ∈ seamEig 2 := midSpan_le_seamEig_two (projMid_mem x)
  exact (mem_seamEig 2 _).mp h

/-- **Eigenvalue 2 — the middle space.**  `G x = 2x ↔ x ∈ midSpan`. -/
theorem seamEig_two_eq : seamEig 2 = midSpan := by
  apply le_antisymm
  · intro x hx
    have hGx := (mem_seamEig 2 x).mp hx
    have hdec := proj_decomp x
    have hexp : seamG x = (2 : ℝ) • projMid x + (4 : ℝ) • projTop x := by
      conv_lhs => rw [hdec]
      rw [map_add, map_add, seamG_projMid, seamG_projTop, seamG_projKer, add_zero]
    have hkey : (2 : ℝ) • x = (2 : ℝ) • projMid x + (4 : ℝ) • projTop x := by
      rw [← hGx, hexp]
    have c4 := congrArg (fun z : CDAlg ℝ 4 => z.coord 4) hkey
    have c5 := congrArg (fun z : CDAlg ℝ 4 => z.coord 5) hkey
    have c6 := congrArg (fun z : CDAlg ℝ 4 => z.coord 6) hkey
    have c7 := congrArg (fun z : CDAlg ℝ 4 => z.coord 7) hkey
    have c12 := congrArg (fun z : CDAlg ℝ 4 => z.coord 12) hkey
    have c13 := congrArg (fun z : CDAlg ℝ 4 => z.coord 13) hkey
    have c14 := congrArg (fun z : CDAlg ℝ 4 => z.coord 14) hkey
    have c15 := congrArg (fun z : CDAlg ℝ 4 => z.coord 15) hkey
    simp only [projMid, projTop, t1, t2, t3, t4, add_coord, smul_coord, sbp_coord,
      e_coord] at c4 c5 c6 c7 c12 c13 c14 c15
    norm_num +decide at c4 c5 c6 c7 c12 c13 c14 c15
    have hx' : x = projMid x := by
      ext k
      rcases fin16_cases k with
        rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp only [projMid, add_coord, smul_coord, e_coord] <;>
        norm_num +decide <;>
        linarith
    rw [hx']
    exact projMid_mem x
  · exact midSpan_le_seamEig_two

/-! ### 4c. The spectrum, packaged -/

theorem finrank_seamEig_four : finrank ℝ (seamEig 4) = 4 := by
  rw [seamEig_four_eq]; exact finrank_topSpan

theorem finrank_seamEig_two : finrank ℝ (seamEig 2) = 8 := by
  rw [seamEig_two_eq]; exact finrank_midSpan

theorem finrank_seamEig_zero : finrank ℝ (seamEig 0) = 4 := by
  rw [seamEig_zero_eq]; exact finrank_seamKerSpan

/-- **THE SPECTRUM OF `L_zᵀL_z` FOR THE SEAM WITNESS `z = e₁ + e₁₀`.**

    `⟨L_z y, L_z w⟩ = ⟨y, G w⟩` (so `G` really is `L_zᵀL_z`), and
    `ℝ¹⁶ = T ⊕ M ⊕ K` with

      `G = 4` on `T = span{e₄+e₁₅, e₅−e₁₄, e₆+e₁₃, e₇−e₁₂}`   (dim 4),
      `G = 2` on `M = span{e₀,e₁,e₂,e₃,e₈,e₉,e₁₀,e₁₁}`        (dim 8),
      `G = 0` on `K = span{e₇+e₁₂, e₆−e₁₃, e₅+e₁₄, e₄−e₁₅}`   (dim 4),

    i.e. singular values `2 (×4)`, `√2 (×8)`, `0 (×4)` for `L_z` — and
    `4 + 8 + 4 = 16`, so the three eigenspaces exhaust 𝕊. -/
theorem seam_gram_spectrum :
    (∀ y w : CDAlg ℝ 4, bil (seamL y) (seamL w) = bil y (seamG w)) ∧
    seamEig 4 = topSpan ∧ seamEig 2 = midSpan ∧ seamEig 0 = seamKerSpan ∧
    finrank ℝ (seamEig 4) = 4 ∧ finrank ℝ (seamEig 2) = 8 ∧
    finrank ℝ (seamEig 0) = 4 ∧
    (∀ x : CDAlg ℝ 4, x = projMid x + projTop x + projKer x) :=
  ⟨seamGram_eq, seamEig_four_eq, seamEig_two_eq, seamEig_zero_eq,
    finrank_seamEig_four, finrank_seamEig_two, finrank_seamEig_zero, proj_decomp⟩

/-! ### 4d. The eigenvalue list is COMPLETE — no fourth eigenvalue

`seamEig_four_eq` / `seamEig_two_eq` / `seamEig_zero_eq` identify three eigenspaces;
on their own they leave open whether some OTHER real number is also an eigenvalue.
It is not: `G` satisfies its own characteristic-root polynomial
`c(c − 2)(c − 4) = 0` as an operator identity (`seamG_cubic`), which forces every
eigenvalue into `{0, 2, 4}` (`seamEig_eq_bot_of_ne`). -/

/-- **The annihilating cubic** of the Gram operator:
    `G³ = 6·G² − 8·G`, i.e. `G·(G − 2·id)·(G − 4·id) = 0`.
    (Read off the `M ⊕ T ⊕ K` decomposition: `G` acts as `2`, `4`, `0`.) -/
theorem seamG_cubic (x : CDAlg ℝ 4) :
    seamG (seamG (seamG x)) = (6 : ℝ) • seamG (seamG x) - (8 : ℝ) • seamG x := by
  have hd := proj_decomp x
  have h1 : seamG x = (2 : ℝ) • projMid x + (4 : ℝ) • projTop x := by
    conv_lhs => rw [hd]
    rw [map_add, map_add, seamG_projMid, seamG_projTop, seamG_projKer, add_zero]
  have h2 : seamG (seamG x) = (4 : ℝ) • projMid x + (16 : ℝ) • projTop x := by
    rw [h1, map_add, map_smul, map_smul, seamG_projMid, seamG_projTop]
    module
  have h3 : seamG (seamG (seamG x)) = (8 : ℝ) • projMid x + (64 : ℝ) • projTop x := by
    rw [h2, map_add, map_smul, map_smul, seamG_projMid, seamG_projTop]
    module
  rw [h3, h2, h1]
  module

/-- **No eigenvalue outside `{0, 2, 4}`:** for every other real `c` the `c`-eigenspace
    of `L_zᵀL_z` is the zero subspace. -/
theorem seamEig_eq_bot_of_ne (c : ℝ) (h0 : c ≠ 0) (h2 : c ≠ 2) (h4 : c ≠ 4) :
    seamEig c = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hG : seamG x = c • x := (mem_seamEig c x).mp hx
  have hG2 : seamG (seamG x) = (c * c) • x := by rw [hG, map_smul, hG, smul_smul]
  have hG3 : seamG (seamG (seamG x)) = (c * c * c) • x := by
    rw [hG2, map_smul, hG, smul_smul]
  have hcub := seamG_cubic x
  rw [hG3, hG2, hG] at hcub
  have hkey : (c * (c - 2) * (c - 4)) • x = 0 := by
    have hexp : (c * (c - 2) * (c - 4)) • x
        = (c * c * c) • x - (6 : ℝ) • ((c * c) • x) + (8 : ℝ) • (c • x) := by module
    rw [hexp, hcub]
    module
  have hne : c * (c - 2) * (c - 4) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h2)) (sub_ne_zero.mpr h4)
  exact (smul_eq_zero.mp hkey).resolve_left hne

/-- **THE SPECTRUM IS EXACTLY `{4 (×4), 2 (×8), 0 (×4)}`.**  The three eigenspaces
    have dimensions `4 + 8 + 4 = 16 = dim 𝕊`, and every other real number has zero
    eigenspace — so the list is complete, not merely a lower bound. -/
theorem seam_gram_spectrum_exhaustive :
    (∀ c : ℝ, c ≠ 0 → c ≠ 2 → c ≠ 4 → seamEig c = ⊥) ∧
    finrank ℝ (seamEig 4) = 4 ∧ finrank ℝ (seamEig 2) = 8 ∧
    finrank ℝ (seamEig 0) = 4 ∧
    finrank ℝ (seamEig 4) + finrank ℝ (seamEig 2) + finrank ℝ (seamEig 0) = 16 := by
  refine ⟨seamEig_eq_bot_of_ne, finrank_seamEig_four, finrank_seamEig_two,
    finrank_seamEig_zero, ?_⟩
  have h4 := finrank_seamEig_four
  have h2 := finrank_seamEig_two
  have h0 := finrank_seamEig_zero
  omega

/-! ## 5. The top plane lies on the zero-divisor ridge

Two statements, one qualitative and one quantitative.  Qualitatively: EVERY
nonzero element of `T` is a two-sided zero divisor, all of them annihilated by the
single element `z₋ = e₁ − e₁₀`.  Quantitatively: the attack-2 potential
`V(x) = ‖[cdLo x, cdHi x]‖²` equals `N(x)²` on `T`, which for a unit vector is the
ridge value `V = 1`. -/

/-- The attack-2 potential `V(x) = ‖[a,b]‖²` for the Cayley–Dickson split
    `x = a + b·ℓ`.  Defined here as a coordinate/commutator norm; no physical or
    substrate reading attaches to it in this file. -/
noncomputable def potV (x : CDAlg ℝ 4) : ℝ :=
  N (cdLo x * cdHi x - cdHi x * cdLo x)

/-- **Every nonzero element of the top plane is a TWO-SIDED zero divisor**, each
    annihilated by the same partner `z₋ = e₁ − e₁₀ ≠ 0`.  This is the derived form
    of "the top singular plane lies on the ridge `V = 1`". -/
theorem top_plane_zero_divisor (t : CDAlg ℝ 4) (ht : t ∈ topSpan) (ht0 : t ≠ 0) :
    seamXm ≠ 0 ∧ t ≠ 0 ∧ seamXm * t = 0 ∧ t * seamXm = 0 := by
  refine ⟨seamXm_ne_zero, ht0, ?_, topSpan_mul_seamXm t ht⟩
  have : t ∈ LinearMap.ker seamLm := by rw [seamLm_ker_eq]; exact ht
  rw [LinearMap.mem_ker, seamLm_apply] at this
  exact this

/-- Each of the four spanning directions of the top plane is itself a basis-sum
    zero divisor `e_i ± e_j` with `i ∈ 1..7`, `j ∈ 9..15`. -/
theorem top_generators_are_zero_divisors :
    (t1 = sbp 4 15 1 ∧ t1 ≠ 0 ∧ seamXm * t1 = 0 ∧ t1 * seamXm = 0) ∧
    (t2 = sbp 5 14 (-1) ∧ t2 ≠ 0 ∧ seamXm * t2 = 0 ∧ t2 * seamXm = 0) ∧
    (t3 = sbp 6 13 1 ∧ t3 ≠ 0 ∧ seamXm * t3 = 0 ∧ t3 * seamXm = 0) ∧
    (t4 = sbp 7 12 (-1) ∧ t4 ≠ 0 ∧ seamXm * t4 = 0 ∧ t4 * seamXm = 0) :=
  ⟨⟨rfl, t1_ne_zero, seamXm_mul_t1, t1_mul_seamXm⟩,
   ⟨rfl, t2_ne_zero, seamXm_mul_t2, t2_mul_seamXm⟩,
   ⟨rfl, t3_ne_zero, seamXm_mul_t3, t3_mul_seamXm⟩,
   ⟨rfl, t4_ne_zero, seamXm_mul_t4, t4_mul_seamXm⟩⟩

/-! ### 5a. Coordinate forms of the Cayley–Dickson halves -/

/-- Expanded form of a `Fin (2^3)`-indexed sum (`2^3` is definitionally `8`). -/
theorem sum_fin_eight (f : Fin (2^3) → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 :=
  Fin.sum_univ_eight (f := f)

theorem N_cdLo_eq (x : CDAlg ℝ 4) :
    N (cdLo x) = x.coord 0 ^ 2 + x.coord 1 ^ 2 + x.coord 2 ^ 2 + x.coord 3 ^ 2
      + x.coord 4 ^ 2 + x.coord 5 ^ 2 + x.coord 6 ^ 2 + x.coord 7 ^ 2 := by
  rw [N_def, sum_fin_eight]
  simp only [cdLo_coord, show loIdx (0 : Fin (2^3)) = (0 : Fin (2^4)) from by decide,
    show loIdx (1 : Fin (2^3)) = (1 : Fin (2^4)) from by decide,
    show loIdx (2 : Fin (2^3)) = (2 : Fin (2^4)) from by decide,
    show loIdx (3 : Fin (2^3)) = (3 : Fin (2^4)) from by decide,
    show loIdx (4 : Fin (2^3)) = (4 : Fin (2^4)) from by decide,
    show loIdx (5 : Fin (2^3)) = (5 : Fin (2^4)) from by decide,
    show loIdx (6 : Fin (2^3)) = (6 : Fin (2^4)) from by decide,
    show loIdx (7 : Fin (2^3)) = (7 : Fin (2^4)) from by decide]

theorem N_cdHi_eq (x : CDAlg ℝ 4) :
    N (cdHi x) = x.coord 8 ^ 2 + x.coord 9 ^ 2 + x.coord 10 ^ 2 + x.coord 11 ^ 2
      + x.coord 12 ^ 2 + x.coord 13 ^ 2 + x.coord 14 ^ 2 + x.coord 15 ^ 2 := by
  rw [N_def, sum_fin_eight]
  simp only [cdHi_coord, show hiIdx (0 : Fin (2^3)) = (8 : Fin (2^4)) from by decide,
    show hiIdx (1 : Fin (2^3)) = (9 : Fin (2^4)) from by decide,
    show hiIdx (2 : Fin (2^3)) = (10 : Fin (2^4)) from by decide,
    show hiIdx (3 : Fin (2^3)) = (11 : Fin (2^4)) from by decide,
    show hiIdx (4 : Fin (2^3)) = (12 : Fin (2^4)) from by decide,
    show hiIdx (5 : Fin (2^3)) = (13 : Fin (2^4)) from by decide,
    show hiIdx (6 : Fin (2^3)) = (14 : Fin (2^4)) from by decide,
    show hiIdx (7 : Fin (2^3)) = (15 : Fin (2^4)) from by decide]

theorem bil_cdLo_cdHi_eq (x : CDAlg ℝ 4) :
    bil (cdLo x) (cdHi x)
      = x.coord 0 * x.coord 8 + x.coord 1 * x.coord 9 + x.coord 2 * x.coord 10
        + x.coord 3 * x.coord 11 + x.coord 4 * x.coord 12 + x.coord 5 * x.coord 13
        + x.coord 6 * x.coord 14 + x.coord 7 * x.coord 15 := by
  rw [bil_def, sum_fin_eight]
  simp only [cdLo_coord, cdHi_coord,
    show loIdx (0 : Fin (2^3)) = (0 : Fin (2^4)) from by decide,
    show loIdx (1 : Fin (2^3)) = (1 : Fin (2^4)) from by decide,
    show loIdx (2 : Fin (2^3)) = (2 : Fin (2^4)) from by decide,
    show loIdx (3 : Fin (2^3)) = (3 : Fin (2^4)) from by decide,
    show loIdx (4 : Fin (2^3)) = (4 : Fin (2^4)) from by decide,
    show loIdx (5 : Fin (2^3)) = (5 : Fin (2^4)) from by decide,
    show loIdx (6 : Fin (2^3)) = (6 : Fin (2^4)) from by decide,
    show loIdx (7 : Fin (2^3)) = (7 : Fin (2^4)) from by decide,
    show hiIdx (0 : Fin (2^3)) = (8 : Fin (2^4)) from by decide,
    show hiIdx (1 : Fin (2^3)) = (9 : Fin (2^4)) from by decide,
    show hiIdx (2 : Fin (2^3)) = (10 : Fin (2^4)) from by decide,
    show hiIdx (3 : Fin (2^3)) = (11 : Fin (2^4)) from by decide,
    show hiIdx (4 : Fin (2^3)) = (12 : Fin (2^4)) from by decide,
    show hiIdx (5 : Fin (2^3)) = (13 : Fin (2^4)) from by decide,
    show hiIdx (6 : Fin (2^3)) = (14 : Fin (2^4)) from by decide,
    show hiIdx (7 : Fin (2^3)) = (15 : Fin (2^4)) from by decide]

theorem cdLo_coord0_eq (x : CDAlg ℝ 4) : (cdLo x).coord 0 = x.coord 0 := by
  rw [cdLo_coord, show loIdx (0 : Fin (2^3)) = (0 : Fin (2^4)) from by decide]

theorem cdHi_coord0_eq (x : CDAlg ℝ 4) : (cdHi x).coord 0 = x.coord 8 := by
  rw [cdHi_coord, show hiIdx (0 : Fin (2^3)) = (8 : Fin (2^4)) from by decide]

/-- `V` via the 𝕆 Lagrange identity: for `x` whose two Cayley–Dickson halves are
    PURE octonions, `V(x) = 4(N(cdLo x)·N(cdHi x) − ⟨cdLo x, cdHi x⟩²)`. -/
theorem potV_eq_gram (x : CDAlg ℝ 4) (h0 : x.coord 0 = 0) (h8 : x.coord 8 = 0) :
    potV x = 4 * (N (cdLo x) * N (cdHi x) - (bil (cdLo x) (cdHi x)) ^ 2) := by
  have hlo : (cdLo x).coord 0 = 0 := by rw [cdLo_coord0_eq, h0]
  have hhi : (cdHi x).coord 0 = 0 := by rw [cdHi_coord0_eq, h8]
  have hcross : cdLo x * cdHi x - cdHi x * cdLo x
      = (2 : ℝ) • QBP.Foundations.CrossProduct.cross (cdLo x) (cdHi x) := by
    rw [QBP.Foundations.CrossProduct.cross_def, smul_smul]
    norm_num
  rw [potV, hcross, QBP.Foundations.CrossProduct.N_smul,
    QBP.Foundations.CrossProduct.octonion_cross_norm_identity _ _ hlo hhi]
  ring

/-! ### 5b. `V = N²` on the whole top plane -/

/-- **THE TOP PLANE LIES ON THE RIDGE.**  For every `t` in the top plane,
    `V(t) = N(t)²`; a UNIT vector of `T` therefore has `V = 1`, the ridge value.
    Proved for the whole 4-dimensional plane, not only for its generators. -/
theorem top_plane_on_ridge_of (x : CDAlg ℝ 4) (a b c d : ℝ)
    (hx : x = a • t1 + b • t2 + c • t3 + d • t4) :
    potV x = (N x) ^ 2 := by
  have hco : ∀ k : Fin (2^4), x.coord k
      = a * ((if k = 4 then (1:ℝ) else 0) + ((1 : ℤ) : ℝ) * (if k = 15 then (1:ℝ) else 0))
      + (b * ((if k = 5 then (1:ℝ) else 0) + (((-1) : ℤ) : ℝ) * (if k = 14 then (1:ℝ) else 0))
      + (c * ((if k = 6 then (1:ℝ) else 0) + ((1 : ℤ) : ℝ) * (if k = 13 then (1:ℝ) else 0))
      + d * ((if k = 7 then (1:ℝ) else 0)
          + (((-1) : ℤ) : ℝ) * (if k = 12 then (1:ℝ) else 0)))) := by
    intro k
    rw [hx]
    simp only [t1, t2, t3, t4, add_coord, smul_coord, sbp_coord]
    ring
  have h0 : x.coord 0 = 0 := by rw [hco 0]; norm_num +decide
  have h1 : x.coord 1 = 0 := by rw [hco 1]; norm_num +decide
  have h2 : x.coord 2 = 0 := by rw [hco 2]; norm_num +decide
  have h3 : x.coord 3 = 0 := by rw [hco 3]; norm_num +decide
  have h4 : x.coord 4 = a := by rw [hco 4]; norm_num +decide
  have h5 : x.coord 5 = b := by rw [hco 5]; norm_num +decide
  have h6 : x.coord 6 = c := by rw [hco 6]; norm_num +decide
  have h7 : x.coord 7 = d := by rw [hco 7]; norm_num +decide
  have h8 : x.coord 8 = 0 := by rw [hco 8]; norm_num +decide
  have h9 : x.coord 9 = 0 := by rw [hco 9]; norm_num +decide
  have h10 : x.coord 10 = 0 := by rw [hco 10]; norm_num +decide
  have h11 : x.coord 11 = 0 := by rw [hco 11]; norm_num +decide
  have h12 : x.coord 12 = -d := by rw [hco 12]; norm_num +decide
  have h13 : x.coord 13 = c := by rw [hco 13]; norm_num +decide
  have h14 : x.coord 14 = -b := by rw [hco 14]; norm_num +decide
  have h15 : x.coord 15 = a := by rw [hco 15]; norm_num +decide
  have hNlo : N (cdLo x) = a^2 + b^2 + c^2 + d^2 := by
    rw [N_cdLo_eq, h0, h1, h2, h3, h4, h5, h6, h7]; ring
  have hNhi : N (cdHi x) = a^2 + b^2 + c^2 + d^2 := by
    rw [N_cdHi_eq, h8, h9, h10, h11, h12, h13, h14, h15]; ring
  have hbil : bil (cdLo x) (cdHi x) = 0 := by
    rw [bil_cdLo_cdHi_eq, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15]; ring
  have hNx : N x = 2 * (a^2 + b^2 + c^2 + d^2) := by
    have hs := QBP.Foundations.NoAutonomousDynamics.N_split x
    rw [hNlo, hNhi] at hs
    rw [hs]; ring
  rw [potV_eq_gram x h0 h8, hNlo, hNhi, hbil, hNx]
  ring

/-- Span form of the ridge theorem. -/
theorem top_plane_on_ridge (a b c d : ℝ) :
    potV (a • t1 + b • t2 + c • t3 + d • t4)
      = (N (a • t1 + b • t2 + c • t3 + d • t4)) ^ 2 :=
  top_plane_on_ridge_of _ a b c d rfl

/-- Membership form of the ridge theorem. -/
theorem top_plane_on_ridge_mem (t : CDAlg ℝ 4) (ht : t ∈ topSpan) :
    potV t = (N t) ^ 2 := by
  have hker : t ∈ LinearMap.ker seamLm := by rw [seamLm_ker_eq]; exact ht
  rw [LinearMap.mem_ker, seamLm_apply] at hker
  exact top_plane_on_ridge_of t (t.coord 4) (t.coord 5) (t.coord 6) (t.coord 7)
    (seam_mker_subset t hker)

/-! ## 6. RIGHT multiplication has the SAME Gram operator — hence the same spectrum

`SeamKernel` proved `ker L_z = ker R_z`.  Much more is true, and it is not automatic
in a non-associative, non-alternative algebra: the two Gram operators COINCIDE,

  `(x·z)·z = z·(z·x)`   for every `x ∈ 𝕊`   (`seam_gram_lr`),

for both signs `z = e₁ ± e₁₀`.  So `R_zᵀR_z = L_zᵀL_z` on the nose, and every
spectral statement of §4 transfers verbatim to `R_z`: singular values
`2 (×4)`, `√2 (×8)`, `0 (×4)` on the SAME three subspaces `T`, `M`, `K`.
(This is the Lean form of attack-2 §2's "`R_z` identical".)  `ad_z = L_z − R_z` is
NOT covered — see the header. -/

/-- Coordinatewise action of `R_{e_a + s·e_b}` — the right-multiplication twin of
    `sbp_mul_coord`. -/
theorem mul_sbp_coord (a b : Fin 16) (s : ℤ) (y : CDAlg ℝ 4) (k : Fin 16) :
    (y * sbp a b s).coord k
      = (mulCoeff 4 (a ^^^ k) a : ℝ) * y.coord (a ^^^ k)
        + (s : ℝ) * ((mulCoeff 4 (b ^^^ k) b : ℝ) * y.coord (b ^^^ k)) := by
  rw [sbp, mul_add_right, add_coord, mul_e_coord, mul_smul_right, smul_coord, mul_e_coord]

/-- The four index identities of the seam plane (kernel `decide`, 16 cases): the
    pair `{1, 10}` generates the 2-element XOR-group `{0, 11}` on indices. -/
theorem seam_xor_idx (k : Fin 16) :
    ((1 : Fin 16) ^^^ ((1 : Fin 16) ^^^ k) = k)
      ∧ ((10 : Fin 16) ^^^ ((1 : Fin 16) ^^^ k) = (11 : Fin 16) ^^^ k)
      ∧ ((1 : Fin 16) ^^^ ((10 : Fin 16) ^^^ k) = (11 : Fin 16) ^^^ k)
      ∧ ((10 : Fin 16) ^^^ ((10 : Fin 16) ^^^ k) = k) := by
  revert k; decide

/-- Sign-table fact (kernel `decide`, 16 cases): the DIAGONAL entry of the `2×2`
    Gram block is the same computed on the right as on the left. -/
theorem seam_gram_diag (k : Fin 16) :
    mulCoeff 4 ((1 : Fin 16) ^^^ k) 1 * mulCoeff 4 k 1
      + mulCoeff 4 ((10 : Fin 16) ^^^ k) 10 * mulCoeff 4 k 10
    = mulCoeff 4 1 ((1 : Fin 16) ^^^ k) * mulCoeff 4 1 k
      + mulCoeff 4 10 ((10 : Fin 16) ^^^ k) * mulCoeff 4 10 k := by
  revert k; decide

/-- Sign-table fact (kernel `decide`, 16 cases): the OFF-DIAGONAL entry of the `2×2`
    Gram block is the same computed on the right as on the left. -/
theorem seam_gram_off (k : Fin 16) :
    mulCoeff 4 ((1 : Fin 16) ^^^ k) 1 * mulCoeff 4 ((11 : Fin 16) ^^^ k) 10
      + mulCoeff 4 ((10 : Fin 16) ^^^ k) 10 * mulCoeff 4 ((11 : Fin 16) ^^^ k) 1
    = mulCoeff 4 1 ((1 : Fin 16) ^^^ k) * mulCoeff 4 10 ((11 : Fin 16) ^^^ k)
      + mulCoeff 4 10 ((10 : Fin 16) ^^^ k) * mulCoeff 4 1 ((11 : Fin 16) ^^^ k) := by
  revert k; decide

theorem seam_gram_lr_coord (x : CDAlg ℝ 4) (k : Fin 16) :
    ((x * seamX) * seamX).coord k = (seamX * (seamX * x)).coord k := by
  have hz : seamX = sbp 1 10 1 := rfl
  obtain ⟨i1, i2, i3, i4⟩ := seam_xor_idx k
  rw [hz, mul_sbp_coord, mul_sbp_coord, mul_sbp_coord,
    sbp_mul_coord, sbp_mul_coord, sbp_mul_coord, i1, i2, i3, i4]
  have hd' := congrArg (fun z : ℤ => (z : ℝ)) (seam_gram_diag k)
  have ho' := congrArg (fun z : ℤ => (z : ℝ)) (seam_gram_off k)
  push_cast at hd' ho' ⊢
  linear_combination x.coord k * hd' + x.coord ((11 : Fin 16) ^^^ k) * ho'

/-- **`(x·z)·z = z·(z·x)` for `z = e₁ + e₁₀`** — the left and right Gram operators
    of the seam witness are the SAME linear map.  Note this is a genuine sign-table
    identity: 𝕊 is not associative, not even alternative, so nothing formal delivers
    it. -/
theorem seam_gram_lr (x : CDAlg ℝ 4) : (x * seamX) * seamX = seamX * (seamX * x) := by
  ext k; exact seam_gram_lr_coord x k

theorem seam_gram_lr_m_coord (x : CDAlg ℝ 4) (k : Fin 16) :
    ((x * seamXm) * seamXm).coord k = (seamXm * (seamXm * x)).coord k := by
  have hz : seamXm = sbp 1 10 (-1) := rfl
  obtain ⟨i1, i2, i3, i4⟩ := seam_xor_idx k
  rw [hz, mul_sbp_coord, mul_sbp_coord, mul_sbp_coord,
    sbp_mul_coord, sbp_mul_coord, sbp_mul_coord, i1, i2, i3, i4]
  have hd' := congrArg (fun z : ℤ => (z : ℝ)) (seam_gram_diag k)
  have ho' := congrArg (fun z : ℤ => (z : ℝ)) (seam_gram_off k)
  push_cast at hd' ho' ⊢
  linear_combination x.coord k * hd' - x.coord ((11 : Fin 16) ^^^ k) * ho'

/-- The same identity for the other sign `z₋ = e₁ − e₁₀`. -/
theorem seam_gram_lr_m (x : CDAlg ℝ 4) : (x * seamXm) * seamXm = seamXm * (seamXm * x) := by
  ext k; exact seam_gram_lr_m_coord x k

/-- Right multiplication by a basis unit is an isometry of the inner product. -/
theorem bil_mul_basis (m : Fin (2^4)) (x y : CDAlg ℝ 4) :
    bil (x * e m) (y * e m) = bil x y := by
  have h1 := QBP.Foundations.CrossProduct.N_add (x * e m) (y * e m)
  have h2 := QBP.Foundations.CrossProduct.N_add x y
  rw [← mul_add_left, N_mul_basis, N_mul_basis, N_mul_basis] at h1
  linarith

/-- Right multiplication by an IMAGINARY basis unit is skew-adjoint. -/
theorem bil_mul_basis_skew (m : Fin (2^4)) (hm : m ≠ 0) (x y : CDAlg ℝ 4) :
    bil (x * e m) y = - bil x (y * e m) := by
  have h := bil_mul_basis m x (y * e m)
  rw [mul_e_sq m hm y, bil_neg_right] at h
  linarith

/-- **`R_{e_a + s·e_b}` is skew-adjoint**, for every basis pair. -/
theorem sbp_skew_right (a b : Fin (2^4)) (ha : a ≠ 0) (hb : b ≠ 0) (s : ℤ) (y w : CDAlg ℝ 4) :
    bil (y * sbp a b s) w = - bil y (w * sbp a b s) := by
  rw [sbp, mul_add_right, mul_add_right, mul_smul_right, mul_smul_right, bil_add_left,
    bil_add_right, bil_smul_left, bil_smul_right, bil_mul_basis_skew a ha,
    bil_mul_basis_skew b hb]
  ring

/-- Right-multiplication twin of `sbp_sq_eq_zero_iff`. -/
theorem sbp_sq_eq_zero_iff_right (a b : Fin (2^4)) (ha : a ≠ 0) (hb : b ≠ 0) (s : ℤ)
    (x : CDAlg ℝ 4) : (x * sbp a b s) * sbp a b s = 0 ↔ x * sbp a b s = 0 := by
  constructor
  · intro h
    have hN : N (x * sbp a b s) = 0 := by
      rw [N_eq_bil, sbp_skew_right a b ha hb s x (x * sbp a b s), h, bil_zero_right]
      ring
    exact (alt_N_eq_zero_iff _).mp hN
  · intro h
    rw [h, alt_zero_mul]

/-- **`R_z` is skew-adjoint** for the seam witness `z = e₁ + e₁₀`. -/
theorem seamR_skew (y w : CDAlg ℝ 4) : bil (seamR y) w = - bil y (seamR w) := by
  rw [seamR_apply, seamR_apply]
  exact sbp_skew_right 1 10 (by decide) (by decide) 1 y w

/-- The Gram operator of `R_z`, realised as `−R_z ∘ R_z`. -/
noncomputable def seamGR : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 4 := -(seamR ∘ₗ seamR)

@[simp] theorem seamGR_apply (y : CDAlg ℝ 4) : seamGR y = -((y * seamX) * seamX) := rfl

/-- **`R_zᵀR_z = L_zᵀL_z`.** -/
theorem seamGR_eq_seamG : seamGR = seamG := by
  ext x
  rw [seamGR_apply, seamG_apply, seam_gram_lr]

/-- `seamGR` really is the Gram operator of `R_z`: `⟨R_z y, R_z w⟩ = ⟨y, G w⟩`. -/
theorem seamRGram_eq (y w : CDAlg ℝ 4) : bil (seamR y) (seamR w) = bil y (seamG w) := by
  rw [seamR_skew y (seamR w), ← seamGR_eq_seamG, seamGR_apply, bil_neg_right]
  rfl

/-- **`ker R_{z₋} = topSpan` too** — upgrading `topSpan_le_ker_seamRm` to an equality.
    So the top plane is exactly the set of elements annihilated by `z₋ = e₁ − e₁₀` on
    EITHER side. -/
theorem seamRm_ker_eq : LinearMap.ker seamRm = topSpan := by
  rw [← seamLm_ker_eq]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, seamRm_apply, seamLm_apply]
  constructor
  · intro h
    have h2 : seamXm * (seamXm * x) = 0 := by
      rw [← seam_gram_lr_m, h, alt_zero_mul]
    exact (sbp_sq_eq_zero_iff 1 10 (by decide) (by decide) (-1) x).mp h2
  · intro h
    have h2 : (x * seamXm) * seamXm = 0 := by
      rw [seam_gram_lr_m, h, alt_mul_zero]
    exact (sbp_sq_eq_zero_iff_right 1 10 (by decide) (by decide) (-1) x).mp h2

/-- The `c`-eigenspace of the RIGHT Gram operator. -/
noncomputable def seamEigR (c : ℝ) : Submodule ℝ (CDAlg ℝ 4) :=
  LinearMap.ker (seamGR - c • LinearMap.id)

theorem seamEigR_eq_seamEig (c : ℝ) : seamEigR c = seamEig c := by
  rw [seamEigR, seamEig, seamGR_eq_seamG]

/-- **THE SPECTRUM OF `R_zᵀR_z` — identical to `L_zᵀL_z`, on the same eigenspaces.**
    `4` on `T` (dim 4), `2` on `M` (dim 8), `0` on `K` (dim 4). -/
theorem seamR_gram_spectrum :
    (∀ y w : CDAlg ℝ 4, bil (seamR y) (seamR w) = bil y (seamGR w)) ∧
    seamGR = seamG ∧
    seamEigR 4 = topSpan ∧ seamEigR 2 = midSpan ∧ seamEigR 0 = seamKerSpan ∧
    finrank ℝ (seamEigR 4) = 4 ∧ finrank ℝ (seamEigR 2) = 8 ∧
    finrank ℝ (seamEigR 0) = 4 := by
  refine ⟨?_, seamGR_eq_seamG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y w; rw [seamGR_eq_seamG]; exact seamRGram_eq y w
  · rw [seamEigR_eq_seamEig]; exact seamEig_four_eq
  · rw [seamEigR_eq_seamEig]; exact seamEig_two_eq
  · rw [seamEigR_eq_seamEig]; exact seamEig_zero_eq
  · rw [seamEigR_eq_seamEig]; exact finrank_seamEig_four
  · rw [seamEigR_eq_seamEig]; exact finrank_seamEig_two
  · rw [seamEigR_eq_seamEig]; exact finrank_seamEig_zero

/-! ## 7. Completeness audit — `#print axioms`

Every declaration in this file is listed; each must depend only on
`{propext, Classical.choice, Quot.sound}`. -/

#print axioms mulCoeff_left_sq
#print axioms mulCoeff_right_sq
#print axioms e_sq_mul
#print axioms mul_e_sq
#print axioms bil_zero_right
#print axioms bil_neg_right
#print axioms bil_basis_mul
#print axioms bil_basis_skew
#print axioms sbp_one_mul
#print axioms sbp_neg_one_mul
#print axioms N_basisPair_split
#print axioms N_basisPair_le
#print axioms N_basisPair_eq_iff
#print axioms basisPair_sq_split
#print axioms sbp_skew
#print axioms sbp_sq_eq_zero_iff
#print axioms seamXm
#print axioms seamXm_ne_zero
#print axioms t1
#print axioms t2
#print axioms t3
#print axioms t4
#print axioms t1_ne_zero
#print axioms t2_ne_zero
#print axioms t3_ne_zero
#print axioms t4_ne_zero
#print axioms seamXm_mul_t1
#print axioms seamXm_mul_t2
#print axioms seamXm_mul_t3
#print axioms seamXm_mul_t4
#print axioms t1_mul_seamXm
#print axioms t2_mul_seamXm
#print axioms t3_mul_seamXm
#print axioms t4_mul_seamXm
#print axioms topIndep_explicit
#print axioms top_linearIndependent
#print axioms topSpan
#print axioms finrank_topSpan
#print axioms sbp_mul_coord
#print axioms sbp_eq_at
#print axioms seam_mker_subset
#print axioms seamLm
#print axioms seamLm_apply
#print axioms seamLm_ker_eq
#print axioms seamRm
#print axioms seamRm_apply
#print axioms topSpan_le_ker_seamRm
#print axioms topSpan_mul_seamXm
#print axioms seamL_skew
#print axioms seamLm_skew
#print axioms seamG
#print axioms seamG_apply
#print axioms seamGram_eq
#print axioms seamG_rayleigh
#print axioms seamEig
#print axioms mem_seamEig
#print axioms seamEig_zero_eq
#print axioms seam_sq_split
#print axioms seamEig_four_eq
#print axioms seamX_mul_e
#print axioms seamG_e_at
#print axioms seamG_e_mid
#print axioms seamG_e0
#print axioms seamG_e1
#print axioms seamG_e2
#print axioms seamG_e3
#print axioms seamG_e8
#print axioms seamG_e9
#print axioms seamG_e10
#print axioms seamG_e11
#print axioms midIdx
#print axioms midIdx_injective
#print axioms mid_linearIndependent
#print axioms midSpan
#print axioms finrank_midSpan
#print axioms seamG_e_mid_all
#print axioms midIdx_spec
#print axioms midSpan_le_seamEig_two
#print axioms projTop
#print axioms projKer
#print axioms projMid
#print axioms proj_decomp
#print axioms projTop_mem
#print axioms projKer_mem
#print axioms e_mem_midSpan
#print axioms e_mem_midSpan_of
#print axioms projMid_mem
#print axioms seamG_projTop
#print axioms seamG_projKer
#print axioms seamG_projMid
#print axioms seamEig_two_eq
#print axioms finrank_seamEig_four
#print axioms finrank_seamEig_two
#print axioms finrank_seamEig_zero
#print axioms seam_gram_spectrum
#print axioms seamG_cubic
#print axioms seamEig_eq_bot_of_ne
#print axioms seam_gram_spectrum_exhaustive
#print axioms potV
#print axioms top_plane_zero_divisor
#print axioms top_generators_are_zero_divisors
#print axioms sum_fin_eight
#print axioms N_cdLo_eq
#print axioms N_cdHi_eq
#print axioms bil_cdLo_cdHi_eq
#print axioms cdLo_coord0_eq
#print axioms cdHi_coord0_eq
#print axioms potV_eq_gram
#print axioms top_plane_on_ridge_of
#print axioms top_plane_on_ridge
#print axioms top_plane_on_ridge_mem
#print axioms mul_sbp_coord
#print axioms seam_xor_idx
#print axioms seam_gram_diag
#print axioms seam_gram_off
#print axioms seam_gram_lr_coord
#print axioms seam_gram_lr
#print axioms seam_gram_lr_m_coord
#print axioms seam_gram_lr_m
#print axioms bil_mul_basis
#print axioms bil_mul_basis_skew
#print axioms sbp_skew_right
#print axioms sbp_sq_eq_zero_iff_right
#print axioms seamR_skew
#print axioms seamGR
#print axioms seamGR_apply
#print axioms seamGR_eq_seamG
#print axioms seamRGram_eq
#print axioms seamRm_ker_eq
#print axioms seamEigR
#print axioms seamEigR_eq_seamEig
#print axioms seamR_gram_spectrum

end QBP.Foundations.SeamSpectrum
