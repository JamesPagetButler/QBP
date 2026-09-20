/-
  QBP.Foundations.HolographicSubalgebra
  =====================================

  **The THEOREM parts of the CTH derived principle `DERIV-holographic`.**

  `DERIV-holographic` read: *"Observers require associativity.  The largest
  associative subalgebra of 𝕆 is ℍ (dim 4).  The 4D gap is the holographic
  boundary."*  It carried constitutional flag 3 (#473 rounds 13–15) because it was
  supported only through Prop 16 via `ℓ`.  The #652 encode (ruling bundle v0.7 §2)
  split it: the proved parts are `DERIV-holographic-theorem` (this file); the
  postulate parts are `POST-observer-associativity` and `POST-observation`; the
  reading is `INTERP-holographic-boundary` — all three OPEN roots with kill lists
  (nothing ruled).  This file proves the provable parts.

  ## What IS claimed here (proved, kernel-checked)

  * **H1 — composition of measurements is multiplication exactly on associative
    sets.**  For left multiplication `L_x : z ↦ x·z` (a genuine `LinearMap`), the
    operator identity `L_x ∘ L_y = L_{x·y}` holds for all `x, y ∈ A` **iff** the
    associator `[x,y,z]` vanishes for all `x, y ∈ A` and all `z`; and the
    "internal" version restricted to `z ∈ A` is equivalent to vanishing of
    `[x,y,z]` on `A³`.  (`lMul_comp_eq_iff_assoc_forall`,
    `lMul_comp_eq_iff_assoc_mem`.)
  * **H2 — quaternion subalgebras of 𝕆 exist, are closed and associative, and
    carry the ℍ multiplication table.**  For orthonormal imaginary `u v : 𝕆`,
    `span ℝ {1, u, v, u·v}` is closed under multiplication
    (`span4_mul_closed`, inherited) and *associative* (`assoc_vanishes_on_span4`,
    inherited from the merged Artin chunk), and its 16 generator products are
    exactly the quaternion table `u² = v² = (uv)² = −1`, `uv = −vu`,
    `u(uv) = −v`, `(uv)v = −u`, `(uv)u = v`, `v(uv) = u`
    (`quaternion_frame_table`).  **General case** — no `decide`, no choice of a
    concrete Fano triple: the table is derived from `imaginary_sq`,
    `anticomm_of_orthogonal_imaginary`, `octonion_alternative`,
    `octonion_flexible` and `octonion_norm_composition`.
  * **H3 — the associator of an orthogonal imaginary triple does not vanish.**
    For pure pairwise-orthogonal `u v w : 𝕆` with `w ⟂ u·v` and nonzero norms,
    `[u,v,w] = 2·((u·v)·w) ≠ 0` (`assoc_orthogonal_triple`,
    `assoc_orthogonal_triple_ne_zero`).  **General case** — derived from the left
    Moufang identity + flexibility + left alternativity + anticommutation of
    orthogonal imaginaries; no `decide`, no G₂-transitivity.  A concrete Fano
    witness (`e₁, e₂, e₄`) is supplied independently by kernel `decide` on the
    integer associator coefficient (`assocCoeffZ_e1_e2_e4_ne_zero`), and the two
    routes are cross-checked to agree.
  * **H3′ — the dimension bound, in the form actually proved.**  If `S` is any
    submodule of 𝕆 that contains a quaternion frame span `span ℝ {1,u,v,uv}`
    (`u v` orthonormal imaginary) and on which the associator vanishes
    identically, then `S = span ℝ {1,u,v,uv}` and `finrank ℝ S = 4`
    (`span4_eq_of_associative`, `finrank_eq_four_of_associative`).  So no
    associative subalgebra of 𝕆 properly extends a quaternion subalgebra.
  * **H4 — the dimension count.**  `finrank ℝ 𝕆 = 8`;
    `finrank ℝ (span ℝ {1,u,v,uv}) = 4` for orthonormal imaginary `u v`
    (`finrank_quaternion_frame`, from genuine linear independence of the
    orthogonal family, not asserted); hence
    `finrank (span) + 4 = finrank 𝕆` (`quaternion_frame_codim_four`).

  ## What is NOT claimed here (explicit non-claims)

  * **"Observers require associativity" is a PHYSICAL POSTULATE.**  It is not a
    theorem, it is not proved here, and nothing in this file asserts it.  It is
    the modelling assumption that an observer/measurement structure must be an
    associative substructure.  H1 is the *mathematical* content that motivates
    it (operator composition = algebra multiplication iff associative), not a
    proof of it.
  * **"The 4D gap is the holographic boundary" is INTERPRETATION.**  This file
    proves a codimension: `8 − 4 = 4`.  It says nothing about boundaries,
    holography, spacetime, or physics.  No metric, energy or crystallisation
    semantics appears in any statement here.
  * **The fully general bound "every associative subalgebra of 𝕆 has dim ≤ 4"
    is NOT proved here.**  What is proved (H3′) is the bound *relative to a
    given quaternion frame*: an associative submodule containing a quaternion
    frame equals it (primary witness `span4_eq_of_associative`).  Closing the
    general statement is DEFERRED, not blocked: it additionally requires an
    orthonormal imaginary pair *inside* an arbitrary associative subalgebra of
    dimension ≥ 3 — a two-step explicit Gram–Schmidt over the existing `bil`
    (elementary; no Mathlib `InnerProductSpace` instance is required).  It is
    deferred per the architecture ruling of 2026-09-07 (a registered
    inner-product structure on `CDAlg`, if ever wanted, is its own foundational
    PR).  That gap is stated, not papered over.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`, zero
  `maxHeartbeats` bump.  `#print axioms` audit at the bottom for every theorem.

  Best practices: `~/Documents/inter/lean-proof-best-practices.md`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import QBP.Foundations.Artin
import QBP.Foundations.Alternator
import QBP.Foundations.CrossProduct
import QBP.Foundations.CDDimension
import QBP.Foundations.NormForm
import QBP.Foundations.CrystalHosting

namespace QBP.Foundations.HolographicSubalgebra

open QBP.Foundations.CDAlg

/-! ## 0. Small reusable facts -/

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A basis vector is nonzero. -/
theorem e_ne_zero (i : Fin (2^n)) : (e i : CDAlg ℝ n) ≠ 0 := by
  intro h
  have hc := congrArg (fun z => CDAlg.coord z i) h
  simp only [e_coord, zero_coord] at hc
  exact one_ne_zero hc

/-- `N 1 = 1`. -/
theorem N_one_cd : N (1 : CDAlg R n) = 1 := by
  rw [N_eq_bil, bil_one_right, one_coord, if_pos rfl]

/-- `N (eᵢ) = 1`. -/
theorem N_e (i : Fin (2^n)) : N (e i : CDAlg ℝ n) = 1 := by
  rw [N_eq_bil, bil_e, if_pos rfl]

/-- Anticommutation, in the "solved" form: for orthogonal imaginary `x y`,
    `y·x = −(x·y)`.  (Repackaging of `anticomm_of_orthogonal_imaginary`.) -/
theorem mul_comm_neg {x y : CDAlg ℝ n}
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) (hxy : bil x y = 0) :
    y * x = -(x * y) := by
  have h := anticomm_of_orthogonal_imaginary hx hy hxy
  rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
  exact h

/-! ## 1. H1 — left multiplication and the associativity criterion

`L_x : z ↦ x·z` is the "apply the measurement `x`" operator.  Composing two such
operators is the operator of the *product* exactly on associative sets — this is
the theorem-shaped form of "measurements compose as multiplication only inside an
associative substructure".  Both directions are stated: the operator identity
(`z` ranges over all of the algebra) and the internal identity (`z ∈ A`). -/

/-- **Left multiplication as an `R`-linear operator**, `L_x(z) = x·z`. -/
def lMul (x : CDAlg R n) : CDAlg R n →ₗ[R] CDAlg R n where
  toFun z := x * z
  map_add' y z := mul_add_right x y z
  map_smul' r z := by
    simp only [RingHom.id_apply]
    exact mul_smul_right r x z

@[simp] theorem lMul_apply (x z : CDAlg R n) : lMul x z = x * z := rfl

/-- **H1 (operator form).**  For a set `A`, the composition law
    `L_x ∘ L_y = L_{x·y}` holds for all `x y ∈ A` **iff** the associator
    `[x,y,z] = (x·y)·z − x·(y·z)` vanishes for all `x y ∈ A` and *every* `z`. -/
theorem lMul_comp_eq_iff_assoc_forall (A : Set (CDAlg R n)) :
    (∀ x ∈ A, ∀ y ∈ A, (lMul x).comp (lMul y) = lMul (x * y)) ↔
      (∀ x ∈ A, ∀ y ∈ A, ∀ z : CDAlg R n, assoc x y z = 0) := by
  constructor
  · intro h x hx y hy z
    have hz := congrArg (fun f : CDAlg R n →ₗ[R] CDAlg R n => f z) (h x hx y hy)
    simp only [LinearMap.comp_apply, lMul_apply] at hz
    rw [assoc, sub_eq_zero]
    exact hz.symm
  · intro h x hx y hy
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, lMul_apply]
    have hz := h x hx y hy z
    rw [assoc, sub_eq_zero] at hz
    exact hz.symm

/-- **H1 (internal form).**  The composition law restricted to arguments drawn
    from `A` (`x y z ∈ A`) is equivalent to vanishing of the associator on `A³`.

    Note the two forms are genuinely different statements: the operator form
    implies the internal form (`lMul_comp_of_forall`), but not conversely — a set
    can associate internally while failing to associate against outside
    elements.  Neither is stated as a mixed-quantifier "iff". -/
theorem lMul_comp_eq_iff_assoc_mem (A : Set (CDAlg R n)) :
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, lMul x (lMul y z) = lMul (x * y) z) ↔
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, assoc x y z = 0) := by
  constructor
  · intro h x hx y hy z hz
    have hzz := h x hx y hy z hz
    simp only [lMul_apply] at hzz
    rw [assoc, sub_eq_zero]
    exact hzz.symm
  · intro h x hx y hy z hz
    have hzz := h x hx y hy z hz
    rw [assoc, sub_eq_zero] at hzz
    simp only [lMul_apply]
    exact hzz.symm

/-- The operator form implies the internal form (the converse fails in general). -/
theorem lMul_comp_of_forall {A : Set (CDAlg R n)}
    (h : ∀ x ∈ A, ∀ y ∈ A, (lMul x).comp (lMul y) = lMul (x * y)) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, lMul x (lMul y z) = lMul (x * y) z := by
  intro x hx y hy z _
  have hz := congrArg (fun f : CDAlg R n →ₗ[R] CDAlg R n => f z) (h x hx y hy)
  simpa using hz

/-! ## 2. H2 — the quaternion frame `{1, u, v, u·v}` in 𝕆

`u v : 𝕆` orthonormal imaginary (`u₀ = v₀ = 0`, `⟨u,v⟩ = 0`, `N u = N v = 1`).
Everything in this section is proved for a GENERAL such pair — no Fano triple is
chosen and no `decide` is used. -/

section Frame

variable {u v w : CDAlg ℝ 3}

/-- For pure `v` orthogonal to `u`, the product `u·v` is pure. -/
theorem mul_coord_zero (hv0 : v.coord 0 = 0) (huv : bil u v = 0) :
    (u * v).coord 0 = 0 := by
  rw [QBP.Foundations.CrossProduct.reCoord_mul_pure u v hv0, huv, neg_zero]

/-- `N (u·v) = N u · N v` at 𝕆 (composition), specialised to unit vectors. -/
theorem N_mul_unit (hNu : N u = 1) (hNv : N v = 1) : N (u * v) = 1 := by
  rw [octonion_norm_composition, hNu, hNv, mul_one]

/-- `u·u = −1` for a pure unit `u`. -/
theorem sq_eq_neg_one (hu0 : u.coord 0 = 0) (hNu : N u = 1) :
    u * u = (-1 : ℝ) • (1 : CDAlg ℝ 3) := by
  rw [imaginary_sq u hu0, hNu]

/-- `u·(u·v) = −v` (left alternativity + `u² = −1`). -/
theorem u_mul_uv (hu0 : u.coord 0 = 0) (hNu : N u = 1) :
    u * (u * v) = (-1 : ℝ) • v := by
  rw [← (octonion_alternative u v).1, sq_eq_neg_one hu0 hNu, mul_smul_left, cd_one_mul]

/-- `(u·v)·v = −u` (right alternativity + `v² = −1`). -/
theorem uv_mul_v (hv0 : v.coord 0 = 0) (hNv : N v = 1) :
    (u * v) * v = (-1 : ℝ) • u := by
  rw [(octonion_alternative u v).2, sq_eq_neg_one hv0 hNv, mul_smul_right, cd_mul_one]

/-- `(u·v)·u = v` (flexibility + anticommutation + left alternativity). -/
theorem uv_mul_u (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) : (u * v) * u = v := by
  rw [octonion_flexible u v, mul_comm_neg hu0 hv0 huv, mul_neg, u_mul_uv hu0 hNu,
    neg_smul, one_smul, neg_neg]

/-- `v·(u·v) = u` (anticommutation + left alternativity). -/
theorem v_mul_uv (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNv : N v = 1) : v * (u * v) = u := by
  have hvu : v * u = -(u * v) := mul_comm_neg hu0 hv0 huv
  have h : v * (v * u) = (-1 : ℝ) • u := u_mul_uv (u := v) (v := u) hv0 hNv
  rw [hvu, mul_neg, neg_smul, one_smul] at h
  exact neg_inj.mp h

/-- `(u·v)·(u·v) = −1`: the third quaternion imaginary unit squares to `−1`. -/
theorem uv_sq (hv0 : v.coord 0 = 0) (huv : bil u v = 0) (hNu : N u = 1) (hNv : N v = 1) :
    (u * v) * (u * v) = (-1 : ℝ) • (1 : CDAlg ℝ 3) :=
  sq_eq_neg_one (mul_coord_zero hv0 huv) (N_mul_unit hNu hNv)

/-- **H2 — the quaternion multiplication table.**  For orthonormal imaginary
    `u v : 𝕆`, the four elements `1, u, v, u·v` multiply exactly as
    `1, i, j, k` do in ℍ:

    `u² = v² = (uv)² = −1`,  `u·v = −(v·u)`,
    `u·(uv) = −v`,  `(uv)·u = v`,  `v·(uv) = u`,  `(uv)·v = −u`.

    Proved for a general orthonormal imaginary pair from the CD/octonion laws
    (`imaginary_sq`, `anticomm_of_orthogonal_imaginary`, `octonion_alternative`,
    `octonion_flexible`, `octonion_norm_composition`) — no basis, no `decide`. -/
theorem quaternion_frame_table
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1) :
    u * u = (-1 : ℝ) • (1 : CDAlg ℝ 3) ∧
    v * v = (-1 : ℝ) • (1 : CDAlg ℝ 3) ∧
    (u * v) * (u * v) = (-1 : ℝ) • (1 : CDAlg ℝ 3) ∧
    v * u = -(u * v) ∧
    u * (u * v) = (-1 : ℝ) • v ∧
    (u * v) * u = v ∧
    v * (u * v) = u ∧
    (u * v) * v = (-1 : ℝ) • u :=
  ⟨sq_eq_neg_one hu0 hNu, sq_eq_neg_one hv0 hNv, uv_sq hv0 huv hNu hNv,
   mul_comm_neg hu0 hv0 huv, u_mul_uv hu0 hNu, uv_mul_u hu0 hv0 huv hNu,
   v_mul_uv hu0 hv0 huv hNv, uv_mul_v hv0 hNv⟩

/-- **H2 (subalgebra form).**  `span ℝ {1, u, v, u·v}` is closed under
    multiplication and every associator of three of its elements vanishes: it is
    an associative subalgebra of 𝕆.  (Both halves are inherited from the merged
    Artin chunks `span4_mul_closed` / `assoc_vanishes_on_span4`, which hold for
    an arbitrary generating pair; orthonormality is what makes the span
    4-dimensional, see `finrank_quaternion_frame`.) -/
theorem quaternion_frame_subalgebra (u v : CDAlg ℝ 3) :
    (∀ a ∈ Submodule.span ℝ (gen4 u v), ∀ b ∈ Submodule.span ℝ (gen4 u v),
        a * b ∈ Submodule.span ℝ (gen4 u v)) ∧
    (∀ a ∈ Submodule.span ℝ (gen4 u v), ∀ b ∈ Submodule.span ℝ (gen4 u v),
        ∀ c ∈ Submodule.span ℝ (gen4 u v), (a * b) * c = a * (b * c)) := by
  refine ⟨fun a ha b hb => span4_mul_closed u v ha hb, fun a ha b hb c hc => ?_⟩
  have h := assoc_vanishes_on_span4 u v ha hb hc
  rw [assoc, sub_eq_zero] at h
  exact h

/-- **H1 ∘ H2.**  The measurement-composition law `L_a(L_b c) = L_{a·b} c` holds
    throughout a quaternion frame span — a non-vacuous instance of H1. -/
theorem lMul_comp_on_quaternion_frame (u v : CDAlg ℝ 3) :
    ∀ a ∈ Submodule.span ℝ (gen4 u v), ∀ b ∈ Submodule.span ℝ (gen4 u v),
      ∀ c ∈ Submodule.span ℝ (gen4 u v), lMul a (lMul b c) = lMul (a * b) c := by
  refine (lMul_comp_eq_iff_assoc_mem (A := (Submodule.span ℝ (gen4 u v) : Set (CDAlg ℝ 3)))).mpr ?_
  intro a ha b hb c hc
  exact assoc_vanishes_on_span4 u v ha hb hc

/-! ## 3. H4 — orthonormality of the frame and its dimension -/

/-- `⟨1, x⟩ = x₀`. -/
theorem bil_one_left (x : CDAlg R n) : bil (1 : CDAlg R n) x = x.coord 0 := by
  rw [QBP.Foundations.NormForm.bil_symm, bil_one_right]

/-- `⟨u, u·v⟩ = 0` for orthonormal imaginary `u v`. -/
theorem bil_u_uv (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) : bil u (u * v) = 0 := by
  have hpure : (u * (u * v)).coord 0 = - bil u (u * v) :=
    QBP.Foundations.CrossProduct.reCoord_mul_pure u (u * v) (mul_coord_zero hv0 huv)
  rw [u_mul_uv hu0 hNu, smul_coord, hv0, mul_zero] at hpure
  linarith

/-- `⟨v, u·v⟩ = 0` for orthonormal imaginary `u v`. -/
theorem bil_v_uv (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNv : N v = 1) : bil v (u * v) = 0 := by
  have hpure : (v * (u * v)).coord 0 = - bil v (u * v) :=
    QBP.Foundations.CrossProduct.reCoord_mul_pure v (u * v) (mul_coord_zero hv0 huv)
  rw [v_mul_uv hu0 hv0 huv hNv, hu0] at hpure
  linarith

/-- **H4 (independence).**  For orthonormal imaginary `u v`, the family
    `1, u, v, u·v` is linearly independent over ℝ.  Proved from pairwise
    `bil`-orthogonality and `N = 1` — not asserted. -/
theorem quaternion_frame_linearIndependent
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1) :
    LinearIndependent ℝ ![(1 : CDAlg ℝ 3), u, v, u * v] := by
  have huv0 : (u * v).coord 0 = 0 := mul_coord_zero hv0 huv
  have hNuv : N (u * v) = 1 := N_mul_unit hNu hNv
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hg
  -- pair the relation against each frame vector
  have key : ∀ b : CDAlg ℝ 3,
      g 0 * bil b 1 + g 1 * bil b u + g 2 * bil b v + g 3 * bil b (u * v) = 0 := by
    intro b
    have h := congrArg (fun z => bil b z) hg
    simp only [bil_add_right, bil_smul_right] at h
    simpa using h
  have h1 := key 1
  have h2 := key u
  have h3 := key v
  have h4 := key (u * v)
  rw [bil_one_left, bil_one_left, bil_one_left, bil_one_left, one_coord, if_pos rfl,
    hu0, hv0, huv0] at h1
  rw [bil_one_right, hu0, ← N_eq_bil, hNu, huv, bil_u_uv hu0 hv0 huv hNu] at h2
  rw [bil_one_right, hv0, QBP.Foundations.NormForm.bil_symm v u, huv, ← N_eq_bil, hNv,
    bil_v_uv hu0 hv0 huv hNv] at h3
  rw [bil_one_right, huv0, QBP.Foundations.NormForm.bil_symm (u * v) u,
    bil_u_uv hu0 hv0 huv hNu, QBP.Foundations.NormForm.bil_symm (u * v) v,
    bil_v_uv hu0 hv0 huv hNv, ← N_eq_bil, hNuv] at h4
  fin_cases i
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4

/-- `gen4 u v` is the range of the frame family. -/
theorem gen4_eq_range (u v : CDAlg ℝ 3) :
    gen4 u v = Set.range ![(1 : CDAlg ℝ 3), u, v, u * v] := by
  ext z
  simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- **H4 (dimension).**  For orthonormal imaginary `u v : 𝕆`, the quaternion
    frame span is exactly 4-dimensional. -/
theorem finrank_quaternion_frame
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1) :
    Module.finrank ℝ (Submodule.span ℝ (gen4 u v)) = 4 := by
  rw [gen4_eq_range u v,
    finrank_span_eq_card (quaternion_frame_linearIndependent hu0 hv0 huv hNu hNv)]
  simp

/-- **H4 (the codimension, additive form — no `Nat` truncation).**
    `dim (span {1,u,v,uv}) + 4 = dim 𝕆`, i.e. `4 + 4 = 8`. -/
theorem quaternion_frame_codim_four
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1) :
    Module.finrank ℝ (Submodule.span ℝ (gen4 u v)) + 4
      = Module.finrank ℝ (CDAlg ℝ 3) := by
  rw [finrank_quaternion_frame hu0 hv0 huv hNu hNv,
    QBP.Foundations.CDDimension.finrank_cdAlg]
  norm_num

/-- The same codimension in subtraction form (both sides are concrete numerals,
    so the `ℕ` subtraction `8 − 4` is exact). -/
theorem quaternion_frame_codim_four'
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1) :
    Module.finrank ℝ (CDAlg ℝ 3) - Module.finrank ℝ (Submodule.span ℝ (gen4 u v)) = 4 := by
  rw [finrank_quaternion_frame hu0 hv0 huv hNu hNv,
    QBP.Foundations.CDDimension.finrank_cdAlg]
  norm_num

/-! ## 4. H3 — the associator of an orthogonal imaginary triple

The key structural identity: for pure pairwise-orthogonal `u v w` with
`w ⟂ u·v`,  `(u·v)·w = −u·(v·w)`, so `[u,v,w] = 2·((u·v)·w) ≠ 0`.

Route (all inputs are merged kernel theorems, no `decide`, no G₂):
1. `(u·w)·u = N u • w`      — flexibility + anticommutation + left alternativity;
2. `u·(w·(u·v)) = ((u·w)·u)·v`  — LEFT MOUFANG;
3. `w·(u·v) = −((u·v)·w)`   — anticommutation (**this is where `w ⟂ u·v` enters**);
4. hence `u·((u·v)·w) = N u • (v·w)`;
5. multiply by `u` again and use `u·u = −N u`: `(u·v)·w = −u·(v·w)`. -/

/-- Step 1: `(u·w)·u = N u • w` for pure orthogonal `u w`. -/
theorem uwu_eq (hu0 : u.coord 0 = 0) (hw0 : w.coord 0 = 0) (huw : bil u w = 0) :
    (u * w) * u = (N u) • w := by
  rw [octonion_flexible u w, mul_comm_neg hu0 hw0 huw, mul_neg,
    ← (octonion_alternative u w).1, imaginary_sq u hu0, mul_smul_left, cd_one_mul,
    neg_smul, neg_neg]

/-- **H3 (core identity).**  For pure pairwise-orthogonal `u v w : 𝕆` with
    `w ⟂ u·v` and `N u ≠ 0`:  `u·(v·w) = −((u·v)·w)`. -/
theorem mul_assoc_flip
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (hw0 : w.coord 0 = 0)
    (huv : bil u v = 0) (huw : bil u w = 0) (hvw : bil v w = 0)
    (hwuv : bil (u * v) w = 0) (hNu : N u ≠ 0) :
    u * (v * w) = -((u * v) * w) := by
  have huv0 : (u * v).coord 0 = 0 := mul_coord_zero hv0 huv
  have hwv : w * v = -(v * w) := mul_comm_neg hv0 hw0 hvw
  have hwuv' : w * (u * v) = -((u * v) * w) := mul_comm_neg huv0 hw0 hwuv
  -- step 4
  have h4 : u * ((u * v) * w) = (N u) • (v * w) := by
    have hmou : u * (w * (u * v)) = ((u * w) * u) * v := octonion_moufang_left u w v
    have hL : u * (w * (u * v)) = -(u * ((u * v) * w)) := by rw [hwuv', mul_neg]
    have hR : ((u * w) * u) * v = -((N u) • (v * w)) := by
      rw [uwu_eq hu0 hw0 huw, mul_smul_left, hwv, smul_neg]
    rw [hL, hR] at hmou
    exact neg_inj.mp hmou
  -- step 5
  have h6 : (-(N u)) • ((u * v) * w) = (N u) • (u * (v * w)) := by
    calc (-(N u)) • ((u * v) * w)
        = (u * u) * ((u * v) * w) := by
          rw [imaginary_sq u hu0, mul_smul_left, cd_one_mul]
      _ = u * (u * ((u * v) * w)) := (octonion_alternative u ((u * v) * w)).1
      _ = u * ((N u) • (v * w)) := by rw [h4]
      _ = (N u) • (u * (v * w)) := mul_smul_right _ _ _
  have h8 : (N u) • ((u * v) * w + u * (v * w)) = 0 := by
    rw [smul_add, ← h6, ← add_smul]
    simp
  have h9 : (u * v) * w + u * (v * w) = 0 := eq_zero_of_smul_eq_zero hNu h8
  rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
  exact h9

/-- **H3 (associator value).**  `[u,v,w] = 2·((u·v)·w)` for a pure
    pairwise-orthogonal triple with `w ⟂ u·v`. -/
theorem assoc_orthogonal_triple
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (hw0 : w.coord 0 = 0)
    (huv : bil u v = 0) (huw : bil u w = 0) (hvw : bil v w = 0)
    (hwuv : bil (u * v) w = 0) (hNu : N u ≠ 0) :
    assoc u v w = (2 : ℝ) • ((u * v) * w) := by
  rw [assoc, mul_assoc_flip hu0 hv0 hw0 huv huw hvw hwuv hNu, sub_neg_eq_add, two_smul]

/-- **H3 (the payload).**  The associator of a pure pairwise-orthogonal triple
    `u v w` of NONZERO octonions with `w ⟂ u·v` never vanishes:
    `[u,v,w] = 2·((u·v)·w) ≠ 0`, because `N((u·v)·w) = N u · N v · N w ≠ 0`.

    Equivalently `(u·v)·w = −u·(v·w) ≠ u·(v·w)`.  So a fourth imaginary
    direction orthogonal to a quaternion frame *always* breaks associativity. -/
theorem assoc_orthogonal_triple_ne_zero
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (hw0 : w.coord 0 = 0)
    (huv : bil u v = 0) (huw : bil u w = 0) (hvw : bil v w = 0)
    (hwuv : bil (u * v) w = 0)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    assoc u v w ≠ 0 := by
  have hNu : N u ≠ 0 := fun h => hu ((alt_N_eq_zero_iff u).mp h)
  have hNv : N v ≠ 0 := fun h => hv ((alt_N_eq_zero_iff v).mp h)
  have hNw : N w ≠ 0 := fun h => hw ((alt_N_eq_zero_iff w).mp h)
  intro hzero
  rw [assoc_orthogonal_triple hu0 hv0 hw0 huv huw hvw hwuv hNu] at hzero
  have hX : (u * v) * w = 0 := eq_zero_of_smul_eq_zero two_ne_zero hzero
  have hN : N ((u * v) * w) = N u * N v * N w := by
    rw [octonion_norm_composition, octonion_norm_composition]
  rw [hX, (alt_N_eq_zero_iff (0 : CDAlg ℝ 3)).mpr rfl] at hN
  exact (mul_ne_zero (mul_ne_zero hNu hNv) hNw) hN.symm

end Frame

/-! ## 5. H3′ — no associative extension of a quaternion frame

Because the frame `{1, u, v, u·v}` is ORTHONORMAL, the orthogonal projection onto
its span is written down explicitly (no inner-product-space machinery needed).
Any element of an associative submodule containing the frame therefore splits as
`z = P z + r` with `r` pure and orthogonal to `1, u, v, u·v`; H3 forces `r = 0`. -/

/-- Explicit orthogonal projection onto the frame span (correct because the frame
    `{1, u, v, u·v}` is orthonormal). -/
def proj4 (u v z : CDAlg ℝ 3) : CDAlg ℝ 3 :=
  (bil z 1) • (1 : CDAlg ℝ 3) + (bil z u) • u + (bil z v) • v + (bil z (u * v)) • (u * v)

theorem proj4_mem (u v z : CDAlg ℝ 3) : proj4 u v z ∈ Submodule.span ℝ (gen4 u v) := by
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact Submodule.smul_mem _ _ (one_mem_span_gen4 u v)
  · exact Submodule.smul_mem _ _ (x_mem_span_gen4 u v)
  · exact Submodule.smul_mem _ _ (y_mem_span_gen4 u v)
  · exact Submodule.smul_mem _ _ (xy_mem_span_gen4 u v)

section Residual

variable {u v : CDAlg ℝ 3}

/-- The `bil`-pairing of `proj4 u v z` with any `b`, expanded. -/
theorem bil_proj4 (u v z b : CDAlg ℝ 3) :
    bil (proj4 u v z) b
      = bil z 1 * bil (1 : CDAlg ℝ 3) b + bil z u * bil u b + bil z v * bil v b
        + bil z (u * v) * bil (u * v) b := by
  simp only [proj4, bil_add_left, bil_smul_left]

/-- The residual `z − P z` is orthogonal to `1` (hence pure). -/
theorem residual_orth_one (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0)
    (huv : bil u v = 0) (z : CDAlg ℝ 3) :
    bil (z - proj4 u v z) (1 : CDAlg ℝ 3) = 0 := by
  have huv0 : (u * v).coord 0 = 0 := mul_coord_zero hv0 huv
  rw [QBP.Foundations.CrossProduct.bil_sub_left, bil_proj4]
  simp only [bil_one_right]
  rw [one_coord, if_pos rfl, hu0, hv0, huv0]
  ring

/-- The residual is orthogonal to `u`. -/
theorem residual_orth_u (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0)
    (huv : bil u v = 0) (hNu : N u = 1) (z : CDAlg ℝ 3) :
    bil (z - proj4 u v z) u = 0 := by
  rw [QBP.Foundations.CrossProduct.bil_sub_left, bil_proj4, bil_one_left, hu0, ← N_eq_bil, hNu,
    QBP.Foundations.NormForm.bil_symm v u, huv,
    QBP.Foundations.NormForm.bil_symm (u * v) u, bil_u_uv hu0 hv0 huv hNu]
  ring

/-- The residual is orthogonal to `v`. -/
theorem residual_orth_v (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0)
    (huv : bil u v = 0) (hNv : N v = 1) (z : CDAlg ℝ 3) :
    bil (z - proj4 u v z) v = 0 := by
  rw [QBP.Foundations.CrossProduct.bil_sub_left, bil_proj4, bil_one_left, hv0, ← N_eq_bil, hNv,
    huv, QBP.Foundations.NormForm.bil_symm (u * v) v, bil_v_uv hu0 hv0 huv hNv]
  ring

/-- The residual is orthogonal to `u·v`. -/
theorem residual_orth_uv (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0)
    (huv : bil u v = 0) (hNu : N u = 1) (hNv : N v = 1) (z : CDAlg ℝ 3) :
    bil (z - proj4 u v z) (u * v) = 0 := by
  have huv0 : (u * v).coord 0 = 0 := mul_coord_zero hv0 huv
  have hNuv : N (u * v) = 1 := N_mul_unit hNu hNv
  rw [QBP.Foundations.CrossProduct.bil_sub_left, bil_proj4, bil_one_left, huv0,
    bil_u_uv hu0 hv0 huv hNu, bil_v_uv hu0 hv0 huv hNv, ← N_eq_bil, hNuv]
  ring

/-- **H3′ — no associative extension.**  Let `u v : 𝕆` be orthonormal imaginary
    and let `S` be a submodule of 𝕆 containing the quaternion frame span
    `span ℝ {1,u,v,u·v}`.  If the associator vanishes on every triple of elements
    of `S`, then `S` is exactly that span.

    In words: **no associative subalgebra of 𝕆 properly contains a quaternion
    subalgebra.**  (The proof: any `z ∈ S` splits as `P z + r` with `r ∈ S` pure
    and orthogonal to `1, u, v, u·v`; if `r ≠ 0` then `[u,v,r] ≠ 0` by H3,
    contradicting associativity of `S`.) -/
theorem span4_eq_of_associative
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1)
    (S : Submodule ℝ (CDAlg ℝ 3))
    (hsub : Submodule.span ℝ (gen4 u v) ≤ S)
    (hassoc : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, assoc a b c = 0) :
    S = Submodule.span ℝ (gen4 u v) := by
  refine le_antisymm (fun z hz => ?_) hsub
  set r : CDAlg ℝ 3 := z - proj4 u v z with hr
  have hrS : r ∈ S := Submodule.sub_mem S hz (hsub (proj4_mem u v z))
  have hzP : z = proj4 u v z + r := by rw [hr]; abel
  by_cases hr0 : r = 0
  · rw [hzP, hr0, add_zero]; exact proj4_mem u v z
  · exfalso
    have hu : u ≠ 0 := fun h => by
      rw [h, (alt_N_eq_zero_iff (0 : CDAlg ℝ 3)).mpr rfl] at hNu; exact zero_ne_one hNu
    have hv : v ≠ 0 := fun h => by
      rw [h, (alt_N_eq_zero_iff (0 : CDAlg ℝ 3)).mpr rfl] at hNv; exact zero_ne_one hNv
    have hr1 : bil r (1 : CDAlg ℝ 3) = 0 := residual_orth_one hu0 hv0 huv z
    have hr0' : r.coord 0 = 0 := by rw [← bil_one_right r]; exact hr1
    have hru : bil u r = 0 := by
      rw [QBP.Foundations.NormForm.bil_symm]
      exact residual_orth_u hu0 hv0 huv hNu z
    have hrv : bil v r = 0 := by
      rw [QBP.Foundations.NormForm.bil_symm]
      exact residual_orth_v hu0 hv0 huv hNv z
    have hruv : bil (u * v) r = 0 := by
      rw [QBP.Foundations.NormForm.bil_symm]
      exact residual_orth_uv hu0 hv0 huv hNu hNv z
    have hne := assoc_orthogonal_triple_ne_zero hu0 hv0 hr0' huv hru hrv hruv hu hv hr0
    exact hne (hassoc u (hsub (x_mem_span_gen4 u v)) v (hsub (y_mem_span_gen4 u v)) r hrS)

/-- **H3′ (dimension form).**  Any associative submodule of 𝕆 containing a
    quaternion frame has dimension exactly 4 — the associativity bound is
    saturated by ℍ and cannot be exceeded in this direction. -/
theorem finrank_eq_four_of_associative
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1)
    (S : Submodule ℝ (CDAlg ℝ 3))
    (hsub : Submodule.span ℝ (gen4 u v) ≤ S)
    (hassoc : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, assoc a b c = 0) :
    Module.finrank ℝ S = 4 := by
  rw [span4_eq_of_associative hu0 hv0 huv hNu hNv S hsub hassoc]
  exact finrank_quaternion_frame hu0 hv0 huv hNu hNv

/-- **H3′ (contrapositive — the deliverable in words).**  If a submodule `S` of 𝕆
    contains a quaternion frame span AND some element outside it, then `S` is NOT
    associative: some triple of its elements fails to re-associate.  So a maximal
    associative submodule of 𝕆 containing a quaternion frame *is* that frame span,
    of dimension 4. -/
theorem not_associative_of_gt_span4
    (hu0 : u.coord 0 = 0) (hv0 : v.coord 0 = 0) (huv : bil u v = 0)
    (hNu : N u = 1) (hNv : N v = 1)
    (S : Submodule ℝ (CDAlg ℝ 3))
    (hsub : Submodule.span ℝ (gen4 u v) ≤ S)
    {z : CDAlg ℝ 3} (hzS : z ∈ S) (hzout : z ∉ Submodule.span ℝ (gen4 u v)) :
    ¬ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, assoc a b c = 0) := by
  intro hassoc
  exact hzout (span4_eq_of_associative hu0 hv0 huv hNu hNv S hsub hassoc ▸ hzS)

end Residual

/-! ## 6. Concrete Fano witness (independent kernel `decide` cross-check)

The general theorems above are proved structurally.  This section supplies the
smallest concrete instance — `u = e₁`, `v = e₂`, `w = e₄` — twice: once by
instantiating the general theorem, once by a kernel `decide` on the integer
associator coefficient.  Agreement of the two routes is a genuine cross-check of
the structural proof. -/

/-- Octonion basis index `1`. -/
def i1 : Fin (2^3) := ⟨1, by norm_num⟩
/-- Octonion basis index `2`. -/
def i2 : Fin (2^3) := ⟨2, by norm_num⟩
/-- Octonion basis index `4`. -/
def i4 : Fin (2^3) := ⟨4, by norm_num⟩

/-- **Kernel `decide`:** the integer associator coefficient of the basis triple
    `(e₁, e₂, e₄)` is `2`, in particular nonzero. -/
theorem assocCoeffZ_e1_e2_e4 : assocCoeffZ 3 i1 i2 i4 = 2 := by decide

/-- **Concrete witness (decide route).**  `[e₁, e₂, e₄] ≠ 0` in 𝕆. -/
theorem assoc_e1_e2_e4_ne_zero :
    assoc (e i1 : CDAlg ℝ 3) (e i2) (e i4) ≠ 0 := by
  rw [assoc_e, assocCoeffZ_e1_e2_e4]
  intro h
  have h2 : (e (i1 ^^^ i2 ^^^ i4) : CDAlg ℝ 3) = 0 := by
    refine eq_zero_of_smul_eq_zero (r := ((2 : Int) : ℝ)) ?_ h
    norm_num
  exact e_ne_zero _ h2

/-- The hypotheses of the general theorem are satisfied by `(e₁, e₂, e₄)`. -/
theorem fano_triple_hypotheses :
    (e i1 : CDAlg ℝ 3).coord 0 = 0 ∧ (e i2 : CDAlg ℝ 3).coord 0 = 0 ∧
    (e i4 : CDAlg ℝ 3).coord 0 = 0 ∧
    bil (e i1 : CDAlg ℝ 3) (e i2) = 0 ∧ bil (e i1 : CDAlg ℝ 3) (e i4) = 0 ∧
    bil (e i2 : CDAlg ℝ 3) (e i4) = 0 ∧
    bil ((e i1 : CDAlg ℝ 3) * e i2) (e i4) = 0 ∧
    (e i1 : CDAlg ℝ 3) ≠ 0 ∧ (e i2 : CDAlg ℝ 3) ≠ 0 ∧ (e i4 : CDAlg ℝ 3) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, e_ne_zero _, e_ne_zero _, e_ne_zero _⟩
  · rw [e_coord, if_neg (by decide)]
  · rw [e_coord, if_neg (by decide)]
  · rw [e_coord, if_neg (by decide)]
  · rw [bil_e, if_neg (by decide)]
  · rw [bil_e, if_neg (by decide)]
  · rw [bil_e, if_neg (by decide)]
  · rw [e_mul_e, bil_smul_left, bil_e, if_neg (by decide : ¬ (i1 ^^^ i2) = i4), mul_zero]

/-- **Concrete witness (structural route).**  The general theorem
    `assoc_orthogonal_triple_ne_zero`, instantiated at the Fano triple
    `(e₁, e₂, e₄)`, gives the same conclusion as the kernel-`decide` route —
    an independent cross-check of the structural proof. -/
theorem assoc_e1_e2_e4_ne_zero_structural :
    assoc (e i1 : CDAlg ℝ 3) (e i2) (e i4) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := fano_triple_hypotheses
  exact assoc_orthogonal_triple_ne_zero h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-- The Fano pair `(e₁, e₂)` is an orthonormal imaginary pair, so it really does
    generate a 4-dimensional quaternion subalgebra of 𝕆 — the general H2/H4
    hypotheses are non-vacuous. -/
theorem fano_pair_frame :
    Module.finrank ℝ (Submodule.span ℝ (gen4 (e i1 : CDAlg ℝ 3) (e i2))) = 4 := by
  refine finrank_quaternion_frame ?_ ?_ ?_ ?_ ?_
  · rw [e_coord, if_neg (by decide)]
  · rw [e_coord, if_neg (by decide)]
  · rw [bil_e, if_neg (by decide)]
  · exact N_e _
  · exact N_e _

/-- **H1 non-vacuity: the composition law genuinely FAILS on all of 𝕆.**  Taking
    `A = 𝕆` in `lMul_comp_eq_iff_assoc_forall`, the operator identity
    `L_x ∘ L_y = L_{x·y}` does not hold for all octonions — witnessed by the
    triple `(e₁, e₂, e₄)`.  So H1's equivalence is a real dichotomy, not a
    statement that happens to be true on both sides. -/
theorem lMul_comp_fails_on_octonions :
    ¬ (∀ x ∈ (Set.univ : Set (CDAlg ℝ 3)), ∀ y ∈ Set.univ,
        (lMul x).comp (lMul y) = lMul (x * y)) := by
  intro h
  have hall := (lMul_comp_eq_iff_assoc_forall (Set.univ : Set (CDAlg ℝ 3))).mp h
  exact assoc_e1_e2_e4_ne_zero
    (hall (e i1) (Set.mem_univ _) (e i2) (Set.mem_univ _) (e i4))

/-! ## 8. The ρ-invariant octonion doubles `ℍ ⊕ ℍ·ℓ ⊂ 𝕊` (#6)

The heterogeneous confirmer's verdict of 2026-09-19 (§4.3, §8 item 6) refuted
the claim that there are *exactly seven* `ρ`-invariant octonion subalgebras of 𝕊
(the coordinate-aligned Fano doubles) and replaced it by the true statement:

> for **every** quaternion subalgebra `ℍ = span ℝ {1, p, q, pq} ⊂ 𝕆` — not only
> the seven Fano-aligned ones — the Cayley–Dickson double `ℍ ⊕ ℍ·ℓ ⊂ 𝕊` is a
> subalgebra containing `1` and `ℓ`, and it is invariant under the order-3
> automorphism `ρ = rotAut3`.

That is what this section proves, for an **arbitrary** pair `p q : 𝕆` (closure,
`*`-closure, `1`, `ℓ`) and, where 4-dimensionality of `ℍ` is needed, for an
orthonormal imaginary pair (properness).  The reason `ρ` preserves the double is
structural and is visible in `rotLo`/`rotHi`: `ρ` acts on the pair split by a
**plane rotation mixing the two halves by real scalars**, `(a, b) ↦ (ca − sb + λ1,
sa + cb + μ1)`, so it preserves `S ⊕ S` for *any* submodule `S ⊆ 𝕆` containing
`1`.  Multiplicative closure is the Cayley–Dickson doubling formula plus closure
of `ℍ` under the octonion product and under conjugation.

**Non-claims.** Nothing here says the double is 8-dimensional, that it is
alternative or a composition algebra, or that the family of such doubles is
finite — the confirmer's measurement says the family is a continuum, and no
counting statement is made in either direction.  Nor is `ρ`-invariance of the
double read as selecting anything physical (INTERP-holographic-boundary stays
OPEN). -/

section RhoInvariantDoubles

open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

/-- **The Cayley–Dickson double of a quaternion span**, `ℍ ⊕ ℍ·ℓ ⊂ 𝕊`, written
    as the set of sedenions both of whose Cayley–Dickson halves lie in
    `ℍ = span ℝ {1, p, q, p·q}`. -/
def quatDouble (p q : CDAlg ℝ 3) : Set (CDAlg ℝ 4) :=
  {x | cdLo x ∈ Submodule.span ℝ (gen4 p q) ∧ cdHi x ∈ Submodule.span ℝ (gen4 p q)}

variable (p q : CDAlg ℝ 3)

theorem mem_quatDouble_iff_halves {x : CDAlg ℝ 4} :
    x ∈ quatDouble p q ↔
      cdLo x ∈ Submodule.span ℝ (gen4 p q) ∧ cdHi x ∈ Submodule.span ℝ (gen4 p q) :=
  Iff.rfl

/-- `1 ∈ ℍ`. -/
theorem one_mem_span_gen4 : (1 : CDAlg ℝ 3) ∈ Submodule.span ℝ (gen4 p q) :=
  Submodule.subset_span (Set.mem_insert _ _)

/-- `ℍ` is closed under conjugation (`x̄ = (2 Re x)·1 − x`, and `1 ∈ ℍ`). -/
theorem conj_mem_span_gen4 {z : CDAlg ℝ 3} (hz : z ∈ Submodule.span ℝ (gen4 p q)) :
    conj z ∈ Submodule.span ℝ (gen4 p q) := by
  rw [CDAut.conj_eq_two_re_sub]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (one_mem_span_gen4 p q)) hz

/-- **The double really is `ℍ ⊕ ℍ·ℓ`.**  Membership is equivalent to being of the
    form `a + b·ℓ` with `a, b ∈ ℍ` (`loOf` is the embedding of the low half,
    `loOf b * ell = hiOf b` by `loOf_mul_ell`). -/
theorem mem_quatDouble_iff {x : CDAlg ℝ 4} :
    x ∈ quatDouble p q ↔
      ∃ a b : CDAlg ℝ 3, a ∈ Submodule.span ℝ (gen4 p q) ∧
        b ∈ Submodule.span ℝ (gen4 p q) ∧ x = loOf a + loOf b * ell := by
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨cdLo x, cdHi x, hlo, hhi, ?_⟩
    rw [loOf_mul_ell]
    exact split_lo_hi x
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [loOf_mul_ell]
    refine ⟨?_, ?_⟩
    · rw [cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]; exact ha
    · rw [cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]; exact hb

/-- `1 ∈ ℍ ⊕ ℍℓ`. -/
theorem one_mem_quatDouble : (1 : CDAlg ℝ 4) ∈ quatDouble p q := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_one]; exact one_mem_span_gen4 p q
  · rw [cdHi_one]; exact Submodule.zero_mem _

/-- `ℓ ∈ ℍ ⊕ ℍℓ`. -/
theorem ell_mem_quatDouble : ell ∈ quatDouble p q := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_ell]; exact Submodule.zero_mem _
  · rw [cdHi_ell]; exact one_mem_span_gen4 p q

theorem zero_mem_quatDouble : (0 : CDAlg ℝ 4) ∈ quatDouble p q := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_zero]; exact Submodule.zero_mem _
  · rw [cdHi_zero]; exact Submodule.zero_mem _

theorem add_mem_quatDouble {x y : CDAlg ℝ 4}
    (hx : x ∈ quatDouble p q) (hy : y ∈ quatDouble p q) : x + y ∈ quatDouble p q := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_add]; exact Submodule.add_mem _ hx.1 hy.1
  · rw [cdHi_add]; exact Submodule.add_mem _ hx.2 hy.2

theorem smul_mem_quatDouble (r : ℝ) {x : CDAlg ℝ 4} (hx : x ∈ quatDouble p q) :
    r • x ∈ quatDouble p q := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_smul]; exact Submodule.smul_mem _ _ hx.1
  · rw [cdHi_smul]; exact Submodule.smul_mem _ _ hx.2

/-- **Multiplicative closure — the substantive half.**  Holds for ARBITRARY
    `p, q` (no unit / imaginary / orthogonality hypothesis), and the mechanism is
    worth stating precisely because the obvious reading of it is wrong:

    * **Artin's theorem does NOT apply in 𝕊.**  𝕊 = `CDAlg ℝ 4` is not alternative
      (`CDLifting.sedenion_not_alternative`), so "any two elements generate an
      associative subalgebra" is FALSE at level 4 and cannot be what closes this.
    * **What the proof actually uses.**  Two steps, both of them:
      (i) the Cayley–Dickson doubling formula in 𝕊 — `cdLo_mul` / `cdHi_mul`,
      `(a,b)(c,d) = (ac − d̄b, da + bc̄)` — which reduces the single 𝕊-product to
      four 𝕆-products; and
      (ii) closure of the 𝕆-level submodule `ℍ = span (gen4 p q)` under the
      OCTONION product (`ArtinSpan.span4_mul_closed`, which is where Artin's
      theorem is genuinely available, 𝕆 being alternative) together with its
      closure under conjugation (`conj_mem_span_gen4`, needed for the `d̄` and `c̄`
      slots).
    So the double `S ⊕ S·ℓ` of a conjugation-closed, multiplicatively closed
    `S ⊂ 𝕆` is closed in 𝕊 by the CD formula — a level-3 fact transported by a
    level-4 identity, never an alternativity claim about 𝕊.
    (Red Team item 8, PR #663.) -/
theorem mul_mem_quatDouble {x y : CDAlg ℝ 4}
    (hx : x ∈ quatDouble p q) (hy : y ∈ quatDouble p q) : x * y ∈ quatDouble p q := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_mul]
    exact Submodule.sub_mem _ (span4_mul_closed p q hx.1 hy.1)
      (span4_mul_closed p q (conj_mem_span_gen4 p q hy.2) hx.2)
  · rw [cdHi_mul]
    exact Submodule.add_mem _ (span4_mul_closed p q hy.2 hx.1)
      (span4_mul_closed p q hx.2 (conj_mem_span_gen4 p q hy.1))

/-- The double is a `*`-subalgebra: closed under sedenion conjugation too. -/
theorem conj_mem_quatDouble {x : CDAlg ℝ 4} (hx : x ∈ quatDouble p q) :
    conj x ∈ quatDouble p q := by
  have h : conj x = (2 * x.coord 0) • (1 : CDAlg ℝ 4) + (-1 : ℝ) • x := by
    rw [CDAut.conj_eq_two_re_sub]; module
  rw [h]
  exact add_mem_quatDouble p q
    (smul_mem_quatDouble p q _ (one_mem_quatDouble p q))
    (smul_mem_quatDouble p q _ hx)

/-- **ρ-invariance (membership form).**  `ρ` acts on the pair split by a plane
    rotation with **real** coefficients plus a real multiple of `1` in each half
    (`rotLo_def` / `rotHi_def`), so it maps `ℍ ⊕ ℍℓ` into itself for any
    submodule `ℍ` containing `1`. -/
theorem rotAut3_mem_quatDouble {x : CDAlg ℝ 4} (hx : x ∈ quatDouble p q) :
    rotAut3 x ∈ quatDouble p q := by
  have hone := one_mem_span_gen4 p q
  refine ⟨?_, ?_⟩
  · show cdLo (rotMap3 x) ∈ _
    rw [cdLo_rotMap3, rotLo_def]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ hx.1) (Submodule.smul_mem _ _ hx.2))
      (Submodule.smul_mem _ _ hone)
  · show cdHi (rotMap3 x) ∈ _
    rw [cdHi_rotMap3, rotHi_def]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ hx.1) (Submodule.smul_mem _ _ hx.2))
      (Submodule.smul_mem _ _ hone)

/-- **`rho_invariant_octonion_doubles` — ρ-invariance as an equality of SETS.**
    For every `p q : 𝕆`, `ρ(ℍ ⊕ ℍℓ) = ℍ ⊕ ℍℓ`.  (`⊆` is
    `rotAut3_mem_quatDouble`; `⊇` uses `ρ³ = id`.)  Contrast
    `CrystalHosting.rho_moves_cd_half`: the CD half `𝕆_low` itself is **not**
    ρ-invariant, because it is not of the form `ℍ ⊕ ℍℓ`. -/
theorem rotAut3_image_quatDouble :
    rotAut3.toFun '' quatDouble p q = quatDouble p q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact rotAut3_mem_quatDouble p q hx
  · intro hy
    exact ⟨rotAut3 (rotAut3 y),
      rotAut3_mem_quatDouble p q (rotAut3_mem_quatDouble p q hy), rotAut3_pow_three y⟩

/-- **The double is a PROPER subset of 𝕊**, so the closure statements above are
    not vacuous.  For an orthonormal imaginary pair `p q`, `ℍ` is 4-dimensional
    (`finrank_quaternion_frame`) hence a proper submodule of the 8-dimensional
    `𝕆`, and any `z ∉ ℍ` gives `loOf z ∉ ℍ ⊕ ℍℓ`. -/
theorem quatDouble_proper
    (hp0 : p.coord 0 = 0) (hq0 : q.coord 0 = 0) (hpq : bil p q = 0)
    (hNp : N p = 1) (hNq : N q = 1) :
    ∃ z : CDAlg ℝ 4, z ∉ quatDouble p q := by
  have hne : Submodule.span ℝ (gen4 p q) ≠ ⊤ := by
    intro htop
    have h4 : Module.finrank ℝ (Submodule.span ℝ (gen4 p q)) = 4 :=
      finrank_quaternion_frame hp0 hq0 hpq hNp hNq
    rw [htop, finrank_top, QBP.Foundations.CDDimension.finrank_cdAlg] at h4
    norm_num at h4
  obtain ⟨z, hz⟩ : ∃ z : CDAlg ℝ 3, z ∉ Submodule.span ℝ (gen4 p q) := by
    by_contra hcon
    push Not at hcon
    exact hne (Submodule.eq_top_iff'.mpr hcon)
  refine ⟨loOf z, ?_⟩
  intro hmem
  exact hz (by simpa using hmem.1)

end RhoInvariantDoubles

/-! ## 9. The encoding family (#A) and the left-module structure of `ℍ^⊥` (#B)

Confirmer pass 2.  §8 above showed every `quatDouble p q = ℍ ⊕ ℍ·ℓ` is a
ρ-invariant, multiplicatively closed subalgebra of 𝕊.  This section identifies
**which** of them contain a given crystal's hosted algebra `ℍ_u`, and proves the
module fact that any completeness argument has to rest on.

**(A) The encoding family.**  Fix a unit imaginary `u : 𝕆`.  For a unit imaginary
`w ⟂ u`, `quatDouble u w` contains `ℍ_u = span{1, ℓ, U, ℓU}`
(`quatSpan_subset_quatDouble`), is closed under the sedenion product and is
ρ-invariant (§8).  Left multiplication `L_u` restricts to `u^⊥ ∩ Im 𝕆` and
squares to `−Id` there (`leftMul_sq_eq_neg`, `perp_stable_under_leftMul`), so
`(u^⊥ ∩ Im 𝕆, L_u)` is a complex vector space; and `w` and `u·w` give the SAME
member of the family (`quatDouble_eq_of_mul_u`).  So the family is parametrised
by the `L_u`-complex lines of `u^⊥`, exactly as the confirmer's pass 2 says.

**Not claimed (out of toolchain, per the dispatch):** that the parametrisation is
a bijection onto the ℂP² of complex lines, that `G₂`/`SU(3)` acts transitively on
it, or any dimension count for the family.

**(B) `ℍ^⊥` as a left `ℍ`-module.**  The composition-algebra adjoint identity
`⟨a·c, d⟩ = ⟨c, ā·d⟩` (`bil_mul_left_adjoint`, derived from the *polarised* norm
composition `octonion_normMap_zero` already in `OctonionLaws`) gives at once that
the orthogonal complement of a quaternion span in 𝕆 is stable under left and
right multiplication by the span (`perp_span4_left_module`,
`perp_span4_right_module`), and `mul_right_ne_zero_of_ne_zero` gives that
`h ↦ h·z` is injective on it.  These are the three inputs the "every 8-dimensional
multiplicatively closed extension is `ℍ ⊕ ℍ·w`" argument needs. -/

section EncodingFamily

open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

variable {u w : CDAlg ℝ 3}

/-- **(A)(i) — `L_u² = −Id`.**  Left multiplication by a unit imaginary octonion
    squares to minus the identity (left alternativity plus `u² = −1`); on
    `u^⊥ ∩ Im 𝕆` this is a complex structure. -/
theorem leftMul_sq_eq_neg (hu0 : u.coord 0 = 0) (hNu : N u = 1) (z : CDAlg ℝ 3) :
    u * (u * z) = -z := by
  rw [u_mul_uv hu0 hNu]; module

/-- **(A)(i, second half) — `L_u` preserves `u^⊥ ∩ Im 𝕆`.**  If `w` is a unit
    imaginary orthogonal to `u`, so is `u·w`. -/
theorem perp_stable_under_leftMul (hu0 : u.coord 0 = 0) (hw0 : w.coord 0 = 0)
    (huw : bil u w = 0) (hNu : N u = 1) (hNw : N w = 1) :
    (u * w).coord 0 = 0 ∧ N (u * w) = 1 ∧ bil u (u * w) = 0 :=
  ⟨mul_coord_zero hw0 huw, N_mul_unit hNu hNw, bil_u_uv hu0 hw0 huw hNu⟩

/-- **(A)(ii) — every member of the family contains the hosted algebra.**  For any
    `w`, the quaternion span `ℍ_u = span{1, ℓ, U, ℓU} ⊂ 𝕊` sits inside
    `quatDouble u w`.  (Only `u.coord 0 = 0` is needed; orthonormality of `w` is
    what makes the double 8-dimensional, which is not claimed here.) -/
theorem quatSpan_subset_quatDouble (hu0 : u.coord 0 = 0) (w : CDAlg ℝ 3) :
    {x : CDAlg ℝ 4 | InQuatSpan (loOf u) x} ⊆ quatDouble u w := by
  rintro x ⟨a, b, c, d, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [cdLo_quatComb a b c d hu0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (one_mem_span_gen4 u w))
      (Submodule.smul_mem _ _ (x_mem_span_gen4 u w))
  · rw [cdHi_quatComb a b c d hu0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (one_mem_span_gen4 u w))
      (Submodule.smul_mem _ _ (x_mem_span_gen4 u w))

/-- **(A)(ii), packaged.**  `𝕆'_w := quatDouble u w` contains the hosted algebra,
    is closed under the sedenion product, and is ρ-invariant as a set.

    **`w` is ARBITRARY here** — no unit/imaginary/orthogonality hypothesis is used
    or needed for these three clauses, so degenerate `w` (e.g. `w = 0`, where the
    "double" collapses to the 4-dimensional quaternion span) are included.  What
    orthonormality of `w` buys is 8-dimensionality of the double — the property
    that makes the `w`-indexed collection a *family of octonion copies* — and that
    is NOT claimed by this theorem.  (Red Team F11, PR #663: an earlier docstring
    said "for a unit imaginary `w ⟂ u`", which the statement does not require.) -/
theorem encoding_family_member (hu0 : u.coord 0 = 0) (w : CDAlg ℝ 3) :
    {x : CDAlg ℝ 4 | InQuatSpan (loOf u) x} ⊆ quatDouble u w ∧
      (∀ x ∈ quatDouble u w, ∀ y ∈ quatDouble u w, x * y ∈ quatDouble u w) ∧
      rotAut3.toFun '' quatDouble u w = quatDouble u w :=
  ⟨quatSpan_subset_quatDouble hu0 w,
   fun _ hx _ hy => mul_mem_quatDouble u w hx hy,
   rotAut3_image_quatDouble u w⟩

/-- `span{1, u, u·w, u·(u·w)} = span{1, u, w, u·w}`: the two generating frames of
    the same quaternion subalgebra. -/
theorem span_gen4_u_mul (hu0 : u.coord 0 = 0) (hNu : N u = 1) (w : CDAlg ℝ 3) :
    Submodule.span ℝ (gen4 u (u * w)) = Submodule.span ℝ (gen4 u w) := by
  have hneg : u * (u * w) = -w := leftMul_sq_eq_neg hu0 hNu w
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · intro z hz
    simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h | h
    · rw [h]; exact one_mem_span_gen4 u w
    · rw [h]; exact x_mem_span_gen4 u w
    · rw [h]; exact xy_mem_span_gen4 u w
    · rw [h, hneg, show -w = (-1 : ℝ) • w by module]
      exact Submodule.smul_mem _ _ (y_mem_span_gen4 u w)
  · intro z hz
    simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h | h
    · rw [h]; exact one_mem_span_gen4 u (u * w)
    · rw [h]; exact x_mem_span_gen4 u (u * w)
    · rw [h]
      have hsm : (-1 : ℝ) • (u * (u * w)) ∈ Submodule.span ℝ (gen4 u (u * w)) :=
        Submodule.smul_mem _ (-1) (xy_mem_span_gen4 u (u * w))
      have heq : (-1 : ℝ) • (u * (u * w)) = w := by rw [hneg]; module
      rwa [heq] at hsm
    · rw [h]; exact y_mem_span_gen4 u (u * w)

/-- **(A)(iii) — `w` and `u·w` give the SAME member of the family.**  So the
    family is indexed by the `L_u`-complex LINES of `u^⊥`, not by its unit
    vectors. -/
theorem quatDouble_eq_of_mul_u (hu0 : u.coord 0 = 0) (hNu : N u = 1)
    (w : CDAlg ℝ 3) : quatDouble u (u * w) = quatDouble u w := by
  rw [quatDouble, quatDouble, span_gen4_u_mul hu0 hNu w]

end EncodingFamily

section PerpModule

open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

/-- **The composition-algebra adjoint identity at 𝕆:** `⟨a·c, d⟩ = ⟨c, ā·d⟩`.
    Derived from the *polarised* norm-composition identity `octonion_normMap_zero`
    (already proved in `OctonionLaws` by the quadrilinear lift) by setting the
    second argument to `1`.  This is the statement that `L_a` and `L_{ā}` are
    mutually adjoint for the norm form. -/
theorem bil_mul_left_adjoint (a c d : CDAlg ℝ 3) :
    bil (a * c) d = bil c (conj a * d) := by
  have h : bil (a * c) ((1 : CDAlg ℝ 3) * d) + bil ((1 : CDAlg ℝ 3) * c) (a * d)
      - 2 * bil a (1 : CDAlg ℝ 3) * bil c d = 0 := by
    rw [← normMap_coord0 a 1 c d, octonion_normMap_zero]
    rfl
  rw [cd_one_mul, cd_one_mul, bil_one_right] at h
  rw [CDAut.conj_eq_two_re_sub a, cd_sub_mul, mul_smul_left, cd_one_mul,
    QBP.Foundations.CrossProduct.bil_sub_right, bil_smul_right]
  linarith

/-- The mirror adjoint identity: `⟨c·a, d⟩ = ⟨c, d·ā⟩`. -/
theorem bil_mul_right_adjoint (a c d : CDAlg ℝ 3) :
    bil (c * a) d = bil c (d * conj a) := by
  have h : bil (c * a) (d * (1 : CDAlg ℝ 3)) + bil (d * a) (c * (1 : CDAlg ℝ 3))
      - 2 * bil c d * bil a (1 : CDAlg ℝ 3) = 0 := by
    rw [← normMap_coord0 c d a 1, octonion_normMap_zero]
    rfl
  rw [cd_mul_one, cd_mul_one, bil_one_right] at h
  rw [CDAut.conj_eq_two_re_sub a, cd_mul_sub, mul_smul_right, cd_mul_one,
    QBP.Foundations.CrossProduct.bil_sub_right, bil_smul_right,
    QBP.Foundations.NormForm.bil_symm c (d * a)]
  linarith

/-- **(B) — `ℍ^⊥` is a LEFT `ℍ`-module.**  If `z` is orthogonal to the quaternion
    span `ℍ = span ℝ {1, p, q, pq}` then so is `a·z` for every `a ∈ ℍ`.  (Proof:
    `⟨k, a·z⟩ = ⟨a·z, k⟩ = ⟨z, ā·k⟩` and `ā·k ∈ ℍ` because `ℍ` is closed under
    conjugation and multiplication.) -/
theorem perp_span4_left_module (p q : CDAlg ℝ 3) {z : CDAlg ℝ 3}
    (hz : ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k z = 0)
    {a : CDAlg ℝ 3} (ha : a ∈ Submodule.span ℝ (gen4 p q)) :
    ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k (a * z) = 0 := by
  intro k hk
  have hadj : bil (a * z) k = bil z (conj a * k) := bil_mul_left_adjoint a z k
  have hmem : conj a * k ∈ Submodule.span ℝ (gen4 p q) :=
    span4_mul_closed p q (conj_mem_span_gen4 p q ha) hk
  rw [QBP.Foundations.NormForm.bil_symm k (a * z), hadj,
    QBP.Foundations.NormForm.bil_symm z (conj a * k)]
  exact hz _ hmem

/-- **(B, mirror) — `ℍ^⊥` is a RIGHT `ℍ`-module.** -/
theorem perp_span4_right_module (p q : CDAlg ℝ 3) {z : CDAlg ℝ 3}
    (hz : ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k z = 0)
    {a : CDAlg ℝ 3} (ha : a ∈ Submodule.span ℝ (gen4 p q)) :
    ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k (z * a) = 0 := by
  intro k hk
  have hadj : bil (z * a) k = bil z (k * conj a) := bil_mul_right_adjoint a z k
  have hmem : k * conj a ∈ Submodule.span ℝ (gen4 p q) :=
    span4_mul_closed p q hk (conj_mem_span_gen4 p q ha)
  rw [QBP.Foundations.NormForm.bil_symm k (z * a), hadj,
    QBP.Foundations.NormForm.bil_symm z (k * conj a)]
  exact hz _ hmem

/-- **`h ↦ h·z` is injective for `z ≠ 0`** — 𝕆 has no zero divisors (norm
    composition).  Together with the module statement this is what forces
    `dim (ℍ·z) = 4` in any completeness argument. -/
theorem mul_right_eq_zero_iff {z : CDAlg ℝ 3} (hz : z ≠ 0) (h : CDAlg ℝ 3) :
    h * z = 0 ↔ h = 0 := by
  constructor
  · intro h0
    have hN : N h * N z = 0 := by rw [← octonion_norm_composition, h0, N_zero]
    have hNz : N z ≠ 0 := fun hc => hz ((alt_N_eq_zero_iff z).mp hc)
    exact (alt_N_eq_zero_iff h).mp ((mul_eq_zero.mp hN).resolve_right hNz)
  · intro h0; rw [h0]; exact alt_zero_mul z

end PerpModule

/-! ### (B) completeness: a quaternion span has no proper multiplicative extension

The three facts above (`perp_span4_left_module`, `bil_mul_left_adjoint`,
`mul_right_eq_zero_iff`) close the octonion-level form of the confirmer's
completeness route: inside 𝕆 a quaternion subalgebra `ℍ` is **maximal among
multiplicatively closed submodules** — any such `O ⊋ ℍ` already contains
`ℍ ⊕ ℍ·z` for any `z ∈ O ∩ ℍ^⊥`, which is all of 𝕆 by dimension.

**What this does NOT do.**  It is the statement inside 𝕆, not inside 𝕊.  The 𝕊
form ("every 8-dimensional multiplicatively closed `O ⊆ 𝕊` containing `ℍ_s` is a
`quatDouble u w`") does **not** follow, because 𝕊 is not a composition algebra:
`N(xy) = N x·N y` fails at level 4, so `bil_mul_left_adjoint` — the engine of the
module argument — is unavailable there and would have to be re-proved from the
level-4 structure constants.  That remains open. -/

section Completeness

open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

variable {p q : CDAlg ℝ 3}

theorem bil_zero_left (y : CDAlg ℝ 3) : bil (0 : CDAlg ℝ 3) y = 0 := by
  show (∑ i, (0 : CDAlg ℝ 3).coord i * y.coord i) = 0
  simp

/-- Orthogonality to the four frame generators propagates to the whole span. -/
theorem orth_span4_of_orth_gen (p q r : CDAlg ℝ 3)
    (h1 : bil (1 : CDAlg ℝ 3) r = 0) (hp : bil p r = 0) (hq : bil q r = 0)
    (hpq : bil (p * q) r = 0) :
    ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k r = 0 := by
  intro k hk
  induction hk using Submodule.span_induction with
  | mem x hx =>
      simp only [gen4, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h <;> rw [h]
      · exact h1
      · exact hp
      · exact hq
      · exact hpq
  | zero => exact bil_zero_left r
  | add x y _ _ hx hy => rw [bil_add_left, hx, hy]; ring
  | smul a x _ hx => rw [bil_smul_left, hx]; ring

/-- Right multiplication by a fixed octonion, as an ℝ-linear map. -/
def rMul (z : CDAlg ℝ 3) : CDAlg ℝ 3 →ₗ[ℝ] CDAlg ℝ 3 where
  toFun h := h * z
  map_add' a b := mul_add_left a b z
  map_smul' r a := mul_smul_left r a z

@[simp] theorem rMul_apply (z h : CDAlg ℝ 3) : rMul z h = h * z := rfl

theorem rMul_injective {z : CDAlg ℝ 3} (hz : z ≠ 0) : Function.Injective (rMul z) := by
  intro a b hab
  have hab' : a * z = b * z := hab
  have h : (a - b) * z = 0 := by rw [cd_sub_mul, hab', sub_self]
  exact sub_eq_zero.mp ((mul_right_eq_zero_iff hz (a - b)).mp h)

/-- **`ℍ ⊕ ℍ·z = 𝕆`** for any nonzero `z ⟂ ℍ`: the quaternion span and its image
    under right multiplication by `z` are complementary and fill 𝕆. -/
theorem span4_sup_rMul_eq_top
    (hp0 : p.coord 0 = 0) (hq0 : q.coord 0 = 0) (hpq : bil p q = 0)
    (hNp : N p = 1) (hNq : N q = 1)
    {z : CDAlg ℝ 3} (hz0 : z ≠ 0)
    (hz : ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k z = 0) :
    Submodule.span ℝ (gen4 p q) ⊔ Submodule.map (rMul z) (Submodule.span ℝ (gen4 p q))
      = ⊤ := by
  haveI : FiniteDimensional ℝ (CDAlg ℝ 3) :=
    Module.Finite.of_basis (QBP.Foundations.CDDimension.cdBasis 3)
  have hinj := rMul_injective hz0
  have hHrank : Module.finrank ℝ (Submodule.span ℝ (gen4 p q)) = 4 :=
    finrank_quaternion_frame hp0 hq0 hpq hNp hNq
  have hKrank :
      Module.finrank ℝ (Submodule.map (rMul z) (Submodule.span ℝ (gen4 p q))) = 4 := by
    rw [← LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective (rMul z) hinj (Submodule.span ℝ (gen4 p q)))]
    exact hHrank
  have hinf :
      Submodule.span ℝ (gen4 p q) ⊓ Submodule.map (rMul z) (Submodule.span ℝ (gen4 p q))
        = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨hxH, a, ha, hax⟩ := hx
    have hx' : bil x x = 0 := by
      have h2 := perp_span4_left_module p q hz ha x hxH
      have hxz : x = a * z := hax.symm
      rw [hxz] at h2 ⊢
      exact h2
    rw [Submodule.mem_bot]
    exact (alt_N_eq_zero_iff x).mp (by rw [N_eq_bil]; exact hx')
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ (gen4 p q)) (Submodule.map (rMul z) (Submodule.span ℝ (gen4 p q)))
  rw [hinf, finrank_bot, hHrank, hKrank] at hsum
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [QBP.Foundations.CDDimension.finrank_cdAlg]
  omega

/-- **Maximality of a quaternion subalgebra of 𝕆.**  If `O` is a submodule of 𝕆
    containing `ℍ = span ℝ {1,p,q,pq}` (`p q` orthonormal imaginary) and closed
    under multiplication, then `O = ℍ` or `O = 𝕆`.  There is nothing in between —
    in particular no 8-dimensional proper extension, which is the octonion-level
    form of `encoding_octonion_completeness`. -/
theorem span4_maximal
    (hp0 : p.coord 0 = 0) (hq0 : q.coord 0 = 0) (hpq : bil p q = 0)
    (hNp : N p = 1) (hNq : N q = 1)
    (O : Submodule ℝ (CDAlg ℝ 3))
    (hsub : Submodule.span ℝ (gen4 p q) ≤ O)
    (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) :
    O = Submodule.span ℝ (gen4 p q) ∨ O = ⊤ := by
  by_cases hle : O ≤ Submodule.span ℝ (gen4 p q)
  · exact Or.inl (le_antisymm hle hsub)
  · right
    obtain ⟨y, hyO, hyH⟩ := SetLike.not_le_iff_exists.mp hle
    set r : CDAlg ℝ 3 := y - proj4 p q y with hr
    have hrO : r ∈ O := Submodule.sub_mem O hyO (hsub (proj4_mem p q y))
    have hr0 : r ≠ 0 := by
      intro h0
      refine hyH ?_
      have : y = proj4 p q y := by rw [← sub_eq_zero]; exact h0
      rw [this]
      exact proj4_mem p q y
    have hrperp : ∀ k ∈ Submodule.span ℝ (gen4 p q), bil k r = 0 := by
      refine orth_span4_of_orth_gen p q r ?_ ?_ ?_ ?_
      · rw [QBP.Foundations.NormForm.bil_symm]
        exact residual_orth_one hp0 hq0 hpq y
      · rw [QBP.Foundations.NormForm.bil_symm]
        exact residual_orth_u hp0 hq0 hpq hNp y
      · rw [QBP.Foundations.NormForm.bil_symm]
        exact residual_orth_v hp0 hq0 hpq hNq y
      · rw [QBP.Foundations.NormForm.bil_symm]
        exact residual_orth_uv hp0 hq0 hpq hNp hNq y
    have htop := span4_sup_rMul_eq_top hp0 hq0 hpq hNp hNq hr0 hrperp
    refine eq_top_iff.mpr ?_
    rw [← htop]
    refine sup_le hsub ?_
    rintro x ⟨a, ha, rfl⟩
    exact hmul a (hsub ha) r hrO

end Completeness

/-! ## 10. (C) transitivity on the encoding family — the reduction

The confirmer's pass-3 construction (`pass3_transitivity.py`, 20/20 to 8e-15)
builds, for two unit imaginary `w₁, w₂ ⟂ u`, an automorphism `Ψ` of 𝕊 that fixes
the crystal and carries `𝕆'_{w₁}` onto `𝕆'_{w₂}`.  Its two halves are:

1. an automorphism `ψ` of 𝕆 with `ψ u = u` and `ψ w₁ = w₂` (in the script: the
   composite of two frame maps `(e₁,e₂,e₄) ↦ (u,wᵢ,rᵢ)`), and
2. the diagonal lift `Ψ = cdLift ψ` to 𝕊.

**Step 2 is proved here in full** (`encoding_family_transitive_of_aut`): given any
such `ψ`, the lift is an automorphism of 𝕊 (that is `CrystalHosting.cdLift`), it
fixes `ℓ`, it fixes EVERY crystal with direction `u`, and it carries
`quatDouble u w₁` onto `quatDouble u w₂` as sets.

**Step 1 is NOT proved and is the whole residue.**  The existence of `ψ` is
transitivity on orthonormal frames of 𝕆 — the script's `frame_auto`, i.e. the
claim that an arbitrary orthonormal imaginary triple is the image of
`(e₁, e₂, e₄)` under an automorphism.  The repository has only the SEVEN
signed-basis witnesses (`G2Transitivity.g2_transitive_genuine_automorphisms`),
which are discrete; the continuous statement is not in the toolchain.  So (C) is
reduced to one named octonion-level input and no further.  No group is named or
used in any statement below. -/

section Transitivity

open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

/-- A `CDAut` read as an ℝ-linear map (so `Submodule.map` applies to it). -/
def autLin {n : ℕ} (φ : CDAut n) : CDAlg ℝ n →ₗ[ℝ] CDAlg ℝ n where
  toFun := φ.toFun
  map_add' := φ.map_add
  map_smul' := φ.map_smul

@[simp] theorem autLin_apply {n : ℕ} (φ : CDAut n) (x : CDAlg ℝ n) :
    autLin φ x = φ x := rfl

/-- An automorphism carries a quaternion frame span to the frame span of the
    images. -/
theorem map_span_gen4 (ψ : CDAut 3) (a b : CDAlg ℝ 3) :
    Submodule.map (autLin ψ) (Submodule.span ℝ (gen4 a b))
      = Submodule.span ℝ (gen4 (ψ a) (ψ b)) := by
  rw [Submodule.map_span]
  congr 1
  simp only [gen4, Set.image_insert_eq, Set.image_singleton, autLin_apply,
    CDAut.map_one ψ, ψ.map_mul]

/-- **(C) — the reduction.**  Given an automorphism `ψ` of 𝕆 fixing `u` and
    carrying `w₁` to `w₂`, its diagonal lift `Ψ = cdLift ψ` is an automorphism of
    𝕊 that (a) fixes `ℓ`, (b) fixes EVERY crystal with direction `u`, and
    (c) carries `quatDouble u w₁` onto `quatDouble u w₂`. -/
theorem encoding_family_transitive_of_aut {u w₁ w₂ : CDAlg ℝ 3}
    (ψ : CDAut 3) (hu : ψ u = u) (hw : ψ w₁ = w₂) :
    cdLift ψ ell = ell
    ∧ (∀ (s : CDAlg ℝ 4) (α γ b₀ : ℝ), cdLo s = α • u →
        cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u → cdLift ψ s = s)
    ∧ (cdLift ψ).toFun '' quatDouble u w₁ = quatDouble u w₂ := by
  have hmap : Submodule.map (autLin ψ) (Submodule.span ℝ (gen4 u w₁))
      = Submodule.span ℝ (gen4 u w₂) := by
    rw [map_span_gen4 ψ u w₁, hu, hw]
  refine ⟨cdLift_ell ψ, ?_, ?_⟩
  · intro s α γ b₀ hlo hhi
    refine eq_of_halves ?_ ?_
    · show cdLo (cdLiftFun ψ s) = cdLo s
      rw [cdLo_liftFun, hlo, ψ.map_smul, hu]
    · show cdHi (cdLiftFun ψ s) = cdHi s
      rw [cdHi_liftFun, hhi, ψ.map_add, ψ.map_smul, ψ.map_smul, hu, CDAut.map_one]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · show cdLo (cdLiftFun ψ x) ∈ _
        rw [cdLo_liftFun, ← hmap]
        exact Submodule.mem_map_of_mem hx.1
      · show cdHi (cdLiftFun ψ x) ∈ _
        rw [cdHi_liftFun, ← hmap]
        exact Submodule.mem_map_of_mem hx.2
    · intro hy
      have hylo : cdLo y ∈ Submodule.map (autLin ψ) (Submodule.span ℝ (gen4 u w₁)) := by
        rw [hmap]; exact hy.1
      have hyhi : cdHi y ∈ Submodule.map (autLin ψ) (Submodule.span ℝ (gen4 u w₁)) := by
        rw [hmap]; exact hy.2
      obtain ⟨a, ha, hae⟩ := hylo
      obtain ⟨b, hb, hbe⟩ := hyhi
      refine ⟨loOf a + hiOf b, ⟨?_, ?_⟩, ?_⟩
      · rw [cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]; exact ha
      · rw [cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]; exact hb
      · refine eq_of_halves ?_ ?_
        · show cdLo (cdLiftFun ψ (loOf a + hiOf b)) = cdLo y
          rw [cdLo_liftFun, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]
          exact hae
        · show cdHi (cdLiftFun ψ (loOf a + hiOf b)) = cdHi y
          rw [cdHi_liftFun, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]
          exact hbe

end Transitivity

/-! ## 11. (D) The numerals: `dim (u^⊥ ∩ Im 𝕆) = 6` and the transverse trace

`dim (u^⊥ ∩ Im 𝕆) = 6` closes (`finrank_perpIm_eq_six`).  With it, the transverse
component map `transComp α γ u` is ONTO a 6-dimensional space
(`transComp_surjOn_perpIm`, via `transComp_eigDir`), which is the honest content
of "the transverse form has rank 6": the form is `8(1−b₀²)` times the squared
norm of a component taking values in a 6-dimensional space, and it vanishes on
the flat family.

**Not proved, stated precisely:** `finrank (tangent space) = 14` and
`finrank (radical of the form) = 8`, hence "rank = 14 − 8 = 6" as a *finrank*
identity.  That needs the radical as a submodule of the tangent space and a
second rank–nullity computation, neither of which is formalised.

The **trace** is proved in the form that a trace actually has:
`hess_trace_transverse` sums the Hessian over an ORTHONORMAL 6-frame of the
transverse subspace and gets `48(1−b₀²)`, and `exists_orthonormal_perpIm_frame`
now EXHIBITS such a frame for every unit imaginary `u`, so
`hess_trace_transverse_exists` states the trace with no undischarged hypothesis
at all (Red Team F7, PR #663).  What is missing for the full
tangent-space trace is that those 6 vectors extend to an orthonormal basis of the
14-dimensional tangent space whose other 8 members lie in the flat family; the
flat family is known to be annihilated (`hessQuad_flatDir`) but the basis
extension is not formalised.

At the poles the form vanishes in EVERY direction (`hessQuad_pole_eq_zero`), which
is "rank 0" with nothing left to prove. -/

section Numerals

open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

variable {u : CDAlg ℝ 3}

/-- `z ↦ (Re z, ⟨u, z⟩)` as an ℝ-linear map. -/
def imPerpMap (u : CDAlg ℝ 3) : CDAlg ℝ 3 →ₗ[ℝ] ℝ × ℝ where
  toFun z := (z.coord 0, bil u z)
  map_add' a b := by
    simp only [Prod.mk_add_mk]
    rw [add_coord, bil_add_right]
  map_smul' r a := by
    simp only [RingHom.id_apply, Prod.smul_mk, smul_eq_mul]
    rw [smul_coord, bil_smul_right]

/-- `u^⊥ ∩ Im 𝕆` — the imaginary octonions orthogonal to `u`. -/
def perpIm (u : CDAlg ℝ 3) : Submodule ℝ (CDAlg ℝ 3) := LinearMap.ker (imPerpMap u)

theorem mem_perpIm {z : CDAlg ℝ 3} :
    z ∈ perpIm u ↔ z.coord 0 = 0 ∧ bil u z = 0 := by
  rw [perpIm, LinearMap.mem_ker]
  exact ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
    fun h => Prod.ext h.1 h.2⟩

theorem imPerpMap_surjective (hu0 : u.coord 0 = 0) (hNu : N u = 1) :
    Function.Surjective (imPerpMap u) := by
  rintro ⟨a, b⟩
  refine ⟨a • (1 : CDAlg ℝ 3) + b • u, ?_⟩
  have h1 : (a • (1 : CDAlg ℝ 3) + b • u).coord 0 = a := by
    rw [add_coord, smul_coord, smul_coord, one_coord, if_pos rfl, hu0, mul_one,
      mul_zero, add_zero]
  have h2 : bil u (a • (1 : CDAlg ℝ 3) + b • u) = b := by
    rw [bil_add_right, bil_smul_right, bil_smul_right, bil_one_right, hu0,
      ← N_eq_bil, hNu]
    ring
  show ((a • (1 : CDAlg ℝ 3) + b • u).coord 0, bil u (a • (1 : CDAlg ℝ 3) + b • u))
      = (a, b)
  rw [h1, h2]

/-- **(D) — `dim (u^⊥ ∩ Im 𝕆) = 6`** for a unit imaginary `u`: rank–nullity for
    the surjection `z ↦ (Re z, ⟨u,z⟩) : 𝕆 → ℝ²`. -/
theorem finrank_perpIm_eq_six (hu0 : u.coord 0 = 0) (hNu : N u = 1) :
    Module.finrank ℝ (perpIm u) = 6 := by
  haveI : FiniteDimensional ℝ (CDAlg ℝ 3) :=
    Module.Finite.of_basis (QBP.Foundations.CDDimension.cdBasis 3)
  have h := LinearMap.finrank_range_add_finrank_ker (imPerpMap u)
  rw [LinearMap.range_eq_top.mpr (imPerpMap_surjective hu0 hNu), finrank_top,
    QBP.Foundations.CDDimension.finrank_cdAlg] at h
  have h2 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [h2] at h
  rw [perpIm]
  omega

/-- **The transverse component map is ONTO `u^⊥ ∩ Im 𝕆`** — every 6-dimensional
    direction is realised by a tangent vector of the explicit transverse family.
    With `finrank_perpIm_eq_six` this is the honest content of "rank 6". -/
theorem transComp_surjOn_perpIm {α γ b₀ : ℝ} {s : CDAlg ℝ 4}
    (hu0 : u.coord 0 = 0) (hk : α ^ 2 + γ ^ 2 ≠ 0)
    (hlo : cdLo s = α • u) (hhi : cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u)
    {e : CDAlg ℝ 3} (he : e ∈ perpIm u) :
    ∃ v : CDAlg ℝ 4, v.coord 0 = 0 ∧ bil s v = 0 ∧ transComp α γ u v = e := by
  obtain ⟨he0, hue⟩ := mem_perpIm.mp he
  exact ⟨eigDir α γ e, eigDir_coord_zero he0 α γ,
    eigDir_orth_crystal (u := u) he0 hlo hhi,
    transComp_eigDir (u := u) hk he0 hue⟩

/-- The Hessian quadratic form is homogeneous of degree 2. -/
theorem hessQuad_smul (s v : CDAlg ℝ 4) (r : ℝ) :
    hessQuad s (r • v) = r ^ 2 * hessQuad s v := by
  have h : secVar s (r • v) = r • secVar s v := by
    rw [secVar, secVar, cdLo_smul, cdHi_smul]
    simp only [mul_smul_left, mul_smul_right]
    module
  rw [hessQuad, hessQuad, h, N_smul]
  ring

/-- The transverse family is conformal: `⟨v_e, v_f⟩ = (α²+γ²)·⟨e, f⟩`. -/
theorem bil_eigDir (α γ : ℝ) (e f : CDAlg ℝ 3) :
    bil (eigDir α γ e) (eigDir α γ f) = (α ^ 2 + γ ^ 2) * bil e f := by
  rw [bil_split]
  simp only [cdLo_eigDir, cdHi_eigDir, bil_smul_left, bil_smul_right]
  ring

/-! ### The orthonormal 6-frame EXISTS — `hess_trace_transverse` is not vacuous

`hess_trace_transverse` below takes an orthonormal 6-frame of `u^⊥ ∩ Im 𝕆` as a
hypothesis.  Red Team item F7 (PR #663) correctly objected that nothing in the
tree produced one, so "trace = 48(1 − b₀²)" rested on an undischarged premise.
`exists_orthonormal_perpIm_frame` discharges it.

The construction imports Mathlib's orthonormal-basis machinery through a
coordinate linear equivalence: `CDAlg ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2^n))`
carries `bil` to the Euclidean inner product (`bil_eq_inner`, both sides being
`∑ᵢ xᵢyᵢ`), so `perpIm u` — of dimension `6` by `finrank_perpIm_eq_six` — maps to
a 6-dimensional subspace of `ℝ⁸`, which has an orthonormal basis
(`stdOrthonormalBasis`).  Pulling that basis back gives the frame.  No
`InnerProductSpace` instance is put on `CDAlg` itself. -/

/-- The coordinate linear equivalence `CDAlg ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2^n))`.
    Used ONLY to borrow Mathlib's orthonormal-basis machinery for `bil`. -/
noncomputable def toEuclid (n : ℕ) : CDAlg ℝ n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2^n)) :=
  (QBP.Foundations.CDDimension.coordEquiv n).trans
    (WithLp.linearEquiv 2 ℝ (Fin (2^n) → ℝ)).symm

open scoped RealInnerProductSpace in
/-- `toEuclid` is an isometry of the bilinear form: `bil x y = ⟪x, y⟫` after
    transport.  Both sides are literally `∑ᵢ xᵢ yᵢ`. -/
theorem bil_eq_inner (n : ℕ) (x y : CDAlg ℝ n) :
    bil x y = ⟪toEuclid n x, toEuclid n y⟫ := by
  rw [PiLp.inner_apply]
  simp [toEuclid, bil, QBP.Foundations.CDDimension.coordEquiv, mul_comm]

open scoped RealInnerProductSpace in
/-- **(D) — an orthonormal 6-frame of `u^⊥ ∩ Im 𝕆` EXISTS** for every unit
    imaginary `u`: six imaginary octonions, each orthogonal to `u`, each of unit
    norm form, pairwise orthogonal.  This is exactly the hypothesis bundle of
    `hess_trace_transverse`, so that theorem is not vacuous (Red Team F7, #663). -/
theorem exists_orthonormal_perpIm_frame (hu0 : u.coord 0 = 0) (hNu : N u = 1) :
    ∃ e : Fin 6 → CDAlg ℝ 3,
      (∀ i, (e i).coord 0 = 0) ∧ (∀ i, bil u (e i) = 0) ∧
      (∀ i, N (e i) = 1) ∧ (∀ i j, i ≠ j → bil (e i) (e j) = 0) := by
  haveI : FiniteDimensional ℝ (CDAlg ℝ 3) :=
    Module.Finite.of_basis (QBP.Foundations.CDDimension.cdBasis 3)
  set f := toEuclid 3 with hf
  set S : Submodule ℝ (EuclideanSpace ℝ (Fin (2^3))) := (perpIm u).map f.toLinearMap with hS
  have hdim : Module.finrank ℝ S = 6 := by
    rw [hS, LinearEquiv.finrank_map_eq f (perpIm u)]
    exact finrank_perpIm_eq_six hu0 hNu
  let b : OrthonormalBasis (Fin 6) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (finCongr hdim)
  have hmem : ∀ i : Fin 6, f.symm ((b i : EuclideanSpace ℝ (Fin (2^3)))) ∈ perpIm u := by
    intro i
    obtain ⟨z, hz, hzeq⟩ := (b i).2
    have hzz : f.symm ((b i : EuclideanSpace ℝ (Fin (2^3)))) = z := by
      rw [← hzeq]; exact f.symm_apply_apply z
    rw [hzz]; exact hz
  refine ⟨fun i => f.symm ((b i : EuclideanSpace ℝ (Fin (2^3)))), ?_, ?_, ?_, ?_⟩
  · intro i; exact (mem_perpIm.mp (hmem i)).1
  · intro i; exact (mem_perpIm.mp (hmem i)).2
  · intro i
    have hON := b.orthonormal
    rw [orthonormal_iff_ite] at hON
    rw [N_eq_bil, bil_eq_inner, ← hf, f.apply_symm_apply, ← Submodule.coe_inner,
      hON i i, if_pos rfl]
  · intro i j hij
    have hON := b.orthonormal
    rw [orthonormal_iff_ite] at hON
    rw [bil_eq_inner, ← hf, f.apply_symm_apply, f.apply_symm_apply, ← Submodule.coe_inner,
      hON i j, if_neg hij]

/-- The trace normaliser `c` with `c²(α² + γ²) = 1` exists whenever `α² + γ² ≠ 0`
    (the non-pole condition).  Removes the last free parameter of the trace
    statement. -/
theorem exists_trace_normaliser {α γ : ℝ} (hk : α ^ 2 + γ ^ 2 ≠ 0) :
    ∃ c : ℝ, c ^ 2 * (α ^ 2 + γ ^ 2) = 1 := by
  have hpos : 0 < α ^ 2 + γ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hk)
  refine ⟨(Real.sqrt (α ^ 2 + γ ^ 2))⁻¹, ?_⟩
  rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- **(D) — the transverse trace is `48(1 − b₀²)`.**  For an ORTHONORMAL 6-frame
    `e₀,…,e₅` of `u^⊥ ∩ Im 𝕆` the rescaled transverse vectors `c·v_{eᵢ}` are
    orthonormal tangent vectors and the Hessian sums to `48(1 − b₀²)` on them. -/
theorem hess_trace_transverse {s : CDAlg ℝ 4} {α γ b₀ c : ℝ}
    (hu0 : u.coord 0 = 0) (hNu : N u = 1)
    (hlo : cdLo s = α • u) (hhi : cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u)
    (hNs : N s = 1) (hk : α ^ 2 + γ ^ 2 ≠ 0) (hc : c ^ 2 * (α ^ 2 + γ ^ 2) = 1)
    {e : Fin 6 → CDAlg ℝ 3} (he0 : ∀ i, (e i).coord 0 = 0)
    (hue : ∀ i, bil u (e i) = 0) (hNe : ∀ i, N (e i) = 1)
    (horth : ∀ i j, i ≠ j → bil (e i) (e j) = 0) :
    (∀ i, N (c • eigDir α γ (e i)) = 1) ∧
      (∀ i j, i ≠ j → bil (c • eigDir α γ (e i)) (c • eigDir α γ (e j)) = 0) ∧
      (∑ i : Fin 6, hessQuad s (c • eigDir α γ (e i))) = 48 * (1 - b₀ ^ 2) := by
  have hb : (1 : ℝ) - b₀ ^ 2 = α ^ 2 + γ ^ 2 := by
    have hnorm : α ^ 2 + γ ^ 2 + b₀ ^ 2 = 1 := by
      rw [← vacuum_norm_parametrised hu0 hNu hlo hhi, hNs]
    linarith
  have hNv : ∀ i, N (c • eigDir α γ (e i)) = 1 := by
    intro i
    rw [N_smul, N_eigDir, hNe i, mul_one]
    exact hc
  refine ⟨hNv, ?_, ?_⟩
  · intro i j hij
    rw [bil_smul_left, bil_smul_right, bil_eigDir, horth i j hij]
    ring
  · have hterm : ∀ i : Fin 6, hessQuad s (c • eigDir α γ (e i)) = 8 * (1 - b₀ ^ 2) := by
      intro i
      rw [hessQuad_smul, hessQuad_eigDir (u := u) (b₀ := b₀) hu0 hNu (he0 i) (hue i)
        hlo hhi hNs hk, N_eigDir, hNe i, mul_one, hb]
      linear_combination (8 * (α ^ 2 + γ ^ 2)) * hc
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

/-- **(D) — the transverse trace `48(1 − b₀²)`, with NO undischarged hypothesis.**
    For every non-pole crystal `s` parametrised by `(u, α, γ, b₀)` there EXIST a
    normaliser `c` and six directions `e₀,…,e₅` such that the rescaled transverse
    vectors `c·v_{eᵢ}` are orthonormal and the Hessian sums to `48(1 − b₀²)` on
    them.  Obtained from `hess_trace_transverse` by discharging its frame and
    normaliser hypotheses with `exists_orthonormal_perpIm_frame` and
    `exists_trace_normaliser` (Red Team F7, PR #663). -/
theorem hess_trace_transverse_exists {s : CDAlg ℝ 4} {α γ b₀ : ℝ}
    (hu0 : u.coord 0 = 0) (hNu : N u = 1)
    (hlo : cdLo s = α • u) (hhi : cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u)
    (hNs : N s = 1) (hk : α ^ 2 + γ ^ 2 ≠ 0) :
    ∃ (c : ℝ) (e : Fin 6 → CDAlg ℝ 3),
      (∀ i, (e i).coord 0 = 0) ∧ (∀ i, bil u (e i) = 0) ∧
      (∀ i, N (c • eigDir α γ (e i)) = 1) ∧
      (∀ i j, i ≠ j → bil (c • eigDir α γ (e i)) (c • eigDir α γ (e j)) = 0) ∧
      (∑ i : Fin 6, hessQuad s (c • eigDir α γ (e i))) = 48 * (1 - b₀ ^ 2) := by
  obtain ⟨c, hc⟩ := exists_trace_normaliser (α := α) (γ := γ) hk
  obtain ⟨e, he0, hue, hNe, horth⟩ := exists_orthonormal_perpIm_frame (u := u) hu0 hNu
  obtain ⟨h1, h2, h3⟩ :=
    hess_trace_transverse (u := u) hu0 hNu hlo hhi hNs hk hc he0 hue hNe horth
  exact ⟨c, e, he0, hue, h1, h2, h3⟩

end Numerals




/-! ## 7. Completeness audit — `#print axioms`

Every theorem must depend only on `{propext, Classical.choice, Quot.sound}`. -/

#print axioms e_ne_zero
#print axioms N_one_cd
#print axioms N_e
#print axioms mul_comm_neg
#print axioms lMul_comp_eq_iff_assoc_forall
#print axioms lMul_comp_eq_iff_assoc_mem
#print axioms lMul_comp_of_forall
#print axioms mul_coord_zero
#print axioms N_mul_unit
#print axioms sq_eq_neg_one
#print axioms u_mul_uv
#print axioms uv_mul_v
#print axioms uv_mul_u
#print axioms v_mul_uv
#print axioms uv_sq
#print axioms quaternion_frame_table
#print axioms quaternion_frame_subalgebra
#print axioms lMul_comp_on_quaternion_frame
#print axioms bil_one_left
#print axioms bil_u_uv
#print axioms bil_v_uv
#print axioms quaternion_frame_linearIndependent
#print axioms gen4_eq_range
#print axioms finrank_quaternion_frame
#print axioms quaternion_frame_codim_four
#print axioms quaternion_frame_codim_four'
#print axioms uwu_eq
#print axioms mul_assoc_flip
#print axioms assoc_orthogonal_triple
#print axioms assoc_orthogonal_triple_ne_zero
#print axioms proj4_mem
#print axioms bil_proj4
#print axioms residual_orth_one
#print axioms residual_orth_u
#print axioms residual_orth_v
#print axioms residual_orth_uv
#print axioms span4_eq_of_associative
#print axioms finrank_eq_four_of_associative
#print axioms not_associative_of_gt_span4
#print axioms assocCoeffZ_e1_e2_e4
#print axioms assoc_e1_e2_e4_ne_zero
#print axioms fano_triple_hypotheses
#print axioms assoc_e1_e2_e4_ne_zero_structural
#print axioms fano_pair_frame
#print axioms lMul_comp_fails_on_octonions
#print axioms mem_quatDouble_iff_halves
#print axioms one_mem_span_gen4
#print axioms conj_mem_span_gen4
#print axioms mem_quatDouble_iff
#print axioms one_mem_quatDouble
#print axioms ell_mem_quatDouble
#print axioms zero_mem_quatDouble
#print axioms add_mem_quatDouble
#print axioms smul_mem_quatDouble
#print axioms mul_mem_quatDouble
#print axioms conj_mem_quatDouble
#print axioms rotAut3_mem_quatDouble
#print axioms rotAut3_image_quatDouble
#print axioms quatDouble_proper
#print axioms leftMul_sq_eq_neg
#print axioms perp_stable_under_leftMul
#print axioms quatSpan_subset_quatDouble
#print axioms encoding_family_member
#print axioms span_gen4_u_mul
#print axioms quatDouble_eq_of_mul_u
#print axioms bil_mul_left_adjoint
#print axioms bil_mul_right_adjoint
#print axioms perp_span4_left_module
#print axioms perp_span4_right_module
#print axioms mul_right_eq_zero_iff
#print axioms bil_zero_left
#print axioms orth_span4_of_orth_gen
#print axioms rMul_injective
#print axioms span4_sup_rMul_eq_top
#print axioms span4_maximal
#print axioms map_span_gen4
#print axioms encoding_family_transitive_of_aut
#print axioms mem_perpIm
#print axioms imPerpMap_surjective
#print axioms finrank_perpIm_eq_six
#print axioms transComp_surjOn_perpIm
#print axioms hessQuad_smul
#print axioms bil_eigDir
#print axioms toEuclid
#print axioms bil_eq_inner
#print axioms exists_orthonormal_perpIm_frame
#print axioms exists_trace_normaliser
#print axioms hess_trace_transverse
#print axioms hess_trace_transverse_exists

end QBP.Foundations.HolographicSubalgebra
