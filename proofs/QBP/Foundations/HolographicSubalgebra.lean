/-
  QBP.Foundations.HolographicSubalgebra
  =====================================

  **The THEOREM parts of the CTH derived principle `DERIV-holographic`.**

  `DERIV-holographic` currently reads: *"Observers require associativity.  The
  largest associative subalgebra of 𝕆 is ℍ (dim 4).  The 4D gap is the
  holographic boundary."*  It carries constitutional flag 3 (#473 rounds 13–15)
  because it was supported only through Prop 16 via `ℓ`.  This file splits the
  principle into its provable and its non-provable parts and proves the provable
  ones, so that the flag can be re-scoped to exactly what remains a postulate.

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
    frame equals it.  Closing the general statement additionally requires
    producing an orthonormal imaginary pair *inside* an arbitrary ≥5-dimensional
    subalgebra (a Gram–Schmidt step, i.e. an inner-product structure on `CDAlg`
    that this corpus does not yet carry).  That gap is stated, not papered over.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`, zero
  `maxHeartbeats` bump.  `#print axioms` audit at the bottom for every theorem.

  Best practices: `~/Documents/inter/lean-proof-best-practices.md`.
-/
import QBP.Foundations.Artin
import QBP.Foundations.Alternator
import QBP.Foundations.CrossProduct
import QBP.Foundations.CDDimension
import QBP.Foundations.NormForm

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

end QBP.Foundations.HolographicSubalgebra
