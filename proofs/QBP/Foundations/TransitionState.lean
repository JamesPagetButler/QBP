/-
  QBP.Foundations.TransitionState
  ===============================

  #473 kill-attack 5 (Prop 13(b) probe, `CONJ-condensed-math-for-transition-state`).

  **What this file proves.**  A *quantitative under-determination* statement for the
  transition-state ("in-flight") regime, stated in pure linear algebra on `CDAlg ℝ 4`
  and therefore layer-clean (Foundations imports Mathlib only).

  Fix a state `s` on the imaginary unit sphere of 𝕊 (`bil s s = 1`, `s₀ = 0`) and a
  vector `g` (intended: the gradient `∇V(s)` of the landscape potential — see
  `QBP.Substrate.RuleFlow.gradV` and `RuleFlow.fderiv_potential_apply`, which says
  `fderiv ℝ V s v = ⟪∇V s, v⟫ = bil v (∇V s)`; that file is Substrate, so it is CITED
  here, never imported).  Then:

  * `Tangent s` — the directions that keep a curve on the state sphere and inside the
    imaginary part, to first order — has dimension **14** (`finrank_tangent`).
  * `VNeutral s g` — those tangential directions that additionally change the potential
    at **zero** first-order rate — has dimension **13** exactly, whenever `g` is itself
    tangential and nonzero (`finrank_vNeutral`), and **14** when `g = 0`
    (`vNeutral_eq_tangent_of_gradient_zero`).

  So: of the 14 directions a dynamical rule may point in at an in-flight state, the
  potential `V` constrains **at most one**.  Thirteen are invisible to `V` — and hence
  invisible to *every* functional of `V`'s level sets, sublevel filtration, vacuum
  locus, or any condensed/locale-theoretic object built from those (all of which are
  functions of `V`'s topology alone).  Adding any `VNeutral` field to a rule field
  leaves the state sphere, the imaginary part and the descent rate of `V` all
  unchanged (`add_vNeutral_preserves_data`) while changing the rule
  (`exists_vNeutral_ne_zero`).

  **What this file does NOT prove.**  Nothing about the flow, the measure, the
  crystallisation endpoint, or the condensed category.  No octonionic or sedenionic
  structure is used beyond the norm form `N` and its polar form `bil`.  The
  identification of `g` with `∇V` is a citation, not a theorem of this file.

  Zero `sorry`, zero `native_decide`, zero vacuous `True`.  `#print axioms` at the end.
-/
import QBP.Foundations.CDDimension
import QBP.Foundations.Alternator
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod

namespace QBP.Foundations.TransitionState

open QBP.Foundations.CDAlg Module

variable {n : ℕ}

/-- `CDAlg ℝ n` is finite-dimensional (it has the standard basis `CDDimension.cdBasis`). -/
instance instFiniteDimensionalCD : FiniteDimensional ℝ (CDAlg ℝ n) :=
  Module.Finite.of_basis (CDDimension.cdBasis n)

/-! ## 1. `bil` as a linear functional -/

/-- Symmetry of the polar form (proved locally so this file needs no `NormForm` import). -/
theorem bil_comm (x y : CDAlg ℝ n) : bil x y = bil y x := by
  simp only [bil_def]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- `x ↦ bil x y`, the polar form of the Cayley–Dickson norm in its left slot, as an
    `ℝ`-linear functional.  (`bil` is the algebra-supplied Euclidean form: `N x = bil x x`.) -/
def bilFun (y : CDAlg ℝ n) : CDAlg ℝ n →ₗ[ℝ] ℝ where
  toFun x := bil x y
  map_add' x x' := bil_add_left x x' y
  map_smul' r x := by simpa using bil_smul_left r x y

@[simp] theorem bilFun_apply (y x : CDAlg ℝ n) : bilFun y x = bil x y := rfl

/-! ## 2. The tangent space of the imaginary unit sphere -/

/-- The first-order constraints of "stay on the state sphere, stay imaginary":
    `x ↦ (⟪x, s⟫, ⟪x, 1⟫)`.  The second slot is `x₀` (`bil_one_right`). -/
def tangentProbe (s : CDAlg ℝ n) : CDAlg ℝ n →ₗ[ℝ] ℝ × ℝ :=
  (bilFun s).prod (bilFun 1)

/-- **The tangent space at `s`.**  Directions that preserve `N` and the imaginary part
    to first order. -/
def Tangent (s : CDAlg ℝ n) : Submodule ℝ (CDAlg ℝ n) := LinearMap.ker (tangentProbe s)

theorem mem_tangent_iff {s x : CDAlg ℝ n} :
    x ∈ Tangent s ↔ bil x s = 0 ∧ x.coord 0 = 0 := by
  simp only [Tangent, LinearMap.mem_ker, tangentProbe, LinearMap.prod_apply, Function.prod,
    bilFun_apply, Prod.mk_eq_zero, bil_one_right]

/-! ## 3. The `V`-neutral directions -/

/-- The full first-order probe: stay on the sphere, stay imaginary, and do not move the
    potential — `x ↦ (⟪x, s⟫, ⟪x, 1⟫, ⟪x, g⟫)` with `g` the gradient of the potential. -/
def vProbe (s g : CDAlg ℝ n) : CDAlg ℝ n →ₗ[ℝ] ℝ × ℝ × ℝ :=
  (bilFun s).prod ((bilFun 1).prod (bilFun g))

/-- **The `V`-neutral directions at `s`.**  Tangential directions along which the
    potential is stationary to first order: the deformations of a dynamical rule that
    *no* invariant of the potential's level sets can detect. -/
def VNeutral (s g : CDAlg ℝ n) : Submodule ℝ (CDAlg ℝ n) := LinearMap.ker (vProbe s g)

theorem mem_vNeutral_iff {s g x : CDAlg ℝ n} :
    x ∈ VNeutral s g ↔ bil x s = 0 ∧ x.coord 0 = 0 ∧ bil x g = 0 := by
  simp only [VNeutral, LinearMap.mem_ker, vProbe, LinearMap.prod_apply, Function.prod,
    bilFun_apply, Prod.mk_eq_zero, bil_one_right]

theorem vNeutral_le_tangent (s g : CDAlg ℝ n) : VNeutral s g ≤ Tangent s := by
  intro x hx
  rw [mem_vNeutral_iff] at hx
  rw [mem_tangent_iff]
  exact ⟨hx.1, hx.2.1⟩

/-- At a rest point of the gradient (`g = 0` — in particular at every crystal, where
    `RuleFlow.gradV_eq_zero_of_isVacuum` applies) *every* tangential direction is
    `V`-neutral: the potential constrains nothing at all. -/
theorem vNeutral_eq_tangent_of_gradient_zero (s : CDAlg ℝ n) :
    VNeutral s 0 = Tangent s := by
  refine le_antisymm (vNeutral_le_tangent s 0) (fun x hx => ?_)
  rw [mem_tangent_iff] at hx
  rw [mem_vNeutral_iff]
  refine ⟨hx.1, hx.2, ?_⟩
  simp only [bil_def, zero_coord, mul_zero, Finset.sum_const_zero]

/-! ## 4. Surjectivity of the probes -/

variable {s g : CDAlg ℝ n}

/-- `bil 1 1 = 1`. -/
theorem bil_one_one : bil (1 : CDAlg ℝ n) 1 = 1 := by
  rw [bil_one_right, one_coord, if_pos rfl]

theorem tangentProbe_surjective (hs : bil s s = 1) (hs0 : s.coord 0 = 0) :
    Function.Surjective (tangentProbe s) := by
  rintro ⟨a, b⟩
  have h1 : bil s (1 : CDAlg ℝ n) = 0 := by rw [bil_one_right, hs0]
  have h2 : bil (1 : CDAlg ℝ n) s = 0 := by rw [bil_comm, bil_one_right, hs0]
  have e1 : bil (a • s + b • (1 : CDAlg ℝ n)) s = a := by
    rw [bil_add_left, bil_smul_left, bil_smul_left, hs, h2]; ring
  have e2 : bil (a • s + b • (1 : CDAlg ℝ n)) (1 : CDAlg ℝ n) = b := by
    rw [bil_add_left, bil_smul_left, bil_smul_left, h1, bil_one_one]; ring
  refine ⟨a • s + b • (1 : CDAlg ℝ n), ?_⟩
  simp only [tangentProbe, LinearMap.prod_apply, Function.prod, bilFun_apply, Prod.mk.injEq]
  exact ⟨e1, e2⟩

theorem vProbe_surjective (hs : bil s s = 1) (hs0 : s.coord 0 = 0)
    (hg : g ∈ Tangent s) (hg0 : g ≠ 0) : Function.Surjective (vProbe s g) := by
  rw [mem_tangent_iff] at hg
  have hNg : N g ≠ 0 := fun h => hg0 ((alt_N_eq_zero_iff g).mp h)
  have hgg : bil g g = N g := (N_eq_bil g).symm
  rintro ⟨a, b, c⟩
  have h1 : bil s (1 : CDAlg ℝ n) = 0 := by rw [bil_one_right, hs0]
  have h2 : bil (1 : CDAlg ℝ n) s = 0 := by rw [bil_comm, bil_one_right, hs0]
  have h3 : bil g s = 0 := hg.1
  have h5 : bil g (1 : CDAlg ℝ n) = 0 := by rw [bil_one_right, hg.2]
  set x : CDAlg ℝ n := a • s + b • (1 : CDAlg ℝ n) + (c / N g) • g with hxdef
  have e1 : bil x s = a := by
    rw [hxdef, bil_add_left, bil_add_left, bil_smul_left, bil_smul_left, bil_smul_left,
      hs, h2, h3]; ring
  have e2 : bil x (1 : CDAlg ℝ n) = b := by
    rw [hxdef, bil_add_left, bil_add_left, bil_smul_left, bil_smul_left, bil_smul_left,
      h1, bil_one_one, h5]; ring
  have e3 : bil x g = c := by
    rw [hxdef, bil_add_left, bil_add_left, bil_smul_left, bil_smul_left, bil_smul_left,
      bil_comm s g, h3, bil_comm (1 : CDAlg ℝ n) g, h5, hgg]
    field_simp
    ring
  refine ⟨x, ?_⟩
  simp only [vProbe, LinearMap.prod_apply, Function.prod, bilFun_apply, Prod.mk.injEq]
  exact ⟨e1, e2, e3⟩

/-! ## 5. The dimension count — 14 tangential directions, 13 of them `V`-blind -/

/-- **The tangent space of the state sphere is 14-dimensional.**  (`𝕊` is 16-dimensional;
    the sphere condition and imaginarity remove one dimension each, and they are
    independent because `⟪s, 1⟫ = s₀ = 0`.) -/
theorem finrank_tangent {s : CDAlg ℝ 4} (hs : bil s s = 1) (hs0 : s.coord 0 = 0) :
    finrank ℝ (Tangent s) = 14 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (tangentProbe s)
  rw [LinearMap.range_eq_top.mpr (tangentProbe_surjective hs hs0)] at hrk
  have h16 : finrank ℝ (CDAlg ℝ 4) = 16 := by rw [CDDimension.finrank_cdAlg 4]; norm_num
  rw [finrank_top, Module.finrank_prod, Module.finrank_self, h16] at hrk
  have : finrank ℝ (LinearMap.ker (tangentProbe s)) = 14 := by omega
  simpa only [Tangent] using this

/-- **The potential constrains exactly one of those 14 directions.**  At any in-flight
    state where the gradient is tangential and nonzero, the `V`-neutral subspace is
    13-dimensional: a 13-parameter family of first-order rule deformations that the
    potential — and therefore every object built from its level sets — cannot see. -/
theorem finrank_vNeutral {s g : CDAlg ℝ 4} (hs : bil s s = 1) (hs0 : s.coord 0 = 0)
    (hg : g ∈ Tangent s) (hg0 : g ≠ 0) : finrank ℝ (VNeutral s g) = 13 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (vProbe s g)
  rw [LinearMap.range_eq_top.mpr (vProbe_surjective hs hs0 hg hg0)] at hrk
  have h16 : finrank ℝ (CDAlg ℝ 4) = 16 := by rw [CDDimension.finrank_cdAlg 4]; norm_num
  rw [finrank_top, Module.finrank_prod, Module.finrank_prod, Module.finrank_self, h16] at hrk
  have : finrank ℝ (LinearMap.ker (vProbe s g)) = 13 := by omega
  simpa only [VNeutral] using this

/-- **The `V`-blind deformations are genuinely there.**  A nonzero direction exists in
    every `VNeutral s g` with `g` tangential (including `g = ∇V(s)` at an in-flight
    state). -/
theorem exists_vNeutral_ne_zero {s g : CDAlg ℝ 4} (hs : bil s s = 1) (hs0 : s.coord 0 = 0)
    (hg : g ∈ Tangent s) (hg0 : g ≠ 0) : ∃ x : CDAlg ℝ 4, x ∈ VNeutral s g ∧ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hbot : VNeutral s g = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    simpa using hcon x hx
  have h13 := finrank_vNeutral hs hs0 hg hg0
  rw [hbot, finrank_bot] at h13
  exact absurd h13 (by norm_num)

/-! ## 5b. Non-vacuity — the hypotheses of §5 are satisfiable

A guard against a vacuously-true dimension theorem: exhibit an imaginary unit state `s`
and a nonzero tangential `g` at it, and instantiate both dimension counts there. -/

/-- Index `1` of the sedenion basis. -/
abbrev idx1 : Fin (2 ^ 4) := ⟨1, by omega⟩
/-- Index `2` of the sedenion basis. -/
abbrev idx2 : Fin (2 ^ 4) := ⟨2, by omega⟩

/-- Two basis directions `e₁`, `e₂` of `𝕊` witness the hypotheses of `finrank_vNeutral`. -/
theorem hypotheses_satisfiable :
    ∃ s g : CDAlg ℝ 4, bil s s = 1 ∧ s.coord 0 = 0 ∧ g ∈ Tangent s ∧ g ≠ 0 := by
  refine ⟨e idx1, e idx2, ?_, ?_, ?_, ?_⟩
  · rw [bil_e, if_pos rfl]
  · rw [e_coord, if_neg (by decide : (0 : Fin (2 ^ 4)) ≠ idx1)]
  · rw [mem_tangent_iff]
    refine ⟨?_, ?_⟩
    · rw [bil_e, if_neg (by decide : idx2 ≠ idx1)]
    · rw [e_coord, if_neg (by decide : (0 : Fin (2 ^ 4)) ≠ idx2)]
  · intro h
    have hc := congrArg (fun z : CDAlg ℝ 4 => z.coord idx2) h
    simp only [e_coord, zero_coord] at hc
    exact one_ne_zero hc

/-- **The dimension counts are instantiated, not vacuous:** there is a concrete state and a
    concrete nonzero tangential gradient direction at which `Tangent` is 14-dimensional and
    `VNeutral` is 13-dimensional. -/
theorem finrank_counts_instantiated :
    ∃ s g : CDAlg ℝ 4, finrank ℝ (Tangent s) = 14 ∧ finrank ℝ (VNeutral s g) = 13 := by
  obtain ⟨s, g, hs, hs0, hg, hg0⟩ := hypotheses_satisfiable
  exact ⟨s, g, finrank_tangent hs hs0, finrank_vNeutral hs hs0 hg hg0⟩

/-! ## 6. What a `V`-blind deformation does to a rule field -/

/-- **Deforming a rule field by a `V`-neutral direction changes nothing the potential
    can measure.**  If `Y` is a tangential rule direction at `s` and `X` is `V`-neutral,
    then `Y + X` is still tangent to the state sphere, still imaginary, and has exactly
    the same first-order rate of change of the potential (`bil · g`, i.e. `fderiv V s ·`
    by `RuleFlow.fderiv_potential_apply`).  Yet `Y + X ≠ Y` whenever `X ≠ 0`. -/
theorem add_vNeutral_preserves_data {s g Y X : CDAlg ℝ n} (hY : Y ∈ Tangent s)
    (hX : X ∈ VNeutral s g) :
    (Y + X) ∈ Tangent s ∧ bil (Y + X) g = bil Y g := by
  rw [mem_vNeutral_iff] at hX
  rw [mem_tangent_iff] at hY
  refine ⟨?_, ?_⟩
  · rw [mem_tangent_iff, bil_add_left, hY.1, hX.1, add_coord, hY.2, hX.2.1]
    exact ⟨by norm_num, by norm_num⟩
  · rw [bil_add_left, hX.2.2, add_zero]

/-- The deformation is a genuine change of the rule field. -/
theorem add_vNeutral_ne {Y X : CDAlg ℝ n} (hX : X ≠ 0) : Y + X ≠ Y := by
  intro h
  exact hX (by simpa using congrArg (fun z => z - Y) h)

/-! ## 7. Completeness audit -/

#print axioms bilFun
#print axioms mem_tangent_iff
#print axioms mem_vNeutral_iff
#print axioms vNeutral_le_tangent
#print axioms vNeutral_eq_tangent_of_gradient_zero
#print axioms bil_one_one
#print axioms tangentProbe_surjective
#print axioms vProbe_surjective
#print axioms finrank_tangent
#print axioms finrank_vNeutral
#print axioms exists_vNeutral_ne_zero
#print axioms hypotheses_satisfiable
#print axioms finrank_counts_instantiated
#print axioms add_vNeutral_preserves_data
#print axioms add_vNeutral_ne

end QBP.Foundations.TransitionState
