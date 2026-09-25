import Mathlib.Topology.Sets.Opens
import Mathlib.Order.Nucleus
import Mathlib.Topology.Closure
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# QBP.Foundations.LocaleDynamics — can a frame supply the dynamical rule?

**Research file for #473 Prop 12 / Prop 13(b) (ATTACK 3 on `KILLED-locale-forcing-route`).**
Foundation-layer discipline applies: Mathlib-only imports, no `QBP.Physics`, no
`QBP.Substrate`, zero `sorry`, zero `native_decide`, zero `True`-stubs.  Nothing
here is anchored and nothing here is ruled.

## What is being tested

`docs/foundations/473-ac1-first-link-2026-09-04.md`, Prop 12, says the
condensed/locale route supplies neither the class of initial measures nor the
dynamical rule, and leaves an explicit loophole: *"(Not 'a locale cannot supply
dynamics by kind': domain theory IS locales-as-computation; the objection is the
rule-dependence, which is testable.)"*  Prop 13(b) is the reversal clause: the
kill reverses if some mechanism supplies *the dynamical rule itself* from
topological/measure data.

This file works that loophole in the only honest way available to a foundation
file: it fixes a topological space `X` and a **continuous potential**
`V : C(X, ℝ)` and asks what a *frame-level* mechanism definable from `V` alone
can do.  Everything below is generic in `(X, V)`.  It does **not** import the
QBP state sphere — the point is precisely that the answers depend on nothing but
`(X, V)`, so the substrate's `StateSphere`/`potential` pair is one instance.

## Vocabulary (fixed here, used nowhere else in the corpus)

* `defOpens V` — the **V-definable opens**: the image of the frame homomorphism
  `V* = Opens.comap V : Ω(ℝ) → Ω(X)`.  A subframe of `Ω(X)` (§1), and, being the
  image of a frame homomorphism, a frame quotient of `Ω(ℝ)`.
* `Saturated V U` — `U` is a union of level sets of `V`.
* `Preserves V h` — the homeomorphism `h` preserves `V` (`V ∘ h = V`).
* `Natural V f` — the frame endomap `f` commutes with `h*` for every
  `V`-preserving homeomorphism `h`.  This is the "definable from `V` alone"
  condition, in its concrete equivariance form.

## The four results

1. **§1–§2 (the sealed position, where it is true).**  For **compact** `X` the
   `V`-definable opens are exactly the `V`-saturated opens
   (`mem_defOpens_iff_saturated`).  A `V`-natural endomap then sends
   `V`-definable opens to `V`-definable opens (`natural_maps_defOpens`) and hence
   **factors through `V*` on the `V`-definable subframe**
   (`natural_factors_through_comap`), under one further hypothesis:
   `FibrewiseTransitive V`, that the `V`-preserving homeomorphisms act
   transitively on each level set.  So on `defOpens`, nothing `V`-natural can see
   inside a level set.  That is the theorem-shaped form of the driver's position.
   **The transitivity hypothesis is an assumption, not a theorem**, and it is the
   weak joint: if it fails (level sets with non-homeomorphic pieces), a
   `V`-natural map can already distinguish those pieces, which only widens the
   crack of §3.

2. **§3 (the crack).**  The sealed position is **false on all of `Ω(X)`**.  The
   closed sublocale of the vacuum `{V = 0}` is given by the nucleus
   `j(U) = U ⊔ V⁻¹(ℝ∖{0})`.  It is built from a single `V`-definable open, it is
   `V`-natural (`vacNucleus_natural`), its fixed opens are exactly the opens
   above `V⁻¹(ℝ∖{0})` and they biject with the opens of the vacuum subspace
   (`vacNucleus_trace_surjective`, `vacNucleus_trace_injective`) — so it **does**
   distinguish points inside the level set `{V = 0}`
   (`crack_vacNucleus_separates_inside_level_set`), and it is **not** a function
   of `V`'s values (`crack_vacNucleus_not_defOpens`).  Locale theory supplies the
   vacuum *sublocale*, with its full internal topology, `V`-naturally.  What it
   does not supply is a measure on it (§5).

3. **§4 (domain theory: "descend one notch" fixes nothing).**  The sublevel
   filtration `{V < c}` is the canonical Scott-style descent.  Its infimum in the
   frame is exactly the *interior* of the vacuum (`iInf_sublevel_eq_interior`),
   hence `⊥` whenever the vacuum has empty interior
   (`iInf_sublevel_eq_bot_of_interior_eq_empty`) — which is the QBP case (a
   2-sphere of vacua inside `S¹⁴`).  So the least fixed point of the only
   canonical frame-native descent is the empty open: it selects **no** point and
   **no** subset of the vacuum.

4. **§5 (valuations: naturality kills the measure).**  With valuations in
   Vickers' sense (modular, monotone, `ν ⊥ = 0`), a `V`-natural valuation is
   invariant under *every* `V`-preserving homeomorphism.  `eq_zero_of_compressed`
   turns that into a vanishing theorem: an open with infinitely many pairwise
   disjoint `V`-natural translates carries valuation `0`.  Instantiated on `ℝ`
   with a constant potential — the maximally degenerate "everything is one level
   set" case — this gives `natural_valuation_vanishes_of_const`: **the only
   `V`-natural valuation is the one that vanishes on every bounded interval.**
   The homeomorphism group of a level set is far too big to preserve a measure;
   the surface measure QBP uses is invariant only under the *isometries* of the
   `N`-metric.  That is Prop 13(b)'s "data beyond the frame", made into a
   theorem for this class.

Companion note: `analysis/473-kill-attack/attack3_locale_dynamics.md`.
-/

namespace QBP.Foundations.LocaleDynamics

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X]

/-! ## §1  The `V`-definable subframe -/

/-- The **`V`-definable opens**: the image of the frame homomorphism
`V* = Opens.comap V : Ω(ℝ) → Ω(X)`.  These are the opens a construction can name
using only the sublevel/superlevel data of `V` and frame operations. -/
def defOpens (V : C(X, ℝ)) : Set (Opens X) := Set.range (Opens.comap V)

theorem mem_defOpens (V : C(X, ℝ)) (W : Opens ℝ) : Opens.comap V W ∈ defOpens V :=
  ⟨W, rfl⟩

theorem bot_mem_defOpens (V : C(X, ℝ)) : (⊥ : Opens X) ∈ defOpens V :=
  ⟨⊥, map_bot (Opens.comap V)⟩

theorem top_mem_defOpens (V : C(X, ℝ)) : (⊤ : Opens X) ∈ defOpens V :=
  ⟨⊤, map_top (Opens.comap V)⟩

theorem inf_mem_defOpens {V : C(X, ℝ)} {U₁ U₂ : Opens X}
    (h₁ : U₁ ∈ defOpens V) (h₂ : U₂ ∈ defOpens V) : U₁ ⊓ U₂ ∈ defOpens V := by
  obtain ⟨W₁, rfl⟩ := h₁
  obtain ⟨W₂, rfl⟩ := h₂
  exact ⟨W₁ ⊓ W₂, map_inf (Opens.comap V) W₁ W₂⟩

theorem sup_mem_defOpens {V : C(X, ℝ)} {U₁ U₂ : Opens X}
    (h₁ : U₁ ∈ defOpens V) (h₂ : U₂ ∈ defOpens V) : U₁ ⊔ U₂ ∈ defOpens V := by
  obtain ⟨W₁, rfl⟩ := h₁
  obtain ⟨W₂, rfl⟩ := h₂
  exact ⟨W₁ ⊔ W₂, map_sup (Opens.comap V) W₁ W₂⟩

/-- `defOpens V` is closed under **arbitrary** joins: it is a subframe of `Ω(X)`.
Together with `inf_mem_defOpens`/`top_mem_defOpens` this is the statement that the
`V`-definable opens form a subframe; being the image of the frame homomorphism
`V*`, it is a frame quotient of `Ω(ℝ)` (`defOpens` is by definition
`Set.range (Opens.comap V)`). -/
theorem sSup_mem_defOpens {V : C(X, ℝ)} {S : Set (Opens X)}
    (hS : ∀ U ∈ S, U ∈ defOpens V) : sSup S ∈ defOpens V := by
  refine ⟨sSup {W : Opens ℝ | Opens.comap V W ∈ S}, ?_⟩
  rw [map_sSup (Opens.comap V)]
  congr 1
  apply Set.Subset.antisymm
  · rintro U ⟨W, hW, rfl⟩; exact hW
  · rintro U hU
    obtain ⟨W, rfl⟩ := hS U hU
    exact ⟨W, hU, rfl⟩

/-- A set is **`V`-saturated** when it is a union of level sets of `V`. -/
def Saturated (V : X → ℝ) (U : Set X) : Prop := ∀ x y, V x = V y → (x ∈ U ↔ y ∈ U)

/-- **Every `V`-definable open is `V`-saturated** — it cannot separate two points
with the same potential.  This is the precise sense in which a construction that
factors through `V*` "moves nothing inside a level set". -/
theorem saturated_of_mem_defOpens {V : C(X, ℝ)} {U : Opens X} (hU : U ∈ defOpens V) :
    Saturated V (U : Set X) := by
  obtain ⟨W, rfl⟩ := hU
  intro x y hxy
  simp only [SetLike.mem_coe, Opens.mem_comap, hxy]

/-- Converse to `saturated_of_mem_defOpens`, crude form: if `V` carries this
saturated open to an open subset **of `ℝ`**, it is `V`-definable.

**Honesty note.**  The hypothesis `IsOpen (V '' U)` is strong and is *not*
generally satisfiable in the case of interest: for `V : S¹⁴ → [0, 1]` the
saturated open `{V < 1/2}` has image `[0, 1/2)`, open in the *range* but not in
`ℝ`.  The usable form is `mem_defOpens_of_saturated_of_compactSpace` below, which
needs no hypothesis beyond compactness of `X`; this lemma is kept only because it
is the general-topology statement. -/
theorem mem_defOpens_of_saturated {V : C(X, ℝ)} (U : Opens X)
    (hsat : Saturated V (U : Set X)) (himg : IsOpen (V '' (U : Set X))) :
    U ∈ defOpens V := by
  refine ⟨⟨V '' (U : Set X), himg⟩, ?_⟩
  apply Opens.ext
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, hxy⟩
    exact (hsat x y hxy.symm).2 hy
  · rintro x hx
    exact ⟨x, hx, rfl⟩

/-- **Converse to `saturated_of_mem_defOpens`, usable form.**  On a *compact*
space — the QBP case, `X = S¹⁴` — every `V`-saturated open is `V`-definable, with
no further hypothesis.  Proof: `Uᶜ` is compact, so `V '' Uᶜ` is compact hence
closed in `ℝ`, and saturation gives `U = V⁻¹((V '' Uᶜ)ᶜ)`.

Together with `saturated_of_mem_defOpens` this is an exact characterisation for
compact `X`: *`V`-definable ⇔ `V`-saturated*. -/
theorem mem_defOpens_of_saturated_of_compactSpace [CompactSpace X] {V : C(X, ℝ)}
    (U : Opens X) (hsat : Saturated V (U : Set X)) : U ∈ defOpens V := by
  have hC : IsCompact ((U : Set X)ᶜ) := (U.isOpen.isClosed_compl).isCompact
  have hVC : IsClosed (V '' (U : Set X)ᶜ) := (hC.image V.continuous).isClosed
  refine ⟨⟨(V '' (U : Set X)ᶜ)ᶜ, hVC.isOpen_compl⟩, ?_⟩
  apply Opens.ext
  ext x
  constructor
  · intro hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩
  · intro hxU
    rintro ⟨y, hy, hxy⟩
    exact hy ((hsat y x hxy).2 hxU)

/-- Exact characterisation on a compact space: the `V`-definable opens are
precisely the `V`-saturated opens. -/
theorem mem_defOpens_iff_saturated [CompactSpace X] {V : C(X, ℝ)} (U : Opens X) :
    U ∈ defOpens V ↔ Saturated V (U : Set X) :=
  ⟨saturated_of_mem_defOpens, mem_defOpens_of_saturated_of_compactSpace U⟩

/-! ## §2  `V`-naturality, and where the sealed position is true -/

/-- A homeomorphism of `X` that **preserves the potential**. -/
def Preserves (V : X → ℝ) (h : X ≃ₜ X) : Prop := ∀ x, V (h x) = V x

/-- The frame automorphism `h*` induced by a homeomorphism. -/
def act (h : X ≃ₜ X) : Opens X → Opens X := Opens.comap (h : C(X, X))

@[simp] theorem mem_act {h : X ≃ₜ X} {U : Opens X} {x : X} : x ∈ act h U ↔ h x ∈ U :=
  Iff.rfl

/-- A frame endomap is **`V`-natural** when it commutes with `h*` for every
`V`-preserving homeomorphism `h`.  This is the concrete, equivariance form of
"definable from `V` alone". -/
def Natural (V : X → ℝ) (f : Opens X → Opens X) : Prop :=
  ∀ h : X ≃ₜ X, Preserves V h → ∀ U, f (act h U) = act h (f U)

/-- Every `V`-definable open is fixed by every `V`-preserving homeomorphism. -/
theorem act_eq_self_of_mem_defOpens {V : C(X, ℝ)} {h : X ≃ₜ X} (hh : Preserves V h)
    {U : Opens X} (hU : U ∈ defOpens V) : act h U = U := by
  obtain ⟨W, rfl⟩ := hU
  apply Opens.ext
  ext x
  simp only [SetLike.mem_coe, mem_act, Opens.mem_comap, hh x]

/-- The `V`-preserving homeomorphisms act **transitively on each level set** of
`V`.  (For the QBP state sphere this holds: each level set of the potential is a
compact manifold-like orbit and the `V`-preserving homeomorphism group is the
full homeomorphism group of the fibration; it is assumed, not proved, here.) -/
def FibrewiseTransitive (V : X → ℝ) : Prop :=
  ∀ x y : X, V x = V y → ∃ h : X ≃ₜ X, Preserves V h ∧ h x = y

/-- Under fibrewise transitivity, an open fixed by every `V`-preserving
homeomorphism is `V`-saturated. -/
theorem saturated_of_act_eq_self {V : C(X, ℝ)} (ht : FibrewiseTransitive V) {U : Opens X}
    (hinv : ∀ h : X ≃ₜ X, Preserves V h → act h U = U) : Saturated V (U : Set X) := by
  intro x y hxy
  obtain ⟨h, hh, rfl⟩ := ht x y hxy
  have := hinv h hh
  constructor
  · intro hx
    have : x ∈ act h U := by rw [this]; exact hx
    exact this
  · intro hy
    have hx : x ∈ act h U := hy
    rw [this] at hx
    exact hx

/-- **The sealed position, where it is true.**  A `V`-natural frame endomap sends
`V`-definable opens to `V`-definable opens, given fibrewise transitivity and the
quotient hypothesis. -/
theorem natural_maps_defOpens [CompactSpace X] {V : C(X, ℝ)} (ht : FibrewiseTransitive V)
    {f : Opens X → Opens X} (hf : Natural V f) {U : Opens X} (hU : U ∈ defOpens V) :
    f U ∈ defOpens V := by
  have hinv : ∀ h : X ≃ₜ X, Preserves V h → act h (f U) = f U := by
    intro h hh
    rw [← hf h hh U, act_eq_self_of_mem_defOpens hh hU]
  have hsat := saturated_of_act_eq_self ht hinv
  exact mem_defOpens_of_saturated_of_compactSpace (f U) hsat

/-- **Factorisation.**  A `V`-natural frame endomap restricted to the
`V`-definable subframe factors through `V*`: there is `φ : Ω(ℝ) → Ω(ℝ)` with
`f (V* W) = V* (φ W)` for every `W`.  This is the driver's sealed position, now a
theorem — *on `defOpens`*.  §3 shows it fails on all of `Ω(X)`. -/
theorem natural_factors_through_comap [CompactSpace X] {V : C(X, ℝ)}
    (ht : FibrewiseTransitive V)
    {f : Opens X → Opens X} (hf : Natural V f) :
    ∃ φ : Opens ℝ → Opens ℝ, ∀ W : Opens ℝ,
      f (Opens.comap V W) = Opens.comap V (φ W) := by
  have hex : ∀ W : Opens ℝ, ∃ W' : Opens ℝ, f (Opens.comap V W) = Opens.comap V W' := by
    intro W
    obtain ⟨W', hW'⟩ := natural_maps_defOpens ht hf (mem_defOpens V W)
    exact ⟨W', hW'.symm⟩
  exact ⟨fun W => (hex W).choose, fun W => (hex W).choose_spec⟩

/-! ## §3  The crack: the vacuum sublocale is `V`-native and *does* see inside -/

/-- The vacuum: the zero level set of the potential. -/
def vacuum (V : X → ℝ) : Set X := V ⁻¹' {0}

/-- The complement of the vacuum, as an open.  It is `V`-definable — it is
`V*` of the open `ℝ ∖ {0}`. -/
def nonVac (V : C(X, ℝ)) : Opens X := Opens.comap V ⟨{c : ℝ | c ≠ 0}, isOpen_ne⟩

@[simp] theorem mem_nonVac {V : C(X, ℝ)} {x : X} : x ∈ nonVac V ↔ V x ≠ 0 := Iff.rfl

theorem nonVac_mem_defOpens (V : C(X, ℝ)) : nonVac V ∈ defOpens V := mem_defOpens V _

theorem coe_nonVac (V : C(X, ℝ)) : (nonVac V : Set X) = (vacuum V)ᶜ := by
  ext x
  simp [vacuum, nonVac]

/-- **The closed sublocale of the vacuum**, as a nucleus on `Ω(X)`:
`j(U) = U ⊔ V⁻¹(ℝ ∖ {0})`.  It is built from a single `V`-definable open. -/
def vacNucleus (V : C(X, ℝ)) : Nucleus (Opens X) where
  toFun U := U ⊔ nonVac V
  map_inf' a b := by
    apply Opens.ext
    ext x
    simp only [Opens.coe_sup, Opens.coe_inf, Set.mem_union, Set.mem_inter_iff]
    tauto
  idempotent' a := le_of_eq (by rw [sup_assoc, sup_idem])
  le_apply' _ := le_sup_left

@[simp] theorem vacNucleus_apply (V : C(X, ℝ)) (U : Opens X) :
    vacNucleus V U = U ⊔ nonVac V := rfl

/-- The vacuum nucleus is **`V`-natural**: it commutes with `h*` for every
`V`-preserving homeomorphism. -/
theorem vacNucleus_natural (V : C(X, ℝ)) : Natural V (fun U => vacNucleus V U) := by
  intro h hh U
  simp only [vacNucleus_apply, act]
  rw [map_sup (Opens.comap (h : C(X, X)))]
  congr 1
  exact (act_eq_self_of_mem_defOpens hh (nonVac_mem_defOpens V)).symm

/-- The fixed opens of the vacuum nucleus are exactly the opens above the
non-vacuum. -/
theorem vacNucleus_fixed_iff (V : C(X, ℝ)) (U : Opens X) :
    vacNucleus V U = U ↔ nonVac V ≤ U := by
  simp only [vacNucleus_apply, sup_eq_left]

/-- Every open of the vacuum **subspace** is the trace of a fixed open: the fixed
frame of `vacNucleus V` surjects onto the opens of `{V = 0}`. -/
theorem vacNucleus_trace_surjective (V : C(X, ℝ)) (W : Opens X) :
    vacNucleus V (W ⊔ nonVac V) = W ⊔ nonVac V ∧
      ((W ⊔ nonVac V : Opens X) : Set X) ∩ vacuum V = (W : Set X) ∩ vacuum V := by
  constructor
  · simp only [vacNucleus_apply, sup_assoc, sup_idem]
  · ext x
    simp only [Opens.coe_sup, Set.mem_inter_iff, Set.mem_union, SetLike.mem_coe, mem_nonVac,
      vacuum, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, hv⟩
      · exact ⟨h, hv⟩
      · exact absurd hv h
    · rintro ⟨h, hv⟩
      exact ⟨Or.inl h, hv⟩

/-- A fixed open of the vacuum nucleus is determined by its trace on the vacuum:
the fixed frame injects into the opens of `{V = 0}`.  With
`vacNucleus_trace_surjective` this is the bijection *fixed opens ↔ opens of the
vacuum subspace* — the nucleus recovers the vacuum with its **full** internal
topology. -/
theorem vacNucleus_trace_injective (V : C(X, ℝ)) {U₁ U₂ : Opens X}
    (h₁ : nonVac V ≤ U₁) (h₂ : nonVac V ≤ U₂)
    (htr : ((U₁ : Set X) ∩ vacuum V) = ((U₂ : Set X) ∩ vacuum V)) : U₁ = U₂ := by
  apply Opens.ext
  ext x
  by_cases hx : V x = 0
  · have : (x ∈ (U₁ : Set X) ∩ vacuum V) ↔ (x ∈ (U₂ : Set X) ∩ vacuum V) := by rw [htr]
    simpa [vacuum, hx] using this
  · constructor
    · intro _; exact h₂ (by simpa using hx)
    · intro _; exact h₁ (by simpa using hx)

/-! ### §3a  The crack, witnessed

`X = ℝ`, `V x = max (x - 1) 0`.  The vacuum is `(-∞, 1]`, which contains the two
points `0` and `1/2`.  No `V`-definable open separates them
(`saturated_of_mem_defOpens`), but a `vacNucleus`-fixed open does. -/

/-- The witness potential: continuous, non-negative, vacuum `= (-∞, 1]`. -/
def crackV : C(ℝ, ℝ) :=
  ⟨fun x => max (x - 1) 0, (continuous_id.sub continuous_const).max continuous_const⟩

@[simp] theorem crackV_apply (x : ℝ) : crackV x = max (x - 1) 0 := rfl

theorem crackV_zero : crackV 0 = 0 := by simp [crackV]

theorem crackV_half : crackV (1/2 : ℝ) = 0 := by
  simp only [crackV_apply]
  rw [max_eq_right (by linarith : (1 / 2 : ℝ) - 1 ≤ 0)]

/-- The separating open: `(-∞, 1/4) ∪ {V ≠ 0}`. -/
def crackU : Opens ℝ := ⟨Set.Iio (1/4 : ℝ), isOpen_Iio⟩ ⊔ nonVac crackV

/-- **The crack.**  `crackU` is fixed by the `V`-natural nucleus `vacNucleus crackV`
and it separates two points of the *same* level set `{V = 0}`.  So a `V`-natural
frame endomorphism can move things inside a level set: the driver's sealed
position is false on all of `Ω(X)` (it is true only on `defOpens`, §2). -/
theorem crack_vacNucleus_separates_inside_level_set :
    crackV 0 = crackV (1/2 : ℝ) ∧
      vacNucleus crackV crackU = crackU ∧
      (0 : ℝ) ∈ crackU ∧ (1/2 : ℝ) ∉ crackU := by
  refine ⟨by rw [crackV_zero, crackV_half], ?_, ?_, ?_⟩
  · simp only [crackV, crackU, vacNucleus_apply, sup_assoc, sup_idem]
  · exact Or.inl (by norm_num)
  · rintro (h | h)
    · exact absurd h (by norm_num)
    · exact (mem_nonVac.1 h) crackV_half

/-- **The crack, second form.**  `vacNucleus crackV` does not land in the
`V`-definable subframe: it is not a function of `V`'s values.  (Contrast
`natural_factors_through_comap`: the factorisation is genuinely restricted to
`defOpens`.) -/
theorem crack_vacNucleus_not_defOpens :
    vacNucleus crackV ⟨Set.Iio (1/4 : ℝ), isOpen_Iio⟩ ∉ defOpens crackV := by
  intro hmem
  have hsat := saturated_of_mem_defOpens hmem
  have hV : crackV 0 = crackV (1/2 : ℝ) := by rw [crackV_zero, crackV_half]
  have h0 : (0 : ℝ) ∈ (vacNucleus crackV ⟨Set.Iio (1/4 : ℝ), isOpen_Iio⟩ : Set ℝ) :=
    Or.inl (by norm_num)
  have h1 := (hsat 0 (1/2 : ℝ) hV).1 h0
  rcases h1 with h | h
  · exact absurd h (by norm_num)
  · exact (mem_nonVac.1 h) crackV_half

/-! ## §4  Domain theory: the sublevel filtration fixes nothing -/

/-- The sublevel open `{V < c}` — the canonical Scott-style "descend one notch"
family. -/
def sublevel (V : C(X, ℝ)) (c : ℝ) : Opens X := Opens.comap V ⟨Set.Iio c, isOpen_Iio⟩

@[simp] theorem mem_sublevel {V : C(X, ℝ)} {c : ℝ} {x : X} :
    x ∈ sublevel V c ↔ V x < c := Iff.rfl

theorem sublevel_mem_defOpens (V : C(X, ℝ)) (c : ℝ) : sublevel V c ∈ defOpens V :=
  mem_defOpens V _

theorem sublevel_mono (V : C(X, ℝ)) : Monotone (sublevel V) := by
  intro c c' hc x hx
  exact lt_of_lt_of_le hx hc

/-- **The least fixed point of the canonical frame-native descent is the interior
of the vacuum.**  The infimum, in `Ω(X)`, of the sublevel opens `{V < c}` over
`c > 0` is exactly `interior {V = 0}` (for a non-negative potential). -/
theorem iInf_sublevel_eq_interior {V : C(X, ℝ)} (hV : ∀ x, 0 ≤ V x) :
    (⨅ c : {c : ℝ // 0 < c}, sublevel V c.1) = Opens.interior (vacuum V) := by
  apply le_antisymm
  · -- the infimum is an open set contained in `{V ≤ 0}`, hence in the interior
    have hsub : ((⨅ c : {c : ℝ // 0 < c}, sublevel V c.1 : Opens X) : Set X) ⊆ vacuum V := by
      intro x hx
      have hall : ∀ c : {c : ℝ // 0 < c}, V x < c.1 := by
        intro c
        have : x ∈ sublevel V c.1 := by
          have hle : (⨅ c : {c : ℝ // 0 < c}, sublevel V c.1) ≤ sublevel V c.1 := iInf_le _ c
          exact hle hx
        exact this
      have hle0 : V x ≤ 0 := by
        rcases le_or_gt (V x) 0 with h | h
        · exact h
        · exact absurd (hall ⟨V x, h⟩) (lt_irrefl _)
      have : V x = 0 := le_antisymm hle0 (hV x)
      exact this
    intro x hx
    exact interior_maximal hsub (Opens.isOpen _) hx
  · -- the interior of the vacuum sits below every sublevel open
    apply le_iInf
    intro c x hx
    have hxv : x ∈ vacuum V := interior_subset hx
    have : V x = 0 := hxv
    simp only [mem_sublevel, this]
    exact c.2

/-- **The kill, domain-theory form.**  If the vacuum has empty interior — the QBP
case, where `{V = 0}` is a 2-sphere inside `S¹⁴` — then the least fixed point of
the sublevel descent is `⊥`.  The only canonical frame-native dynamics converges
to the empty open: it selects no point of the vacuum, and a fortiori no measure
on it. -/
theorem iInf_sublevel_eq_bot_of_interior_eq_empty {V : C(X, ℝ)} (hV : ∀ x, 0 ≤ V x)
    (hint : interior (vacuum V) = ∅) :
    (⨅ c : {c : ℝ // 0 < c}, sublevel V c.1) = ⊥ := by
  rw [iInf_sublevel_eq_interior hV]
  apply Opens.ext
  simpa using hint

/-! ## §5  Valuations: `V`-naturality kills the measure -/

/-- A **valuation on the frame of opens** in Vickers' sense (real-valued,
finite): non-negative, `ν ⊥ = 0`, monotone, and modular.  Countable/directed
Scott-continuity is *not* assumed — none of the results below need it, which makes
them stronger. -/
structure LocaleValuation (X : Type*) [TopologicalSpace X] where
  toFun : Opens X → ℝ
  nonneg' : ∀ U, 0 ≤ toFun U
  map_bot' : toFun ⊥ = 0
  mono' : Monotone toFun
  modular' : ∀ U W, toFun (U ⊔ W) + toFun (U ⊓ W) = toFun U + toFun W

namespace LocaleValuation

variable (ν : LocaleValuation X)

/-- Modularity plus `ν ⊥ = 0` gives finite additivity on disjoint opens. -/
theorem map_sup_of_disjoint {U W : Opens X} (h : U ⊓ W = ⊥) :
    ν.toFun (U ⊔ W) = ν.toFun U + ν.toFun W := by
  have hm := ν.modular' U W
  rw [h, ν.map_bot'] at hm
  linarith

/-- Finite additivity over a pairwise-disjoint finite family. -/
theorem sum_eq_sup {ι : Type*} [DecidableEq ι] (g : ι → Opens X)
    (hd : ∀ i j, i ≠ j → g i ⊓ g j = ⊥) (s : Finset ι) :
    ∑ i ∈ s, ν.toFun (g i) = ν.toFun (s.sup g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ν.map_bot']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert, ih]
      rw [ν.map_sup_of_disjoint]
      rw [← disjoint_iff]
      rw [Finset.disjoint_sup_right]
      intro j hj
      rw [disjoint_iff]
      exact hd a j (by rintro rfl; exact ha hj)

/-- **Compression bound.**  `n` pairwise-disjoint opens of equal valuation fit
inside `⊤`, so `n · ν(U) ≤ ν(⊤)`. -/
theorem card_mul_le_top {ι : Type*} [DecidableEq ι] (g : ι → Opens X)
    (hd : ∀ i j, i ≠ j → g i ⊓ g j = ⊥) (s : Finset ι) (r : ℝ)
    (hval : ∀ i ∈ s, ν.toFun (g i) = r) :
    (s.card : ℝ) * r ≤ ν.toFun ⊤ := by
  have hsum : ∑ i ∈ s, ν.toFun (g i) = (s.card : ℝ) * r := by
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum, ν.sum_eq_sup g hd s]
  exact ν.mono' le_top

/-- **Compression vanishing.**  An open with an infinite pairwise-disjoint family
of equal-valuation opens has valuation `0`. -/
theorem eq_zero_of_compressed (U : Opens X) (g : ℕ → Opens X)
    (hd : ∀ i j, i ≠ j → g i ⊓ g j = ⊥) (hval : ∀ i, ν.toFun (g i) = ν.toFun U) :
    ν.toFun U = 0 := by
  by_contra hne
  have hpos : 0 < ν.toFun U := lt_of_le_of_ne (ν.nonneg' U) (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (ν.toFun ⊤ / ν.toFun U)
  have hle : (n : ℝ) * ν.toFun U ≤ ν.toFun ⊤ := by
    have := ν.card_mul_le_top g hd (Finset.range n) (ν.toFun U) (fun i _ => hval i)
    simpa using this
  have : ν.toFun ⊤ < (n : ℝ) * ν.toFun U := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  linarith

end LocaleValuation

/-- A valuation is **`V`-natural** when it is invariant under every `V`-preserving
homeomorphism. -/
def NaturalValuation (V : X → ℝ) (ν : LocaleValuation X) : Prop :=
  ∀ h : X ≃ₜ X, Preserves V h → ∀ U, ν.toFun (act h U) = ν.toFun U

/-- The **`V`-shadow** of a valuation: its pushforward along `V`, a valuation on
`Ω(ℝ)`.  Vickers' direction — the only thing a `V`-definable valuation can be
read off from is a measure on the value line. -/
def pushforward (V : C(X, ℝ)) (ν : LocaleValuation X) : LocaleValuation ℝ where
  toFun W := ν.toFun (Opens.comap V W)
  nonneg' _ := ν.nonneg' _
  map_bot' := by rw [map_bot (Opens.comap V)]; exact ν.map_bot'
  mono' _ _ h := ν.mono' (Opens.comap_mono V h)
  modular' U W := by
    rw [map_sup (Opens.comap V), map_inf (Opens.comap V)]
    exact ν.modular' _ _

/-- On the `V`-definable subframe, a valuation *is* its `V`-shadow: definitional,
but it records that `defOpens` carries no information beyond a measure on `ℝ`. -/
theorem pushforward_apply (V : C(X, ℝ)) (ν : LocaleValuation X) (W : Opens ℝ) :
    (pushforward V ν).toFun W = ν.toFun (Opens.comap V W) := rfl

/-! ### §5a  The instantiation: naturality forbids a measure on a level set

`X = ℝ` with the **constant** potential — the degenerate case where all of `X` is
a single level set, so `Preserves V h` holds for *every* homeomorphism.  A
`V`-natural valuation is then invariant under the full homeomorphism group; the
translations alone already compress every bounded interval to valuation `0`.

This is the frame-level shadow of the classical fact that `Homeo(M)` preserves no
non-zero finite Borel measure on a manifold `M` of positive dimension.  Level sets
of the QBP potential are such manifolds; the surface measure the substrate uses is
invariant only under the *isometry group of the `N`-metric*, which is not
`V`-natural data. -/

/-- The constant potential on `ℝ`. -/
def constV : C(ℝ, ℝ) := ContinuousMap.const ℝ (0 : ℝ)

@[simp] theorem constV_apply (x : ℝ) : constV x = 0 := rfl

theorem preserves_constV (h : ℝ ≃ₜ ℝ) : Preserves constV h := fun _ => rfl

/-- **No `V`-natural measure.**  Every `V`-natural valuation on `ℝ` with the
constant potential vanishes on every bounded open interval.  Hence there is no
`V`-natural valuation concentrating anywhere on a level set that carries a
compressing symmetry — the locale supplies the support (§3) but never the
measure. -/
theorem natural_valuation_vanishes_of_const (ν : LocaleValuation ℝ)
    (hnat : NaturalValuation constV ν) (a b : ℝ) (hab : a < b) :
    ν.toFun ⟨Set.Ioo a b, isOpen_Ioo⟩ = 0 := by
  set d : ℝ := b - a with hd
  have hdpos : 0 < d := by simp only [hd]; linarith
  set U : Opens ℝ := ⟨Set.Ioo a b, isOpen_Ioo⟩ with hU
  set g : ℕ → Opens ℝ := fun k => act (Homeomorph.addRight (-((k : ℝ) * d))) U with hg
  have happ : ∀ t x : ℝ, (Homeomorph.addRight t) x = x + t := fun _ _ => rfl
  have hmem : ∀ (k : ℕ) (x : ℝ), x ∈ g k ↔ (a < x - (k : ℝ) * d ∧ x - (k : ℝ) * d < b) := by
    intro k x
    simp only [hg, mem_act, hU]
    constructor
    · rintro ⟨h1, h2⟩
      rw [happ] at h1 h2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩ <;> rw [happ] <;> linarith
  have hdisj : ∀ i j : ℕ, i ≠ j → g i ⊓ g j = ⊥ := by
    have key : ∀ i j : ℕ, i < j → ∀ x : ℝ, x ∈ g i → x ∈ g j → False := by
      intro i j hij x hxi hxj
      obtain ⟨_, h2⟩ := (hmem i x).1 hxi
      obtain ⟨h3, _⟩ := (hmem j x).1 hxj
      have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
      nlinarith [mul_le_mul_of_nonneg_right hcast hdpos.le]
    intro i j hij
    apply Opens.ext
    ext x
    simp only [Opens.coe_inf, Set.mem_inter_iff, Opens.coe_bot, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h x hxi hxj
    · exact key j i h x hxj hxi
  have hval : ∀ k : ℕ, ν.toFun (g k) = ν.toFun U := by
    intro k
    exact hnat _ (preserves_constV _) U
  exact ν.eq_zero_of_compressed U g hdisj hval


/-! ## §6  Completeness audit — `#print axioms` on every theorem

Every closure below must be a subset of `{propext, Classical.choice, Quot.sound}`:
no `sorry`, no `native_decide`, no `Lean.ofReduceBool`. -/

#print axioms mem_defOpens
#print axioms bot_mem_defOpens
#print axioms top_mem_defOpens
#print axioms inf_mem_defOpens
#print axioms sup_mem_defOpens
#print axioms sSup_mem_defOpens
#print axioms saturated_of_mem_defOpens
#print axioms mem_defOpens_of_saturated
#print axioms mem_defOpens_of_saturated_of_compactSpace
#print axioms mem_defOpens_iff_saturated
#print axioms mem_act
#print axioms act_eq_self_of_mem_defOpens
#print axioms saturated_of_act_eq_self
#print axioms natural_maps_defOpens
#print axioms natural_factors_through_comap
#print axioms mem_nonVac
#print axioms nonVac_mem_defOpens
#print axioms coe_nonVac
#print axioms vacNucleus_apply
#print axioms vacNucleus_natural
#print axioms vacNucleus_fixed_iff
#print axioms vacNucleus_trace_surjective
#print axioms vacNucleus_trace_injective
#print axioms crackV_apply
#print axioms crackV_zero
#print axioms crackV_half
#print axioms crack_vacNucleus_separates_inside_level_set
#print axioms crack_vacNucleus_not_defOpens
#print axioms mem_sublevel
#print axioms sublevel_mem_defOpens
#print axioms sublevel_mono
#print axioms iInf_sublevel_eq_interior
#print axioms iInf_sublevel_eq_bot_of_interior_eq_empty
#print axioms LocaleValuation.map_sup_of_disjoint
#print axioms LocaleValuation.sum_eq_sup
#print axioms LocaleValuation.card_mul_le_top
#print axioms LocaleValuation.eq_zero_of_compressed
#print axioms pushforward_apply
#print axioms constV_apply
#print axioms preserves_constV
#print axioms natural_valuation_vanishes_of_const

end QBP.Foundations.LocaleDynamics
