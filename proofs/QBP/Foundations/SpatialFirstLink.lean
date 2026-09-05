/-
  QBP.Foundations.SpatialFirstLink
  ================================

  #473 AC1, Prop 1 — the *spatial first link* of the proposed condensed → locale chain,
  written out formally (PR #631, doc `docs/foundations/473-ac1-first-link-2026-09-04.md`).

  Informal statement (doc row 1): for a compactly generated space X (in particular any
  compact Hausdorff space, and in particular ℝ, which is metrisable hence sequential hence
  compactly generated) the locale Ω(X) is determined by the condensed set X̲:

      Ω(X) ≅ Ω(condensedSetToTopCat X̲),

  and the composite  CompactlyGenerated → CondensedSet → TopCat → Locale  is naturally
  isomorphic to the direct  CompactlyGenerated → TopCat → Locale.

  Everything here is a composition of Mathlib library facts:
    * `CondensedSet.compactlyGeneratedAdjunctionCounitHomeo` — the counit of the restricted
      adjunction  condensedSetToCompactlyGenerated ⊣ compactlyGeneratedToCondensedSet  is a
      homeomorphism on compactly generated spaces;
    * `topToLocale` — the functor Top → Loc, X ↦ the frame of opens of X (opposite);
    * `CompHausToLocale.faithful` — Top → Loc is faithful on compact Hausdorff spaces
      (Mathlib notes T₀ suffices).
  The ℝ instance needs the universe lift `ULift.{1} ℝ` because `TopCat.toCondensedSet` lives
  at `TopCat.{u+1}` (Red Team PR #631 finding 18); the lift is a homeomorphism, so first
  countability, hence sequentiality, hence compact generation transfer.

  RESEARCH-THREAD anchor: this is NOT a substrate claim and opens no file under
  `proofs/QBP/Substrate/` (doc Prop 2 / empty-Substrate rule). It records that the spatial
  first link was never load-bearing — the Cantor-set anecdote of the ledger is decoration —
  and that AC1's "forcing argument for ℝ" is not delivered by this link (doc §4 firewall).

  Zero `sorry`, zero `native_decide`, zero vacuous `True`. `#print axioms` at the bottom.
-/
import Mathlib.Condensed.TopCatAdjunction
import Mathlib.Topology.Category.Locale
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas

namespace QBP.Foundations.SpatialFirstLink

open CategoryTheory TopologicalSpace Topology CompactlyGenerated CondensedSet

universe u

/-! ## 1. The spatial first link, object form -/

/-- **Prop 1 (object form).**  For a compactly generated space `X`, the locale of `X` is
    recovered from its condensed set: `Ω(condensedSetToTopCat X̲) ≅ Ω(X)` in `Locale`.
    Proof: apply `topToLocale` to the counit homeomorphism of the restricted adjunction. -/
noncomputable def localeIsoOfCondensed (X : TopCat.{u + 1}) [UCompactlyGeneratedSpace.{u} X] :
    topToLocale.obj (condensedSetToTopCat.obj X.toCondensedSet) ≅ topToLocale.obj X :=
  topToLocale.mapIso (TopCat.isoOfHomeo (CondensedSet.compactlyGeneratedAdjunctionCounitHomeo X))

/-- The underlying homeomorphism is the counit `x ↦ x PUnit.unit`; its inverse is continuous
    precisely because `X` is compactly generated. Recorded so the iso is not a black box. -/
theorem localeIsoOfCondensed_hom (X : TopCat.{u + 1}) [UCompactlyGeneratedSpace.{u} X] :
    (localeIsoOfCondensed X).hom =
      topToLocale.map
        (TopCat.isoOfHomeo (CondensedSet.compactlyGeneratedAdjunctionCounitHomeo X)).hom :=
  rfl

/-! ## 2. Functor form: CG → Cond → Top → Loc  ≅  CG → Top → Loc -/

/-- **Prop 1 (functor form).**  The composite functor through condensed sets is naturally
    isomorphic to the direct one, on compactly generated spaces. -/
noncomputable def localeFunctorIso :
    CondensedSet.compactlyGeneratedToCondensedSet.{u} ⋙ condensedSetToTopCat.{u} ⋙
        topToLocale.{u + 1} ≅
      CompactlyGenerated.compactlyGeneratedToTop.{u, u + 1} ⋙ topToLocale.{u + 1} :=
  NatIso.ofComponents (fun X => localeIsoOfCondensed X.toTop) (fun _ => by
    dsimp [localeIsoOfCondensed]
    rfl)

/-- The same natural isomorphism obtained by whiskering the (invertible) counit of the
    restricted adjunction with `CG → Top → Loc`; type-checks against the same statement,
    which is the categorical content of Prop 1. -/
noncomputable def localeFunctorIso' :
    CondensedSet.compactlyGeneratedToCondensedSet.{u} ⋙ condensedSetToTopCat.{u} ⋙
        topToLocale.{u + 1} ≅
      CompactlyGenerated.compactlyGeneratedToTop.{u, u + 1} ⋙ topToLocale.{u + 1} :=
  Functor.isoWhiskerRight (asIso CondensedSet.compactlyGeneratedAdjunction.counit)
    (CompactlyGenerated.compactlyGeneratedToTop ⋙ topToLocale)

/-! ## 3. The ℝ instance -/

/-- `ℝ`, lifted one universe so that `TopCat.toCondensedSet` applies. -/
abbrev RealTop : TopCat.{1} := TopCat.of (ULift.{1} ℝ)

/-- The lift is a homeomorphism, so `ULift ℝ` is first countable … -/
instance : FirstCountableTopology (ULift.{1} ℝ) :=
  (Homeomorph.ulift.{1, 0} (X := ℝ)).isInducing.firstCountableTopology

/-- … hence sequential (Mathlib instance), hence compactly generated (Mathlib instance).
    Stated explicitly so the instance chain is visible. -/
instance realTop_uCompactlyGenerated : UCompactlyGeneratedSpace.{0} RealTop :=
  inferInstance

/-- **Prop 1 for ℝ.**  The locale of ℝ is determined by the condensed set of ℝ. -/
noncomputable def realLocaleIsoOfCondensed :
    topToLocale.obj (condensedSetToTopCat.obj RealTop.toCondensedSet) ≅ topToLocale.obj RealTop :=
  localeIsoOfCondensed RealTop

/-- The locale in question is literally the frame of open sets of (lifted) ℝ. -/
theorem realTop_locale_eq : (topToLocale.obj RealTop : Type 1) = Opens (ULift.{1} ℝ) := rfl

/-- …and that frame is order-isomorphic to the frame of open sets of ℝ itself, via the lift
    homeomorphism — so "ℝ is an instance" is literal, not up to universe bookkeeping. -/
noncomputable def realOpensOrderIso : Opens (ULift.{1} ℝ) ≃o Opens ℝ :=
  (Homeomorph.ulift.{1, 0} (X := ℝ)).opensCongr

/-! ## 4. Faithfulness (library facts, cited by type-check) -/

/-- Top → Loc is faithful on compact Hausdorff spaces (Mathlib: T₀ suffices). -/
example : (compHausToTop ⋙ topToLocale.{u}).Faithful := inferInstance

/-- CG → Cond is fully faithful: two continuous maps of compactly generated spaces that
    agree as condensed maps agree. -/
noncomputable example : CondensedSet.compactlyGeneratedToCondensedSet.{u}.FullyFaithful :=
  CondensedSet.fullyFaithfulCompactlyGeneratedToCondensedSet

#print axioms localeIsoOfCondensed
#print axioms localeIsoOfCondensed_hom
#print axioms localeFunctorIso
#print axioms localeFunctorIso'
#print axioms realTop_uCompactlyGenerated
#print axioms realLocaleIsoOfCondensed
#print axioms realTop_locale_eq
#print axioms realOpensOrderIso

end QBP.Foundations.SpatialFirstLink
