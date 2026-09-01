{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #607 (follow-up to #595 step 1 / #606): the substrate-connection theorem —
-- the baryon number is ADDITIVE under the substrate's quaternion product.
--
-- Physics (mandate B): #606 established the topological charge
-- B = baryonNumber = degree 3 on Skyrme configurations S³ → S³ and its
-- charge algebra with respect to the *source-side* pinch sum ∙Π. What it
-- could NOT yet say is anything about the *target-side* algebra — the
-- actual quaternion multiplication μ that the #575 Buchholtz–Rijke port
-- puts on the same sphere (S3FromCD.S³-HSpace). This file proves Furey's
-- substrate-connection theorem:
--
--     B(f ⋆ g) = B(f) + B(g),      (f ⋆ g)(x) = μ (f x) (g x)
--
-- the pointwise quaternion product of two Skyrmion fields carries the sum
-- of their baryon numbers — the substrate's SU(2) algebra *induces* the
-- additive topology of the baryon number (the H-space/Eckmann–Hilton
-- mechanism, Pontryagin-style). Corollaries: translating a configuration
-- by ANY unit quaternion a (x ↦ μ a (f x)) preserves its charge, and the
-- left-translation field μ(a,·) itself is a unit Skyrmion, B = +1, for
-- every a — SU(2) acting on itself is charge-neutral.
--
-- Method (the module-abstraction barrier, #607 AC1): #575's μ is
-- univalence-transported (join → S³), and normalizing it is structurally
-- unbounded (exponential hcomp boundary tree; confirmed by analysis and a
-- live near-OOM — see README "Performance discipline"). So EVERYTHING here
-- is proved inside `module SubstrateLink (H : HSpace (S₊∙ 3))`, where μ,
-- μₗ, μᵣ are *neutral variables that cannot unfold*. The proof is pure
-- path algebra over a neutral μ:
--
--  * interchange: (f ∙Π g) ⋆ (h ∙Π k) ~ (f ⋆ h) ∙Π (g ⋆ k), by suspension
--    induction — the merid square is cong₂-functoriality of μ over path
--    composition plus conjugation bookkeeping (Eckmann–Hilton's engine);
--  * unit laws: 1Π ⋆ g ~ g and f ⋆ 1Π ~ f, pointwise by μₗ/μᵣ;
--  * then B(f ⋆ g) = B((f ∙Π 1Π) ⋆ (1Π ∙Π g)) = B((f ⋆ 1Π) ∙Π (1Π ⋆ g))
--    = B(f ⋆ 1Π) + B(1Π ⋆ g) = B f + B g, using #606's degreeHom.
--
-- The theorems are then instantiated at the concrete S³-HSpace by plain
-- application — the checker only substitutes, it never normalizes μ — with
-- the statements spelled syntactically verbatim (the same discipline that
-- fixed the π₃ block in SkyrmionCharge.agda).
--
-- Scoping note (#575/#579): only the plain HSpace record is used — no
-- AssocHSpace, no associativity anywhere. The whole development would
-- instantiate verbatim at a future S⁷/octonion H-space (non-associative),
-- as the eventual G₂ generalization requires.
--
-- Convention note (#578 AC5): S³-HSpace descends from the Baez-convention
-- Cayley–Dickson port ((a,b)(c,d) = (ac − db*, a*d + cb)); any comparison
-- with the Lean #474 Schafer-convention octonions must route through
-- φ(a,b) = (a,b*). Nothing here identifies components across the two.
--
-- Everything is --safe with agda/cubical @ 7b9019b2 (cubical-0.9);
-- no postulates, no holes, no pragmas.

module SubstrateCharge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (PathP≡doubleCompPathˡ)
open import Cubical.Foundations.GroupoidLaws
  using (rUnit ; ∙∙lCancel ; doubleCompPath-elim)
open import Cubical.Foundations.HLevels
  using (isPropΠ ; isProp→isOfHLevelSuc)

open import Cubical.Data.Int using (ℤ ; pos)
  renaming (_+_ to _+ℤ_)
open import Cubical.Data.Int.Properties using (isSetℤ)

open import Cubical.HITs.Susp using (north ; south ; merid ; toSusp)
open import Cubical.HITs.Sn using (S₊ ; S₊∙)
open import Cubical.HITs.Sn.Properties using (sphereElim)
open import Cubical.HITs.Sn.Degree using (degreeIdfun ; degreeHom)

open import Cubical.Homotopy.Loopspace using (Ω→)
open import Cubical.Homotopy.Group.Base
  using (∙Π ; 1Π ; ∙Π-rUnit ; ∙Π-lUnit)
open import Cubical.Homotopy.HSpace using (HSpace)

open import S3FromCD using (S³-HSpace)
open import SkyrmionCharge
  using (SkyrmeConfig ; SkyrmeConfig∙ ; baryonNumber ; baryonNumber∙)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

-- ————————————————————————————————————————————————————————————————
-- Generic path algebra (no H-space involved): the three groupoid facts
-- the interchange square decomposes into. All proved by J — cheap,
-- fully neutral, no hcomp programming.
-- ————————————————————————————————————————————————————————————————

private
  -- cong₂ is functorial over path composition (in both arguments at once)
  cong₂-∙ : {B : Type ℓ'} {C : Type ℓ''} (m : A → B → C)
    {x y z : A} {u v w : B}
    (p : x ≡ y) (q : y ≡ z) (r : u ≡ v) (s : v ≡ w)
    → cong₂ m (p ∙ q) (r ∙ s) ≡ cong₂ m p r ∙ cong₂ m q s
  cong₂-∙ m p q r s =
    J (λ _ q → cong₂ m (p ∙ q) (r ∙ s) ≡ cong₂ m p r ∙ cong₂ m q s)
      (J (λ _ s → cong₂ m (p ∙ refl) (r ∙ s)
                 ≡ cong₂ m p r ∙ cong₂ m refl s)
         ((λ i → cong₂ m (rUnit p (~ i)) (rUnit r (~ i)))
          ∙ rUnit (cong₂ m p r))
         s)
      q

  -- … and over double composition
  cong₂-∙∙ : {B : Type ℓ'} {C : Type ℓ''} (m : A → B → C)
    {x y z w : A} {x' y' z' w' : B}
    (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
    (p' : x' ≡ y') (q' : y' ≡ z') (r' : z' ≡ w')
    → cong₂ m (p ∙∙ q ∙∙ r) (p' ∙∙ q' ∙∙ r')
     ≡ (cong₂ m p p' ∙∙ cong₂ m q q' ∙∙ cong₂ m r r')
  cong₂-∙∙ m p q r p' q' r' =
       (λ i → cong₂ m (doubleCompPath-elim p q r i)
                      (doubleCompPath-elim p' q' r' i))
    ∙∙ cong₂-∙ m (p ∙ q) r (p' ∙ q') r'
    ∙∙ cong (_∙ cong₂ m r r') (cong₂-∙ m p q p' q')
     ∙ sym (doubleCompPath-elim (cong₂ m p p') (cong₂ m q q')
                                (cong₂ m r r'))

  -- conjugating by a composite = conjugating twice
  conj-∙ : {x y z : A} (P : x ≡ y) (L : y ≡ z) (Q : x ≡ x)
    → (sym (P ∙ L) ∙∙ Q ∙∙ (P ∙ L))
     ≡ (sym L ∙∙ (sym P ∙∙ Q ∙∙ P) ∙∙ L)
  conj-∙ P L Q =
    J (λ _ L → (sym (P ∙ L) ∙∙ Q ∙∙ (P ∙ L))
              ≡ (sym L ∙∙ (sym P ∙∙ Q ∙∙ P) ∙∙ L))
      ((λ i → sym (rUnit P (~ i)) ∙∙ Q ∙∙ rUnit P (~ i))
       ∙ rUnit (sym P ∙∙ Q ∙∙ P))
      L

  -- the Eckmann–Hilton bookkeeping square, as a path equation:
  -- pre-composing with the inverse of a ∙-product of two loops and
  -- post-composing with their L-conjugates collapses to L itself
  exchange : {x y : A} (L : x ≡ y) (c d : x ≡ x)
    → (sym (c ∙ d) ∙∙ L ∙∙ ((sym L ∙∙ c ∙∙ L) ∙ (sym L ∙∙ d ∙∙ L))) ≡ L
  exchange L c d =
    J (λ _ L → (sym (c ∙ d) ∙∙ L
               ∙∙ ((sym L ∙∙ c ∙∙ L) ∙ (sym L ∙∙ d ∙∙ L))) ≡ L)
      ((λ i → sym (c ∙ d) ∙∙ refl ∙∙ (rUnit c (~ i) ∙ rUnit d (~ i)))
       ∙ ∙∙lCancel (c ∙ d))
      L

-- ————————————————————————————————————————————————————————————————
-- The abstraction barrier (#607 AC1): a generic H-space on S₊∙ 3.
-- Inside this module μ, μₗ, μᵣ are neutral variables — nothing the
-- type-checker could ever try to normalize. The quaternionic S³-HSpace
-- is substituted only at the very end, by plain application.
-- ————————————————————————————————————————————————————————————————

module SubstrateLink (H : HSpace (S₊∙ 3)) where

  open HSpace H  -- μ, μₗ, μᵣ (μₗᵣ unused; AssocHSpace deliberately absent)

  -- the substrate product of configurations: pointwise μ
  _⋆_ : SkyrmeConfig → SkyrmeConfig → SkyrmeConfig
  (f ⋆ g) x = μ (f x) (g x)

  -- pointed version (vacuum boundary condition is preserved: μ(1,1) = 1)
  _⋆∙_ : SkyrmeConfig∙ → SkyrmeConfig∙ → SkyrmeConfig∙
  fst (f ⋆∙ g) x = μ (fst f x) (fst g x)
  snd (f ⋆∙ g) = cong₂ μ (snd f) (snd g) ∙ μₗ north

  private
    -- the meridian loop a pointed map traces in the target (the loop
    -- ∙Π composes on merid a)
    Ωσ : SkyrmeConfig∙ → S₊ 2 → Path (S₊ 3) north north
    Ωσ F a = Ω→ F .fst (toSusp (S₊∙ 2) a)

    -- Ω→ of a ⋆∙-product is the μₗ-conjugate of the cong₂-product of
    -- the factors' loops (μ stays neutral: only cong₂/∙∙ bookkeeping)
    Ω⋆ : (F G : SkyrmeConfig∙) (a : S₊ 2)
      → Ωσ (F ⋆∙ G) a
       ≡ (sym (μₗ north) ∙∙ cong₂ μ (Ωσ F a) (Ωσ G a) ∙∙ μₗ north)
    Ω⋆ F G a =
        conj-∙ (cong₂ μ (snd F) (snd G)) (μₗ north)
               (cong (fst (F ⋆∙ G)) (toSusp (S₊∙ 2) a))
      ∙ cong (λ M → sym (μₗ north) ∙∙ M ∙∙ μₗ north)
          (sym (cong₂-∙∙ μ
                 (sym (snd F)) (cong (fst F) (toSusp (S₊∙ 2) a)) (snd F)
                 (sym (snd G)) (cong (fst G) (toSusp (S₊∙ 2) a)) (snd G)))

  -- ——————————————————————————————————————————————————————————
  -- Interchange (Eckmann–Hilton): the target-side product ⋆ and the
  -- source-side pinch sum ∙Π commute, up to (unpointed) homotopy
  -- ——————————————————————————————————————————————————————————

  module _ (f g h k : SkyrmeConfig∙) where

    interchangeFun : (x : S₊ 3)
      → μ (fst (∙Π f g) x) (fst (∙Π h k) x)
       ≡ fst (∙Π (f ⋆∙ h) (g ⋆∙ k)) x
    interchangeFun north = μₗ north
    interchangeFun south = μₗ north
    interchangeFun (merid a i) = sq i
      where
      eqn : (sym (cong₂ μ (Ωσ f a ∙ Ωσ g a) (Ωσ h a ∙ Ωσ k a))
            ∙∙ μₗ north
            ∙∙ (Ωσ (f ⋆∙ h) a ∙ Ωσ (g ⋆∙ k) a))
           ≡ μₗ north
      eqn = (λ i → sym (cong₂-∙ μ (Ωσ f a) (Ωσ g a) (Ωσ h a) (Ωσ k a) i)
                   ∙∙ μₗ north
                   ∙∙ (Ω⋆ f h a i ∙ Ω⋆ g k a i))
          ∙ exchange (μₗ north) (cong₂ μ (Ωσ f a) (Ωσ h a))
                                (cong₂ μ (Ωσ g a) (Ωσ k a))

      sq : PathP (λ i → μ ((Ωσ f a ∙ Ωσ g a) i) ((Ωσ h a ∙ Ωσ k a) i)
                       ≡ (Ωσ (f ⋆∙ h) a ∙ Ωσ (g ⋆∙ k) a) i)
                 (μₗ north) (μₗ north)
      sq = transport
             (sym (PathP≡doubleCompPathˡ
                    (cong₂ μ (Ωσ f a ∙ Ωσ g a) (Ωσ h a ∙ Ωσ k a))
                    (μₗ north) (μₗ north)
                    (Ωσ (f ⋆∙ h) a ∙ Ωσ (g ⋆∙ k) a)))
             eqn

    interchange : fst (∙Π f g ⋆∙ ∙Π h k) ≡ fst (∙Π (f ⋆∙ h) (g ⋆∙ k))
    interchange = funExt interchangeFun

  -- ——————————————————————————————————————————————————————————
  -- THE substrate-connection theorem (#607 AC2):
  -- B(f ⋆ g) = B(f) + B(g) — the H-space algebra induces the
  -- additive baryon topology
  -- ——————————————————————————————————————————————————————————

  ⋆∙-additive : (f g : SkyrmeConfig∙)
    → baryonNumber∙ (f ⋆∙ g) ≡ baryonNumber∙ f +ℤ baryonNumber∙ g
  ⋆∙-additive f g =
      cong baryonNumber
        ( (λ i → fst (∙Π-rUnit f (~ i) ⋆∙ ∙Π-lUnit g (~ i)))
        ∙ interchange f 1Π 1Π g )
    ∙ degreeHom {n = 2} (f ⋆∙ 1Π) (1Π ⋆∙ g)
    ∙ cong₂ _+ℤ_
        (cong baryonNumber (funExt (λ x → μᵣ (fst f x))))
        (cong baryonNumber (funExt (λ x → μₗ (fst g x))))

  -- ——————————————————————————————————————————————————————————
  -- Corollaries: SU(2) self-action is charge-neutral. Since the goal
  -- is a proposition (ℤ is a set), connectedness of S³ lets sphereElim
  -- reduce ANY translation a to the identity quaternion — no μ ever
  -- unfolds, only μₗ at the basepoint.
  -- ——————————————————————————————————————————————————————————

  translationInvariance : (a : S₊ 3) (f : SkyrmeConfig)
    → baryonNumber (λ x → μ a (f x)) ≡ baryonNumber f
  translationInvariance =
    sphereElim 2
      {A = λ a → (f : SkyrmeConfig)
                → baryonNumber (λ x → μ a (f x)) ≡ baryonNumber f}
      (λ _ → isProp→isOfHLevelSuc 2 (isPropΠ (λ _ → isSetℤ _ _)))
      (λ f → cong baryonNumber (funExt (λ x → μₗ (f x))))

  -- every left translation μ(a,·) is itself a unit Skyrmion: B = +1
  leftTranslationCharge : (a : S₊ 3) → baryonNumber (μ a) ≡ pos 1
  leftTranslationCharge a =
    translationInvariance a (λ x → x) ∙ degreeIdfun 3

-- ————————————————————————————————————————————————————————————————
-- Instantiation at the substrate (#575's quaternion multiplication).
-- Plain application of the barrier module — the checker substitutes
-- S³-HSpace but never normalizes its transported μ. Statements are
-- spelled verbatim in terms of HSpace.μ S³-HSpace.
-- ————————————————————————————————————————————————————————————————

-- the substrate's quaternion multiplication on S³ (Baez-convention CD)
_·q_ : S₊ 3 → S₊ 3 → S₊ 3
_·q_ = HSpace.μ S³-HSpace

-- mandate C, the callable primitive: the pointwise quaternion product
-- of two Skyrmion configurations
quaternionProduct∙ : SkyrmeConfig∙ → SkyrmeConfig∙ → SkyrmeConfig∙
quaternionProduct∙ = SubstrateLink._⋆∙_ S³-HSpace

-- its underlying field really is the pointwise product (by definition)
quaternionProduct∙-pointwise : (f g : SkyrmeConfig∙)
  → fst (quaternionProduct∙ f g) ≡ (λ x → fst f x ·q fst g x)
quaternionProduct∙-pointwise f g = refl

-- THE theorem, on the substrate: pointwise quaternion multiplication
-- of Skyrmion fields ADDS baryon numbers
baryonNumber-quaternionProduct-correct : (f g : SkyrmeConfig∙)
  → baryonNumber∙ (quaternionProduct∙ f g)
   ≡ baryonNumber∙ f +ℤ baryonNumber∙ g
baryonNumber-quaternionProduct-correct = SubstrateLink.⋆∙-additive S³-HSpace

-- translating a configuration by any unit quaternion preserves B …
baryonNumber-quaternionTranslation-invariant : (a : S₊ 3) (f : SkyrmeConfig)
  → baryonNumber (λ x → a ·q f x) ≡ baryonNumber f
baryonNumber-quaternionTranslation-invariant =
  SubstrateLink.translationInvariance S³-HSpace

-- … and the left-translation field μ(a,·) is a unit Skyrmion, for EVERY a
baryonNumber-leftTranslation-correct : (a : S₊ 3)
  → baryonNumber (a ·q_) ≡ pos 1
baryonNumber-leftTranslation-correct =
  SubstrateLink.leftTranslationCharge S³-HSpace
