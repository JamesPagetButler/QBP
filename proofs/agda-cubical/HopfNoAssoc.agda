{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #579 Step C (fallback form): the associativity-INDEPENDENT half of the
-- library's Hopf construction, lifted out of `Cubical.Homotopy.Hopf`.
--
-- Provenance / licence: this module is a verbatim extraction of
--   agda/cubical @ 7b9019b2993535d6931991d87f5c762aee87a67a,
--   Cubical/Homotopy/Hopf.agda, lines 36–198 (private helper `retEq≡secEq`,
--   `isEquiv-μ`, `isEquiv-μ'`, `μ-eq`, `μ-eq'`, `Hopf`, `TotalSpaceHopfPush`,
--   `TotalSpaceHopfPush→TotalSpace`, `joinIso₁`,
--   `isEquivTotalSpaceHopfPush→TotalSpace`, `IsoTotalSpaceJoin`),
-- © 2018– the github.com/agda/cubical contributors, MIT License
-- (https://github.com/agda/cubical/blob/master/LICENSE). Nothing in the
-- proofs is changed; the ONLY change is the module header: the library's
-- `module Hopf … (e-ass : AssocHSpace e) (conA : …)` takes an associativity
-- witness up front although none of the declarations below use it (e-ass is
-- consumed only by the later `ua-lem` / `Push→TotalSpaceHopf-equiv` /
-- `joinIso₂` section — the join-of-joins TotalSpacePush², not the fibration).
-- Here the header takes just the H-space and the connectivity of its carrier.
--
-- Why this exists: the quaternionic Hopf fibration S³ ↪ S⁷ ↠ S⁴ *as a
-- fibration with total space ≃ S³ * S³* needs only `HSpace (S₊∙ 3)` (which
-- #575 delivers) + `S³` connected. `AssocHSpace S³-HSpace` — the join-level
-- associativity of the Cayley–Dickson product — is the separate, still-open
-- obligation stated in QuaternionicHopf.agda; once it lands, the full library
-- module is instantiated directly (see `QuaternionicHopf.WithAssoc`) and this
-- file becomes redundant.

module HopfNoAssoc where

open import Cubical.Homotopy.HSpace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)
open import Cubical.HITs.Join

open Iso
open HSpace

private
  retEq≡secEq : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B)
                  → (x : _) → secEq e (e .fst x) ≡ cong (e .fst) (retEq e x)
  retEq≡secEq {A = A} =
    EquivJ (λ B e → (x : _) → secEq e (e .fst x) ≡ cong (e .fst) (retEq e x))
           λ _ → refl

-- The library's `Hopf` module minus the unused `e-ass` parameter.
module HopfNA {ℓ : Level} {A : Pointed ℓ} (e : HSpace A)
              (conA : ((x y : typ A) → ∥ x ≡ y ∥₁)) where
  isEquiv-μ : (x : typ A) → isEquiv (λ z → (μ e z x))
  isEquiv-μ x = pRec (isPropIsEquiv _)
                     (J (λ x _ → isEquiv (λ z → μ e z x))
                       (subst isEquiv (funExt (λ z → sym (μᵣ e z)))
                                      (idIsEquiv (typ A))))
                     (conA (pt A) x)

  isEquiv-μ' : (x : typ A) → isEquiv (μ e x)
  isEquiv-μ' x =
    pRec (isPropIsEquiv _)
          (J (λ x _ → isEquiv (μ e x))
            (subst isEquiv (funExt (λ x → sym (μₗ e x))) (idIsEquiv (typ A))))
          (conA (pt A) x)

  μ-eq : (x : typ A) → typ A ≃ typ A
  μ-eq x = (λ z → μ e z x) , (isEquiv-μ x)

  μ-eq' : (x : typ A) → typ A ≃ typ A
  μ-eq' x = μ e x , isEquiv-μ' x

  Hopf : Susp (typ A) → Type ℓ
  Hopf north = typ A
  Hopf south = typ A
  Hopf (merid a i₁) = ua (μ-eq a) i₁

  TotalSpaceHopfPush : Type _
  TotalSpaceHopfPush =
    Pushout {A = typ A × typ A} fst λ x → μ e (fst x) (snd x)

  TotalSpaceHopfPush→TotalSpace :
    TotalSpaceHopfPush → Σ[ x ∈ Susp (typ A) ] Hopf x
  TotalSpaceHopfPush→TotalSpace (inl x) = north , x
  TotalSpaceHopfPush→TotalSpace (inr x) = south , x
  TotalSpaceHopfPush→TotalSpace (push (x , y) i₁) =
    merid y i₁ , ua-gluePt (μ-eq y) i₁ x

  joinIso₁ : Iso (TotalSpaceHopfPush) (join (typ A) (typ A))
  joinIso₁ = theIso
    where
    F : TotalSpaceHopfPush → join (typ A) (typ A)
    F (inl x) = inl x
    F (inr x) = inr x
    F (push (a , x) i) = push a (μ e a x) i

    G : join (typ A) (typ A) → TotalSpaceHopfPush
    G (inl x) = inl x
    G (inr x) = inr x
    G (push a b i) =
      (push (a , invEq (μ-eq' a) b) ∙ cong inr (secEq (μ-eq' a) b)) i

    s : section F G
    s (inl x) = refl
    s (inr x) = refl
    s (push a b i) j =
      hcomp (λ k → λ { (i = i0) → inl a
                      ; (i = i1) → inr (secEq (μ-eq' a) b (j ∨ k))
                      ; (j = i0) → F (compPath-filler
                                       (push (a , invEq (μ-eq' a) b))
                                       (cong inr (secEq (μ-eq' a) b)) k i)
                      ; (j = i1) → push a b i})
        (hcomp (λ k → λ { (i = i0) → inl a
                      ; (i = i1) → inr (secEq (μ-eq' a) b (~ k ∨ j))
                      ; (j = i0) → push a (secEq (μ-eq' a) b (~ k)) i
                      ; (j = i1) → push a b i})
               (push a b i))

    r : retract F G
    r (inl x) = refl
    r (inr x) = refl
    r (push (x , y) i) j =
      hcomp (λ k → λ { (i = i0) → inl x
                      ; (i = i1) → inr (μ e x y)
                      ; (j = i0) → (push (x , invEq (μ-eq' x) (μ e x y))
                                  ∙ (λ i₁ → inr (retEq≡secEq (μ-eq' x) y (~ k) i₁))) i
                      ; (j = i1) → push (x , y) i})
         (hcomp (λ k → λ { (i = i0) → inl x
                      ; (i = i1) → inr (μ e x (retEq (μ-eq' x) y k))
                      ; (j = i1) → push (x , retEq (μ-eq' x) y k) i})
                ((push (x , invEq (μ-eq' x) (μ e x y))) i))

    theIso : Iso TotalSpaceHopfPush (join (typ A) (typ A))
    fun theIso = F
    inv theIso = G
    sec theIso = s
    ret theIso = r

  isEquivTotalSpaceHopfPush→TotalSpace :
    isEquiv TotalSpaceHopfPush→TotalSpace
  isEquivTotalSpaceHopfPush→TotalSpace =
    isoToIsEquiv theIso
    where
    inv' : _ → _
    inv' (north , y) = inl y
    inv' (south , y) = inr y
    inv' (merid a i , y) =
      hcomp (λ k → λ { (i = i0) → push (y , a) (~ k)
                      ; (i = i1) → inr y})
            (inr (ua-unglue (μ-eq a) i y))
      where

      pp : PathP (λ i → ua (μ-eq a) i → TotalSpaceHopfPush)
                 inl inr
      pp = ua→ {e = μ-eq a} {B = λ _ → TotalSpaceHopfPush} λ b → push (b , a)

    sect : (x : _) → TotalSpaceHopfPush→TotalSpace (inv' x) ≡ x
    sect (north , x) = refl
    sect (south , x) = refl
    sect (merid a i , y) j =
      hcomp (λ k → λ { (i = i0) → merid a (~ k ∧ ~ j)
                                  , ua-gluePt (μ-eq a) (~ k ∧ ~ j) y
                      ; (i = i1) → south , y
                      ; (j = i0) →
                        TotalSpaceHopfPush→TotalSpace
                         (hfill (λ k → λ { (i = i0) → push (y , a) (~ k)
                                          ; (i = i1) → inr y})
                                (inS (inr (ua-unglue (μ-eq a) i y)))
                                k)
                      ; (j = i1) → merid a i , y})
            ((merid a (i ∨ ~ j)) , lem (μ-eq a) i j y)
      where
      lem : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) →
                PathP (λ i → PathP (λ j → (y : ua e i) → ua e (i ∨ ~ j))
                 (λ y → ua-unglue e i y)
                 λ y → y)
                 (λ j y → ua-gluePt e (~ j) y)
                 refl
      lem {A = A} {B = B} =
        EquivJ (λ B e → PathP (λ i → PathP (λ j → (y : ua e i) → ua e (i ∨ ~ j))
          (λ y → ua-unglue e i y)
           λ y → y)
           (λ j y → ua-gluePt e (~ j) y)
           refl)
           λ i j a → ua-gluePt (idEquiv B) (i ∨ ~ j) (ua-unglue (idEquiv B) i a)

    retr : retract TotalSpaceHopfPush→TotalSpace inv'
    retr (inl x) = refl
    retr (inr x) = refl
    retr (push (x , y) i) j =
      hcomp (λ k → λ { (i = i0) → push (x , y) (~ k)
                      ; (i = i1) → inr (μ e x y)
                      ; (j = i1) → push (x , y) (i ∨ ~ k)})
            (inr (μ e x y))

    theIso : Iso TotalSpaceHopfPush (Σ (Susp (typ A)) Hopf)
    fun theIso = TotalSpaceHopfPush→TotalSpace
    inv theIso = inv'
    sec theIso = sect
    ret theIso = retr

  IsoTotalSpaceJoin : Iso (Σ[ x ∈ Susp (typ A) ] Hopf x) (join (typ A) (typ A))
  IsoTotalSpaceJoin =
    compIso (equivToIso (invEquiv (_ , isEquivTotalSpaceHopfPush→TotalSpace)))
            joinIso₁
