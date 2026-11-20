{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibHLevelsGroupoid — Cubical.Foundations.HLevels, .GroupoidLaws, .Path.
-- Pins: isProp→isOfHLevelSuc; rUnit, lCancel; PathP≡doubleCompPathˡ, compPath→Square.
-- Used by QBP: QuaternionicHopf.agda, HopfNoAssoc.agda, SubstrateCharge.agda (HLevels);
-- CDLawsBool.agda, CDAssocBool.agda, SubstrateCharge.agda (GroupoidLaws);
-- SubstrateCharge.agda, CDLawsBool.agda (Path).
module LibHLevelsGroupoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (HLevel ; isOfHLevel ; isProp→isOfHLevelSuc)
open import Cubical.Data.Nat using (suc)
open import Cubical.Foundations.GroupoidLaws using (rUnit ; lCancel)
open import Cubical.Foundations.Path using (PathP≡doubleCompPathˡ ; compPath→Square)

private variable
  ℓ : Level
  A : Type ℓ

_ : (n : HLevel) → isProp A → isOfHLevel (suc n) A
_ = isProp→isOfHLevelSuc

_ : {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
_ = rUnit

_ : {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
_ = lCancel

_ : {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
  → (PathP (λ i → p i ≡ s i) q r) ≡ (sym p ∙∙ q ∙∙ s ≡ r)
_ = PathP≡doubleCompPathˡ

_ : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → p ∙ s ≡ r ∙ q → Square r s p q
_ = compPath→Square
