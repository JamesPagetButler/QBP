{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibTruncations — Cubical.HITs.PropositionalTruncation,
-- .SetTruncation, .Truncation, .Pushout.
-- Pins: ∥_∥₁, ∣_∣₁, squash₁; ∥_∥₂, ∣_∣₂; propTruncTrunc1Iso; Pushout.
-- Used by QBP: QuaternionicHopf.agda, HopfNoAssoc.agda, CDAssocCubesStatus.agda
-- (prop truncation); SkyrmionCharge.agda (set truncation); CDAssocCubesStatus.agda
-- (propTruncTrunc1Iso); HopfNoAssoc.agda (Pushout).
module LibTruncations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.HITs.SetTruncation using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.Truncation using (∥_∥_ ; propTruncTrunc1Iso)
open import Cubical.HITs.Pushout using (Pushout)

private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  B : Type ℓ'
  C : Type ℓ''

_ : Type ℓ → Type ℓ
_ = ∥_∥₁

_ : A → ∥ A ∥₁
_ = ∣_∣₁

_ : (x y : ∥ A ∥₁) → x ≡ y
_ = squash₁

_ : Type ℓ → Type ℓ
_ = ∥_∥₂

_ : A → ∥ A ∥₂
_ = ∣_∣₂

_ : Iso ∥ A ∥₁ (∥ A ∥ 1)
_ = propTruncTrunc1Iso

-- (explicit binders: a generalised `A : Type ℓ` does not share its level with
--  an explicit `ℓ` in the same signature on Agda 2.8.0 — see FEATURES.md)
_ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} (f : X → Y) (g : X → Z) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
_ = Pushout
