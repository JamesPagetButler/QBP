{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibDataSigma — Cubical.Data.Sigma.
-- Pins: Σ-syntax (`Σ[ x ∈ A ] B`) and Σ≡Prop.
-- Used by QBP: QuaternionicHopf.agda (`Σ≡Prop isPropIsEquiv refl`), HopfNoAssoc.agda.
module LibDataSigma where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax ; Σ≡Prop)

private variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : A → Type ℓ'

_ : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
_ = Σ-syntax

_ : ((x : A) → isProp (B x)) → {u v : Σ[ x ∈ A ] B x} → (p : u .fst ≡ v .fst) → u ≡ v
_ = Σ≡Prop
