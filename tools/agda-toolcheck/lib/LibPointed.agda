{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibPointed — Cubical.Foundations.Pointed and .Pointed.Base.
-- Pins: Pointed, typ, pt, _→∙_, idfun∙, and ua∙ (pointed univalence, the
-- transport QBPS3HSpace.agda's HSpace≃ is built on).
-- Used by QBP: CDJoinBR.agda, QBPS3HSpace.agda, S3FromCD.agda, AssocTransport.agda,
-- HopfNoAssoc.agda, SkyrmionCharge.agda.
module LibPointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Pointed using (Pointed ; typ ; pt ; _→∙_ ; idfun∙)
open import Cubical.Foundations.Pointed.Base using (ua∙)

private variable
  ℓ ℓ' : Level

_ : (ℓ : Level) → Type (ℓ-suc ℓ)
_ = Pointed

_ : Pointed ℓ → Type ℓ
_ = typ

_ : (A : Pointed ℓ) → typ A
_ = pt

_ : Pointed ℓ → Pointed ℓ' → Type (ℓ-max ℓ ℓ')
_ = _→∙_

_ : (A : Pointed ℓ) → A →∙ A
_ = idfun∙

_ : {A B : Pointed ℓ} (e : fst A ≃ fst B) → fst e (snd A) ≡ snd B → A ≡ B
_ = ua∙
