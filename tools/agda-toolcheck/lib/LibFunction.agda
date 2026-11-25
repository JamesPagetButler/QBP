{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibFunction — Cubical.Foundations.Function.
-- Pins: idfun, _∘_.
-- Used by QBP: HopfNoAssoc.agda (`open import Cubical.Foundations.Function`).
module LibFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun ; _∘_)

private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ

_ : (A : Type ℓ) → A → A
_ = idfun

-- the library's composition is dependent (g's first argument is implicit)
_ : {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
_ = _∘_

-- and specialises to the ordinary one
compose : {B : Type ℓ'} {C : Type ℓ''} → (B → C) → (A → B) → A → C
compose g f = g ∘ f
