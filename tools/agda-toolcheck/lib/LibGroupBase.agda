{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibGroupBase — Cubical.Homotopy.Group.Base.
-- Pins: π'Gr : (n : ℕ) (A : Pointed ℓ) → Group ℓ (the homotopy groups as
-- groups), the pinch sum ∙Π, inverse -Π, unit 1Π on S₊∙ n →∙ A, and ∙Π-rCancel.
-- SkyrmionCharge.agda's additivity and anti-Skyrmion contracts are stated on ∙Π / -Π.
-- Used by QBP: SkyrmionCharge.agda, SubstrateCharge.agda.
module LibGroupBase where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed ; _→∙_)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.HITs.Sn using (S₊∙)
open import Cubical.Algebra.Group.Base using (Group)
open import Cubical.Homotopy.Group.Base using (π'Gr ; ∙Π ; -Π ; 1Π ; ∙Π-rCancel)

private variable
  ℓ : Level

_ : (n : ℕ) (A : Pointed ℓ) → Group ℓ
_ = π'Gr

_ : {A : Pointed ℓ} {n : ℕ} → (S₊∙ n →∙ A) → (S₊∙ n →∙ A) → (S₊∙ n →∙ A)
_ = ∙Π

_ : {A : Pointed ℓ} {n : ℕ} → (S₊∙ n →∙ A) → (S₊∙ n →∙ A)
_ = -Π

_ : {A : Pointed ℓ} {n : ℕ} → (S₊∙ n →∙ A)
_ = 1Π

_ : {A : Pointed ℓ} {n : ℕ} (f : S₊∙ (suc n) →∙ A) → ∙Π f (-Π f) ≡ 1Π
_ = ∙Π-rCancel

-- the group QBP's π₃(S³) ≅ ℤ statement is about, as a type only
π₃S³ : Group ℓ-zero
π₃S³ = π'Gr 2 (S₊∙ 3)
