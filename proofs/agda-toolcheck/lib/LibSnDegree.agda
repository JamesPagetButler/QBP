{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibSnDegree — Cubical.HITs.Sn.Degree.
-- Pins the baryon-number primitive's library layer: degree : (n : ℕ) → (S₊ n → S₊ n) → ℤ
-- and its contracts degreeIdfun (= 1), degreeConst (= 0), degreeHom (additivity
-- under ∙Π), degree∥₂ / degree∥₂Iso (the complete classification ∥S³→S³∥₂ ≅ ℤ).
-- The specific integers (pos 1, pos 0) are the physical content (#595 mandate B).
-- Used by QBP: SkyrmionCharge.agda (`baryonNumber = degree 3`), SubstrateCharge.agda.
module LibSnDegree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (_→∙_)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos) renaming (_+_ to _+ℤ_)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.SetTruncation using (∥_∥₂)
open import Cubical.HITs.Sn.Degree using (degree ; degreeIdfun ; degreeConst ; degreeHom ; degree∥₂ ; degree∥₂Iso)
open import Cubical.Homotopy.Group.Base using (∙Π)

_ : (n : ℕ) → (S₊ n → S₊ n) → ℤ
_ = degree

_ : (n : ℕ) → degree n (λ x → x) ≡ pos 1
_ = degreeIdfun

_ : (n : ℕ) → degree n (λ _ → ptSn n) ≡ pos 0
_ = degreeConst

_ : {n : ℕ} (f g : S₊∙ (suc n) →∙ S₊∙ (suc n))
  → degree (suc n) (∙Π f g .fst) ≡ degree (suc n) (fst f) +ℤ degree (suc n) (fst g)
_ = degreeHom

_ : (n : ℕ) → ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ → ℤ
_ = degree∥₂

_ : (n : ℕ) → Iso ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ ℤ
_ = degree∥₂Iso

-- the S³ instance: the baryon-number primitive and its two pinned values
baryonNumber : (S₊ 3 → S₊ 3) → ℤ
baryonNumber = degree 3

hedgehog-has-charge-one : baryonNumber (λ x → x) ≡ pos 1
hedgehog-has-charge-one = degreeIdfun 3

vacuum-has-charge-zero : baryonNumber (λ _ → ptSn 3) ≡ pos 0
vacuum-has-charge-zero = degreeConst 3
