{-# OPTIONS --cubical --safe --no-import-sorts --guardedness --lossy-unification #-}
-- TOOLCHECK lib/LibPinSn — Cubical.Homotopy.Group.PinSn (πₙ(Sⁿ) ≅ ℤ).
-- Pins: πₙ'Sⁿ≅ℤ : (n : ℕ) → GroupIso (π'Gr n (S₊∙ (suc n))) ℤGroup,
-- πₙ'Sⁿ≅ℤ-idfun∙ (the identity maps to +1) and πₙ'Sⁿ-gen-by-idfun (it generates).
-- Stated at a GENERIC n only: SkyrmionCharge.agda records that concrete-index
-- instances must be spelled verbatim in the library's form or conversion
-- normalises the whole iso (>30 min / 6 GB observed). This file deliberately
-- forces no such normalisation; it carries --lossy-unification exactly as
-- SkyrmionCharge.agda and PinSn itself do.
-- Also pins Cubical.Algebra.Group.{Morphisms,Instances.Int,Properties,ZAction}:
-- GroupIso, ℤGroup, GroupTheory.invUniqueR, gen₁-by.
-- Used by QBP: SkyrmionCharge.agda.
module LibPinSn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (idfun∙)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.HITs.Sn using (S₊∙)
open import Cubical.HITs.SetTruncation using (∣_∣₂)
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupIso)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.ZAction using (gen₁-by)
open import Cubical.Homotopy.Group.Base using (π'Gr)
open import Cubical.Homotopy.Group.PinSn using (πₙ'Sⁿ≅ℤ ; πₙ'Sⁿ≅ℤ-idfun∙ ; πₙ'Sⁿ-gen-by-idfun)

private variable
  ℓ ℓ' : Level

_ : (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
_ = GroupIso

_ : Group ℓ-zero
_ = ℤGroup

_ : (G : Group ℓ) → (g : fst G) → Type ℓ
_ = gen₁-by

_ : (n : ℕ) → GroupIso (π'Gr n (S₊∙ (suc n))) ℤGroup
_ = πₙ'Sⁿ≅ℤ

_ : (n : ℕ) → Iso.fun (fst (πₙ'Sⁿ≅ℤ n)) ∣ idfun∙ _ ∣₂ ≡ pos (suc zero)
_ = πₙ'Sⁿ≅ℤ-idfun∙

_ : (n : ℕ) → gen₁-by (π'Gr n (S₊∙ (suc n))) ∣ idfun∙ _ ∣₂
_ = πₙ'Sⁿ-gen-by-idfun

-- GroupTheory module instantiated at ℤGroup, as SkyrmionCharge does
module ℤTheory = GroupTheory ℤGroup

open GroupStr (snd ℤGroup) using (_·_ ; inv ; 1g)

_ : {g h : ℤ} → g · h ≡ 1g → h ≡ inv g
_ = ℤTheory.invUniqueR
