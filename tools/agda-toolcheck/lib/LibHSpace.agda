{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibHSpace — Cubical.Homotopy.HSpace.
-- Pins: the HSpace record (fields μ, μₗ, μᵣ, μₗᵣ — the exact shape of
-- S³-HSpace : HSpace (S₊∙ 3)), AssocHSpace (μ-assoc, μ-assoc-filler — the #579
-- obligation, kept DOWNSTREAM of the generic CD machinery), S1-HSpace and
-- S1-AssocHSpace (the ℂ-level base case CDLawsBool.agda builds on).
-- Used by QBP: all 13 proofs/agda-cubical/*.agda files except Diamond.agda.
module LibHSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed ; typ ; pt)
open import Cubical.HITs.Sn using (S₊∙)
open import Cubical.Homotopy.HSpace using (HSpace ; AssocHSpace ; S1-HSpace ; S1-AssocHSpace)

private variable
  ℓ : Level

_ : Pointed ℓ → Type ℓ
_ = HSpace

_ : {A : Pointed ℓ} → HSpace A → Type ℓ
_ = AssocHSpace

-- the four fields, in the form the port projects them
module _ {A : Pointed ℓ} (H : HSpace A) where
  open HSpace H

  _ : typ A → typ A → typ A
  _ = μ

  _ : (x : typ A) → μ (pt A) x ≡ x
  _ = μₗ

  _ : (x : typ A) → μ x (pt A) ≡ x
  _ = μᵣ

  _ : μₗ (pt A) ≡ μᵣ (pt A)
  _ = μₗᵣ

module _ {A : Pointed ℓ} {H : HSpace A} (As : AssocHSpace H) where
  open HSpace H
  open AssocHSpace As

  _ : (x y z : typ A) → μ (μ x y) z ≡ μ x (μ y z)
  _ = μ-assoc

_ : HSpace (S₊∙ 1)
_ = S1-HSpace

_ : AssocHSpace S1-HSpace
_ = S1-AssocHSpace
