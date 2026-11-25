{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibSn — Cubical.HITs.Sn and .Sn.Properties.
-- Pins: S₊, S₊∙, ptSn and the DEFINITIONAL presentation S₊ 3 = Susp (Susp S¹)
-- with ptSn 3 = north (the carrier of S³-HSpace, baryonNumber and HopfS³ —
-- the "S₊∙ 3 presentation" every #575/#595/#579 statement is pinned to);
-- sphereElim, sphereElim2, wedgeconFun, sphereConnected.
-- Used by QBP: QBPS3HSpace.agda, S3FromCD.agda, SkyrmionCharge.agda,
-- SubstrateCharge.agda, QuaternionicHopf.agda, CDAssocBool.agda, CDAssocCubesStatus.agda.
module LibSn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed)
open import Cubical.Foundations.HLevels using (HLevel ; isOfHLevel)
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.HITs.S1 using (S¹)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.Sn.Properties using (sphereElim ; sphereElim2 ; wedgeconFun ; sphereConnected)
open import Cubical.Homotopy.Connected using (isConnected)

private variable
  ℓ : Level

_ : ℕ → Type₀
_ = S₊

_ : ℕ → Pointed ℓ-zero
_ = S₊∙

_ : (n : ℕ) → S₊ n
_ = ptSn

-- the S³ presentation, definitionally
S³-presentation : S₊ 3 ≡ Susp (Susp S¹)
S³-presentation = refl

S³-basepoint : ptSn 3 ≡ north
S³-basepoint = refl

_ : (n : ℕ) {A : S₊ (suc n) → Type ℓ} → ((x : S₊ (suc n)) → isOfHLevel (suc n) (A x))
  → A (ptSn (suc n)) → (x : S₊ (suc n)) → A x
_ = sphereElim

_ : (n : ℕ) {A : S₊ (suc n) → S₊ (suc n) → Type ℓ}
  → ((x y : S₊ (suc n)) → isOfHLevel (suc n) (A x y))
  → A (ptSn (suc n)) (ptSn (suc n)) → (x y : S₊ (suc n)) → A x y
_ = sphereElim2

_ : (n m : ℕ) {A : S₊ (suc n) → S₊ (suc m) → Type ℓ}
  → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel (suc n + suc m) (A x y))
  → (f : (x : _) → A (ptSn (suc n)) x)
  → (g : (x : _) → A x (ptSn (suc m)))
  → (p : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
  → (x : S₊ (suc n)) (y : S₊ (suc m)) → A x y
_ = wedgeconFun

_ : (n : HLevel) → isConnected (suc n) (S₊ n)
_ = sphereConnected
