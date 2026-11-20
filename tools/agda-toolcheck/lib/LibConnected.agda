{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibConnected — Cubical.Homotopy.Connected.
-- Pins: isConnected, isConnectedPath, isConnectedPathP, isConnectedRetractFromIso,
-- isConnectedSubtr — the connectivity toolkit CDAssocCubesStatus.agda uses to show
-- the two-push cubes are merely inhabited (π₂(S³) = 0) and that the 3-push 4-cube
-- is NOT reachable this way (π₃(S³) = ℤ ≠ 0).
-- Used by QBP: CDAssocCubesStatus.agda.
module LibConnected where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels using (HLevel)
open import Cubical.Data.Nat using (suc ; _+_)
open import Cubical.Homotopy.Connected
  using (isConnected ; isConnectedPath ; isConnectedPathP ; isConnectedRetractFromIso ; isConnectedSubtr)

private variable
  ℓ ℓ' : Level

_ : (n : HLevel) (A : Type ℓ) → Type ℓ
_ = isConnected

_ : (n : HLevel) {A : Type ℓ} → isConnected (suc n) A → (a₀ a₁ : A) → isConnected n (a₀ ≡ a₁)
_ = isConnectedPath

_ : (n : HLevel) {P : I → Type ℓ} → isConnected (suc n) (P i1)
  → (a₀ : P i0) (a₁ : P i1) → isConnected n (PathP P a₀ a₁)
_ = isConnectedPathP

_ : (n : HLevel) {A : Type ℓ} {B : Type ℓ'} → Iso A B → isConnected n B → isConnected n A
_ = isConnectedRetractFromIso

_ : {A : Type ℓ} (n m : HLevel) → isConnected (m + n) A → isConnected n A
_ = isConnectedSubtr
