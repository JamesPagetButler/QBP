{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibUnivalence — Cubical.Foundations.Univalence and .Transport.
-- Pins: ua, uaβ, ua-gluePt, ua-unglue, ua→, EquivJ; transport⁻. Also pins the
-- library's univalence COMPUTING on a non-trivial equivalence:
-- transport (ua notEquiv) true ≡ false, by uaβ (the tool layer could only do
-- this for the identity, since it has no isEquiv proof for `not`).
-- Used by QBP: HopfNoAssoc.agda (ua, ua-gluePt, ua-unglue, ua→, EquivJ),
-- QuaternionicHopf.agda (ua), HopfNoAssoc.agda (Transport).
module LibUnivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; equivFun ; idEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; ua-gluePt ; ua-unglue ; ua→ ; EquivJ)
open import Cubical.Foundations.Transport using (transport⁻)
open import Cubical.Data.Bool using (Bool ; true ; false ; notEquiv)

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

_ : A ≃ B → A ≡ B
_ = ua

_ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ equivFun e x
_ = uaβ

_ : (e : A ≃ B) (i : I) (x : A) → ua e i
_ = ua-gluePt

_ : (e : A ≃ B) (i : I) (x : ua e i) → B
_ = ua-unglue

_ : {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {P : (i : I) → Type ℓ'}
    {f₀ : A₀ → P i0} {f₁ : A₁ → P i1}
  → ((a : A₀) → PathP P (f₀ a) (f₁ (e .fst a)))
  → PathP (λ i → ua e i → P i) f₀ f₁
_ = ua→

_ : {A B : Type ℓ} (P : (A : Type ℓ) → (e : A ≃ B) → Type ℓ')
  → (r : P B (idEquiv B)) → (e : A ≃ B) → P A e
_ = EquivJ

_ : A ≡ B → B → A
_ = transport⁻

-- univalence computes on `not`
ua-not-true : transport (ua notEquiv) true ≡ false
ua-not-true = uaβ notEquiv true
