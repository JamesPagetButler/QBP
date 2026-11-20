{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibPrelude — Cubical.Foundations.Prelude (agda/cubical, pinned).
-- Pins the symbols QBP uses from the Prelude, with their types:
-- transport, transportRefl, subst, substRefl, J, JRefl, funExt, cong, _∙_,
-- Square, compPath-filler, isProp, isSet.
-- Used by QBP: all 13 proofs/agda-cubical/*.agda files (`open import Cubical.Foundations.Prelude`).
module LibPrelude where

open import Cubical.Foundations.Prelude

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

_ : A ≡ B → A → B
_ = transport

_ : (x : A) → transport refl x ≡ x
_ = transportRefl

_ : {x y : A} (P : A → Type ℓ') (p : x ≡ y) → P x → P y
_ = subst

-- (the library states substRefl with the family in the SAME universe as A)
substRefl' : {P : A → Type ℓ} {x : A} (u : P x) → subst P refl u ≡ u
substRefl' {P = P} u = substRefl {B = P} u

_ : {x : A} (P : (y : A) → x ≡ y → Type ℓ') (d : P x refl) {y : A} (p : x ≡ y) → P y p
_ = J

_ : {x : A} (P : (y : A) → x ≡ y → Type ℓ') (d : P x refl) → J P d refl ≡ d
_ = JRefl

-- the library's funExt and cong are the dependent (PathP) versions
_ : {P : A → I → Type ℓ'} {f : (x : A) → P x i0} {g : (x : A) → P x i1}
  → ((x : A) → PathP (P x) (f x) (g x)) → PathP (λ i → (x : A) → P x i) f g
_ = funExt

_ : {P : A → Type ℓ'} {x y : A} (f : (a : A) → P a) (p : x ≡ y)
  → PathP (λ i → P (p i)) (f x) (f y)
_ = cong

-- which specialise to the non-dependent statements QBP writes
funExt' : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funExt' = funExt

cong' : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong' f = cong f

_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_ = _∙_

_ : {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
_ = compPath-filler

_ : {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁) {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁) → Type _
_ = Square

_ : Type ℓ → Type ℓ
_ = isProp

_ : Type ℓ → Type ℓ
_ = isSet
