{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/PathP — paths as maps out of the interval.
--
-- Feature: `PathP` (dependent paths), `_≡_` as PathP over a constant family,
-- function extensionality and `cong` as λ-manipulations (not axioms),
-- dependent `cong`, componentwise paths in Σ, and `Square` as a PathP of paths.
--
-- Used by QBP: proofs/agda/QBPSubstrate.agda (funext/happly/cong-path),
-- proofs/agda-cubical/Diamond.agda (Square), CDAssocReduction.agda,
-- CDAssocCubesStatus.agda (PathP of PathP), QuaternionicHopf.agda.
module PathP where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Primitive.Cubical using (I; i0; i1) renaming (primIMax to _∨_)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

private variable
  ℓ ℓ' : Level
  A : Set ℓ
  B : Set ℓ'
  x y : A

refl : x ≡ x
refl {x = x} = λ _ → x

-- _≡_ is PathP over the constant family, definitionally
≡→PathP : x ≡ y → PathP (λ _ → A) x y
≡→PathP p = p

PathP→≡ : PathP (λ _ → A) x y → x ≡ y
PathP→≡ p = p

-- function extensionality is a λ-swap
funExt : {P : A → Set ℓ'} {f g : (a : A) → P a} → ((a : A) → f a ≡ g a) → f ≡ g
funExt p i a = p a i

happly : {P : A → Set ℓ'} {f g : (a : A) → P a} → f ≡ g → (a : A) → f a ≡ g a
happly q a i = q i a

funExt-β : {P : A → Set ℓ'} {f g : (a : A) → P a} (p : (a : A) → f a ≡ g a)
         → happly (funExt p) ≡ p
funExt-β p = refl

funExt-η : {P : A → Set ℓ'} {f g : (a : A) → P a} (q : f ≡ g)
         → funExt (happly q) ≡ q
funExt-η q = refl

-- cong is computation, not an axiom
cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f p i = f (p i)

-- dependent cong over a line of types
congP : {P Q : I → Set ℓ} (f : (i : I) → P i → Q i) {u : P i0} {v : P i1}
      → PathP P u v → PathP Q (f i0 u) (f i1 v)
congP f p i = f i (p i)

-- a path in a Σ-type is a path in the base and a dependent path over it
-- (explicit binders: with generalised x y the Σ-constructor's implicit family
--  is left unsolved on Agda 2.8.0 — recorded in FEATURES.md)
ΣPathP : {X : Set ℓ} {P : X → Set ℓ'} {a b : X} {u : P a} {v : P b}
       → (p : a ≡ b) → PathP (λ i → P (p i)) u v
       → _≡_ {A = Σ X P} (a , u) (b , v)
ΣPathP p q i = p i , q i

-- a square is a PathP of paths; the ∧-connection fills one
Square : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
       → a₀₀ ≡ a₀₁ → a₁₀ ≡ a₁₁ → a₀₀ ≡ a₁₀ → a₀₁ ≡ a₁₁ → Set _
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

-- Diamond.agda's `orSquare`: top = left = p, bottom = right = refl
orSquare : (p : x ≡ y) → Square p refl p refl
orSquare p j k = p (j ∨ k)
