{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/CoreSyntax — the ordinary Agda surface QBP's files lean on.
--
-- Feature: generalisable `variable` blocks, `private`, anonymous parameterised
-- modules (`module _ (…) where`), named module instantiation, `where` blocks,
-- `renaming` on import, records with fields and copattern definitions,
-- mixfix operators with fixity declarations, universe polymorphism
-- (`Level`, `lsuc`, `_⊔_`), Σ from the builtins, pattern-matching lambdas,
-- and Unicode identifiers (μ, ⊗, ₗ, ᵣ) as the library convention uses them.
--
-- Used by QBP: all files (Diamond.agda `module _ {A} {B} where`, CDJoinBR.agda
-- `record CDLaws`, SubstrateCharge.agda `module SubstrateLink (H : HSpace …)`,
-- CDLawsBool.agda `_⊗Bool_`, S3FromCD.agda / QBPS3HSpace.agda).
module CoreSyntax where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+ℕ_)

private variable
  ℓ ℓ' : Level
  A : Set ℓ

refl : {x : A} → x ≡ x
refl {x = x} = λ _ → x

-- a record with fields, in the shape of the library's HSpace
record HSpace {A : Set ℓ} (e : A) : Set ℓ where
  field
    μ  : A → A → A
    μₗ : (x : A) → μ e x ≡ x
    μᵣ : (x : A) → μ x e ≡ x

-- an anonymous parameterised module, as in Diamond.agda and SubstrateCharge.agda
module _ {A : Set ℓ} {e : A} (H : HSpace e) where
  open HSpace H

  infixl 30 _⊗_
  _⊗_ : A → A → A
  _⊗_ = μ

  ⊗-unitˡ : (x : A) → e ⊗ x ≡ x
  ⊗-unitˡ = μₗ

-- Nat is an H-space with unit 0; the record is built by copatterns
NatHSpace : HSpace 0
HSpace.μ  NatHSpace = _+ℕ_
HSpace.μₗ NatHSpace x = refl
HSpace.μᵣ NatHSpace = +ℕ-zero
  where
    cong-suc : {m n : Nat} → m ≡ n → suc m ≡ suc n
    cong-suc p i = suc (p i)
    +ℕ-zero : (n : Nat) → n +ℕ 0 ≡ n
    +ℕ-zero zero    = refl
    +ℕ-zero (suc n) = cong-suc (+ℕ-zero n)

-- named module instantiation
module NatH = HSpace NatHSpace

three : Nat
three = NatH.μ 1 2

-- universe polymorphism: a pointed type at any level, and its lifting
Pointed : (ℓ : Level) → Set (lsuc ℓ)
Pointed ℓ = Σ (Set ℓ) (λ X → X)

pointed-pair : Pointed ℓ → Pointed ℓ' → Pointed (ℓ ⊔ ℓ')
pointed-pair (X , x) (Y , y) = (Σ X (λ _ → Y)) , (x , y)

-- pattern-matching lambda and Σ projections
swap : {X : Set ℓ} {Y : Set ℓ'} → Σ X (λ _ → Y) → Σ Y (λ _ → X)
swap = λ { (x , y) → y , x }

swap-swap : {X : Set ℓ} {Y : Set ℓ'} (p : Σ X (λ _ → Y)) → swap (swap p) ≡ p
swap-swap p = refl
