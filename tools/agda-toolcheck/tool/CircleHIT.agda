{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/CircleHIT — a higher inductive type with a path constructor.
--
-- Feature: `data S¹` with `loop : base ≡ base`; pattern matching on the path
-- constructor (`loop i`) in the recursor and in the DEPENDENT eliminator
-- (whose loop case is a PathP); the β-rules on both constructors hold by refl;
-- a non-trivial map (`reverse`, loop ↦ sym loop) and its involutivity.
--
-- Used by QBP: proofs/agda/QBPSubstrate.agda (S¹-rec + β-rules), and every
-- library file through Cubical.HITs.S1 (CDLawsBool.agda, CDAssocBool.agda).
module CircleHIT where

open import Agda.Primitive using (Level)
open import Agda.Primitive.Cubical using (I; i0; i1) renaming (primINeg to ~_)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)

private variable
  ℓ : Level

refl : {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

data S¹ : Set where
  base : S¹
  loop : base ≡ base

-- recursor: pattern matching on the path constructor
S¹-rec : {C : Set ℓ} (b : C) (l : b ≡ b) → S¹ → C
S¹-rec b l base     = b
S¹-rec b l (loop i) = l i

-- dependent eliminator: the loop case is a dependent path
S¹-ind : (P : S¹ → Set ℓ) (b : P base) (l : PathP (λ i → P (loop i)) b b)
       → (s : S¹) → P s
S¹-ind P b l base     = b
S¹-ind P b l (loop i) = l i

-- β-rules, including on the path constructor, hold definitionally
S¹-rec-base : {C : Set ℓ} (b : C) (l : b ≡ b) → S¹-rec b l base ≡ b
S¹-rec-base b l = refl

S¹-rec-loop : {C : Set ℓ} (b : C) (l : b ≡ b) → (λ i → S¹-rec b l (loop i)) ≡ l
S¹-rec-loop b l = refl

S¹-ind-loop : (P : S¹ → Set ℓ) (b : P base) (l : PathP (λ i → P (loop i)) b b)
            → (λ i → S¹-ind P b l (loop i)) ≡ l
S¹-ind-loop P b l = refl

-- a genuine map: reverse the loop
reverse : S¹ → S¹
reverse base     = base
reverse (loop i) = loop (~ i)

reverse-reverse : (s : S¹) → reverse (reverse s) ≡ s
reverse-reverse base     = refl
reverse-reverse (loop i) = refl
