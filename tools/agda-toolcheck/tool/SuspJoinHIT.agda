{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/SuspJoinHIT — suspension and join as HITs.
--
-- Feature: a parameterised HIT with a point-indexed path constructor
-- (`merid : A → north ≡ south`), a HIT with a BINARY path constructor
-- (`push : (a : A) (b : B) → inl a ≡ inr b`), recursors by pattern matching
-- on `merid a i` / `push a b i`, their β-rules by refl, the iterated
-- suspension S³ = Susp (Susp (Susp 𝟚)) as a definitional unfolding, and the
-- map Susp Bool → S¹ that sends one meridian to the loop (the library's
-- `SuspBool→S¹`, on which CDLawsBool.agda's whole construction rests).
--
-- Used by QBP: proofs/agda/QBPSpheres.agda, QBPJoin.agda; through the library,
-- Diamond.agda / CDJoinBR.agda (`push`), CDLawsBool.agda (`merid false i ↦ loop i`).
module SuspJoinHIT where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Primitive.Cubical using (I; i0; i1)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Bool using (Bool; true; false)

private variable
  ℓ ℓ' ℓ'' : Level

refl : {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = λ _ → x

data Susp (A : Set ℓ) : Set ℓ where
  north south : Susp A
  merid : A → north ≡ south

data Join (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inl  : A → Join A B
  inr  : B → Join A B
  push : (a : A) (b : B) → inl a ≡ inr b

data S¹ : Set where
  base : S¹
  loop : base ≡ base

Susp-rec : {A : Set ℓ} {C : Set ℓ'} (n s : C) (m : A → n ≡ s) → Susp A → C
Susp-rec n s m north       = n
Susp-rec n s m south       = s
Susp-rec n s m (merid a i) = m a i

Susp-rec-merid : {A : Set ℓ} {C : Set ℓ'} (n s : C) (m : A → n ≡ s) (a : A)
               → (λ i → Susp-rec n s m (merid a i)) ≡ m a
Susp-rec-merid n s m a = refl

Join-rec : {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
           (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b)
         → Join A B → C
Join-rec l r p (inl a)      = l a
Join-rec l r p (inr b)      = r b
Join-rec l r p (push a b i) = p a b i

Join-rec-push : {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
                (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b)
                (a : A) (b : B)
              → (λ i → Join-rec l r p (push a b i)) ≡ p a b
Join-rec-push l r p a b = refl

-- the sphere tower by iterated suspension; S³ unfolds definitionally
S⁰ S¹s S² S³ : Set
S⁰  = Bool
S¹s = Susp S⁰
S²  = Susp S¹s
S³  = Susp S²

S³-is-Susp³ : S³ ≡ Susp (Susp (Susp Bool))
S³-is-Susp³ = refl

-- Susp Bool → S¹: one meridian becomes the loop, the other stays at base
SuspBool→S¹ : Susp Bool → S¹
SuspBool→S¹ north           = base
SuspBool→S¹ south           = base
SuspBool→S¹ (merid false i) = loop i
SuspBool→S¹ (merid true i)  = base

SuspBool→S¹-merid-false : (λ i → SuspBool→S¹ (merid false i)) ≡ loop
SuspBool→S¹-merid-false = refl
