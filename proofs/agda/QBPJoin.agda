{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------
-- QBP substrate brick 3: the join (the Hopf total space).
-- The quaternionic Hopf fibration is  S³ → (S³ * S³) → S⁴,  where the total
-- space S³ * S³ is the JOIN and S⁴ = Susp S³. This brick builds the join HIT
-- and names the concrete total space `S³*S³`. Builtins only; machine-checked.
--
-- SCOPE (honest): with S³ (brick 2) + this join, the ONLY remaining piece of
-- the quaternionic Hopf is the S³ H-SPACE (the quaternion multiplication on
-- S³) — Buchholtz–Rijke's core theorem, which is NOT in the cubical library
-- (the library's general `Hopf` module is parameterised by an H-space and is
-- instantiated only at S¹). Once the S³ H-space exists, that module yields the
-- fibration for free. So the quaternionic Hopf is localised to one hard brick.
------------------------------------------------------------------------
module QBPJoin where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import QBPSpheres using (S³)

private
  variable
    ℓ ℓ′ ℓ″ : Level

refl-path : {A : Set ℓ} {x : A} → x ≡ x
refl-path {x = x} = λ _ → x

-- the join A * B as a HIT: a copy of A, a copy of B, and a path joining every
-- a∈A to every b∈B.
data Join (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  inl  : A → Join A B
  inr  : B → Join A B
  push : (a : A) (b : B) → inl a ≡ inr b

-- the concrete Hopf total space.
S³*S³ : Set
S³*S³ = Join S³ S³

-- the (non-dependent) join recursor.
Join-rec : {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
           (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b)
         → Join A B → C
Join-rec l r p (inl a)      = l a
Join-rec l r p (inr b)      = r b
Join-rec l r p (push a b i) = p a b i

------------------------------------------------------------------------
-- VERIFICATION: Join is a genuine HIT — recursor β-rules on inl/inr/push.
------------------------------------------------------------------------

Join-rec-inl : {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
               (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b) (a : A)
             → Join-rec l r p (inl a) ≡ l a
Join-rec-inl l r p a = refl-path

Join-rec-inr : {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
               (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b) (b : B)
             → Join-rec l r p (inr b) ≡ r b
Join-rec-inr l r p b = refl-path

-- the PATH-constructor β-rule (the genuine HIT computation rule).
Join-rec-push : {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″}
                (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b)
                (a : A) (b : B)
              → (λ i → Join-rec l r p (push a b i)) ≡ p a b
Join-rec-push l r p a b = refl-path
