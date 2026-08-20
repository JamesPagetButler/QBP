{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------
-- QBP substrate brick 2: the sphere tower via suspension (S⁰..S³).
-- The Buchholtz–Rijke CD-in-HoTT tower lives on these spheres; S³ is the
-- ℍ-level sphere (the H-space whose Hopf construction gives the quaternionic
-- Hopf fibration). Builtins only (no cubical library) so CI stays light.
-- Every claim below is machine-checked (refl under --safe = genuine, not asserted).
------------------------------------------------------------------------
module QBPSpheres where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Cubical.Path using (_≡_)

private
  variable
    ℓ ℓ′ : Level

refl-path : {A : Set ℓ} {x : A} → x ≡ x
refl-path {x = x} = λ _ → x

-- Suspension as a Higher Inductive Type: two poles + a meridian path for each point of A.
data Susp (A : Set ℓ) : Set ℓ where
  north : Susp A
  south : Susp A
  merid : A → north ≡ south

-- two-point type for S⁰.
data 𝟚 : Set where
  ⊙ ⊗ : 𝟚

-- the sphere tower.
S⁰ S¹ S² S³ : Set
S⁰ = 𝟚
S¹ = Susp S⁰
S² = Susp S¹
S³ = Susp S²          -- the ℍ-level sphere

-- the (non-dependent) suspension recursor.
Susp-rec : {A : Set ℓ} {C : Set ℓ′} (n s : C) (m : A → n ≡ s) → Susp A → C
Susp-rec n s m north       = n
Susp-rec n s m south       = s
Susp-rec n s m (merid a i) = m a i

------------------------------------------------------------------------
-- VERIFICATION: Susp is a genuine HIT — its recursor computes on all three
-- constructors (β-rules, machine-checked). This is what makes S³ real.
------------------------------------------------------------------------

Susp-rec-north : {A : Set ℓ} {C : Set ℓ′} (n s : C) (m : A → n ≡ s)
              → Susp-rec n s m north ≡ n
Susp-rec-north n s m = refl-path

Susp-rec-south : {A : Set ℓ} {C : Set ℓ′} (n s : C) (m : A → n ≡ s)
              → Susp-rec n s m south ≡ s
Susp-rec-south n s m = refl-path

-- the PATH-constructor β-rule: the recursor sends each meridian to m a (the
-- genuinely-higher computation rule that only a real HIT satisfies).
Susp-rec-merid : {A : Set ℓ} {C : Set ℓ′} (n s : C) (m : A → n ≡ s) (a : A)
              → (λ i → Susp-rec n s m (merid a i)) ≡ m a
Susp-rec-merid n s m a = refl-path

-- S³ is definitionally the iterated suspension of 𝟚 (the cell structure is real).
S³-is-Susp³ : S³ ≡ Susp (Susp (Susp 𝟚))
S³-is-Susp³ = refl-path
