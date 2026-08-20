{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------
-- QBP substrate brick 4: the H-space interface + the precise S³ goal.
-- The quaternionic Hopf is completed by ONE thing (verified absent from the
-- cubical library): an H-space structure on S³ — the quaternion multiplication.
-- This brick formalises WHAT that is (the interface, matching the library's
-- HSpace), proves the interface is inhabited (sanity), and states the exact
-- typed goal `HSpace S³ north`. Constructing μ on S³ is Buchholtz–Rijke's
-- core theorem — the research-level remainder. Builtins only; machine-checked.
------------------------------------------------------------------------
module QBPHSpace where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import QBPSpheres using (Susp; north; S³)

private
  variable
    ℓ : Level

refl-path : {A : Set ℓ} {x : A} → x ≡ x
refl-path {x = x} = λ _ → x

-- H-space structure on a type A with unit e: a multiplication with two-sided unit.
-- (Matches the basic shape of Cubical.Homotopy.HSpace, which the general Hopf
--  construction is parameterised over.)
record HSpace {A : Set ℓ} (e : A) : Set ℓ where
  field
    μ        : A → A → A
    μ-unit-l : (a : A) → μ e a ≡ a
    μ-unit-r : (a : A) → μ a e ≡ a

-- Sanity: the interface is inhabited — the unit type 𝟙 is (trivially) an H-space.
-- (Confirms HSpace is usable, not vacuous.)
data 𝟙 : Set where ⋆ : 𝟙

𝟙-HSpace : HSpace ⋆
𝟙-HSpace = record { μ = λ _ _ → ⋆ ; μ-unit-l = lemma ; μ-unit-r = lemma }
  where
    lemma : (a : 𝟙) → ⋆ ≡ a
    lemma ⋆ = refl-path

------------------------------------------------------------------------
-- THE GOAL (Buchholtz–Rijke core theorem; NOT in the cubical library):
--
--     S³-HSpace : HSpace {A = S³} north
--
-- i.e. the quaternion multiplication μ : S³ → S³ → S³ with the pole `north` as
-- unit. Constructing μ respecting the suspension cell structure (and the
-- associativity / equivalence / connectedness the Hopf construction additionally
-- needs) is the research-level remainder. Once it exists, the library's general
-- `Hopf` module (parameterised by an H-space) yields the quaternionic fibration
--     S³ → (S³ * S³) → S⁴
-- for free (brick 3 already built the total space S³*S³).
--
-- It is left as the stated goal rather than a stub: under --safe a partial proof
-- would not type-check, so we do not fake it.
------------------------------------------------------------------------
