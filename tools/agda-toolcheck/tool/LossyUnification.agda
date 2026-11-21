{-# OPTIONS --cubical --safe --lossy-unification #-}
-- TOOLCHECK tool/LossyUnification — `--lossy-unification` under `--safe`.
--
-- Feature: the flag SkyrmionCharge.agda needs (and that the library's
-- Cubical.Homotopy.Group.Base / PinSn themselves carry). It makes the
-- unifier compare applications of the same head argument-wise first
-- ("first-order unification, lossy"), which is what keeps the concrete-index
-- πₙ'Sⁿ≅ℤ statements from normalising the whole iso. The flag does not
-- affect what is PROVABLE (it can only make the checker reject more), so it
-- is --safe-compatible; this file pins that the combination is accepted and
-- that an ordinary higher-order unification problem still solves under it.
--
-- Used by QBP: proofs/agda-cubical/SkyrmionCharge.agda (file pragma).
module LossyUnification where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

private variable
  ℓ : Level
  A B : Set ℓ

refl : {x : A} → x ≡ x
refl {x = x} = λ _ → x

cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f p i = f (p i)

-- the unifier must solve `f := suc` from `f (n + 0) ≡ suc (n + 0)`
-- (argument-wise first-order step, then the body)
+-zero : (n : Nat) → n + 0 ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)
