{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/Opaque — `opaque` blocks and `unfolding`.
--
-- Feature: `opaque` definitions do not unfold outside an `opaque unfolding`
-- block; inside one they do. This is the abstraction barrier the agda-prover
-- persona recommends for univalence-transported structures (the S³ μ of
-- QBPS3HSpace.agda), whose normalisation is super-exponential: an `opaque`
-- μ cannot be unfolded by accident. QBP currently achieves the same barrier
-- with module parameters (SubstrateCharge.agda `module SubstrateLink (H : HSpace …)`);
-- this file pins that the keyword itself is available and behaves as documented
-- (Agda ≥ 2.6.4).
--
-- Used by QBP: not yet (persona recommendation); candidate for the #579 files.
module Opaque where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Cubical.Path using (_≡_)

refl : {A : Set} {x : A} → x ≡ x
refl {x = x} = λ _ → x

opaque
  secret : Nat
  secret = 40 + 2

-- outside an unfolding block `secret` is a neutral constant; the only thing
-- provable about it without unfolding is what holds of any Nat
secret-is-itself : secret ≡ secret
secret-is-itself = refl

opaque
  unfolding secret

  -- inside, it computes
  secret-is-42 : secret ≡ 42
  secret-is-42 = refl

-- the unfolding result is usable outside (as a theorem, not by computation)
use-it : secret ≡ 42
use-it = secret-is-42
