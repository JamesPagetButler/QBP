{-# OPTIONS --cubical --safe --guardedness #-}
-- TOOLCHECK tool/Guardedness — `--guardedness` with `--safe`.
--
-- Feature: the flag the library tree carries (qbp-cubical.agda-lib and
-- agda/cubical's own cubical.agda-lib both pass `--guardedness`): coinductive
-- records defined by copatterns pass the (guarded) productivity check, and
-- their projections compute by refl. `--guardedness` is --safe-compatible
-- as long as `--sized-types` is off (it is).
--
-- Used by QBP: every proofs/agda-cubical/*.agda file carries the flag
-- (inherited from the library pin); no QBP file defines a coinductive type,
-- so this pins only that the flag combination is accepted and does what it says.
module Guardedness where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Cubical.Path using (_≡_)

refl : {A : Set} {x : A} → x ≡ x
refl {x = x} = λ _ → x

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

-- productive by guardedness (the recursive call is under a projection)
repeat : {A : Set} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

nats-from : Nat → Stream Nat
hd (nats-from n) = n
tl (nats-from n) = nats-from (suc n)

-- copattern definitions compute
repeat-hd : {A : Set} (a : A) → hd (repeat a) ≡ a
repeat-hd a = refl

repeat-tl : {A : Set} (a : A) → tl (repeat a) ≡ repeat a
repeat-tl a = refl

nats-from-tl-hd : (n : Nat) → hd (tl (nats-from n)) ≡ suc n
nats-from-tl-hd n = refl
