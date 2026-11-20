{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/Transp — transport from the `transp` primitive.
--
-- Feature: `transp` (the constructive replacement for J): `transport`,
-- `transportRefl` (transp with φ = i1 is the identity, definitionally),
-- the transport filler, `subst`, and J + its computation rule JRefl.
--
-- Used by QBP: every library-dependent file (transport/subst/J are the
-- port's whole discipline: QBPS3HSpace.agda `subst HSpace (ua∙ e p)`,
-- AssocTransport.agda `J … substRefl`, Diamond.agda `J`/`JRefl`,
-- SubstrateCharge.agda, SkyrmionCharge.agda).
module Transp where

open import Agda.Primitive using (Level)
open import Agda.Primitive.Cubical
  using (I; i0; i1)
  renaming (primTransp to transp; primINeg to ~_; primIMin to _∧_)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)
open import Agda.Builtin.Bool using (Bool; true; false)

private variable
  ℓ ℓ' : Level
  A B : Set ℓ
  x y : A

refl : x ≡ x
refl {x = x} = λ _ → x

transport : A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

-- transp over a constant family with φ = i1 is definitionally the identity;
-- varying φ from i0 to i1 is the proof that transport along refl is the identity
transportRefl : (a : A) → transport refl a ≡ a
transportRefl {A = A} a i = transp (λ _ → A) i a

transp-i1 : (a : A) → transp (λ _ → A) i1 a ≡ a
transp-i1 a = refl

-- the filler: a dependent path from a to its transport
transport-filler : (p : A ≡ B) (a : A) → PathP (λ i → p i) a (transport p a)
transport-filler p a i = transp (λ j → p (i ∧ j)) (~ i) a

subst : (P : A → Set ℓ') (p : x ≡ y) → P x → P y
subst P p u = transport (λ i → P (p i)) u

substRefl : (P : A → Set ℓ') (u : P x) → subst P refl u ≡ u
substRefl P u = transportRefl u

-- path induction, computed by transport along the singleton contraction
J : {x : A} (P : (y : A) → x ≡ y → Set ℓ') (d : P x refl)
  → {y : A} (p : x ≡ y) → P y p
J P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

JRefl : {x : A} (P : (y : A) → x ≡ y → Set ℓ') (d : P x refl) → J P d refl ≡ d
JRefl P d = transportRefl d

-- a concrete computation: transporting a Bool along the constant path
transport-Bool : (b : Bool) → transport (λ _ → Bool) b ≡ b
transport-Bool = transportRefl
