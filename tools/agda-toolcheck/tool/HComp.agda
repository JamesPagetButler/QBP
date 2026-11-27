{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/HComp — homogeneous composition and filling.
--
-- Feature: `hcomp` with a partial system written as a pattern-matching
-- lambda on faces, `hfill` (via `Sub`/`inS`/`outS`), the definitional
-- reduction of hcomp when the system covers everything (φ = i1), and the
-- heterogeneous `comp`/`fill` from the builtin HCompU helpers.
--
-- Used by QBP: proofs/agda-cubical/HopfNoAssoc.agda (eight hcomp systems,
-- `hfill … (inS …)`), Diamond.agda (through the library's `_∙_`),
-- SubstrateCharge.agda (composition/groupoid laws).
module HComp where

open import Agda.Primitive using (Level)
open import Agda.Primitive.Cubical
  using (I; i0; i1; Partial)
  renaming (primHComp to hcomp; primComp to comp; primINeg to ~_
          ; primIMax to _∨_; primIMin to _∧_; itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Agda.Builtin.Cubical.HCompU using (module Helpers)

private variable
  ℓ : Level
  A : Set ℓ
  x y z : A

refl : x ≡ x
refl {x = x} = λ _ → x

-- path composition as an open box: left wall constant, right wall q, base p
_∙_ : x ≡ y → y ≡ z → x ≡ z
(p ∙ q) i = hcomp (λ j → λ { (i = i0) → p i0 ; (i = i1) → q j }) (p i)

-- at the endpoints the system is total (φ = i1), so hcomp REDUCES
∙-i0 : (p : x ≡ y) (q : y ≡ z) → (p ∙ q) i0 ≡ x
∙-i0 p q = refl

∙-i1 : (p : x ≡ y) (q : y ≡ z) → (p ∙ q) i1 ≡ z
∙-i1 p q = refl

-- homogeneous filling: the open box's interior, with the lid at i = i1
hfill : {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1 ; (i = i0) → outS u0 }) (outS u0)

-- the filler of the composite: a square with top p, bottom p ∙ q
∙-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
∙-filler p q j i = hfill (λ j → λ { (i = i0) → p i0 ; (i = i1) → q j }) (inS (p i)) j

-- the builtin heterogeneous fill agrees with its base at i0 (comp reduces at φ = i1)
fill-i0 : {P : I → Set ℓ} {φ : I} (u : ∀ i → Partial φ (P i)) (u0 : P i0 [ φ ↦ u i0 ])
        → Helpers.fill P u u0 i0 ≡ outS u0
fill-i0 u u0 = refl
