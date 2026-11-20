{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/Interval — the interval I and its De Morgan algebra.
--
-- Feature: `I`, `i0`, `i1`, `~` (primINeg), `∧` (primIMin), `∨` (primIMax),
-- `Partial`, and the DEFINITIONAL De Morgan / absorption laws the checker
-- uses whenever it compares the boundary of a square. Every connection
-- square `λ i j → p (i ∧ j)` in QBP relies on exactly these laws.
--
-- Used by QBP: proofs/agda-cubical/Diamond.agda (orSquare/andSquare),
-- CDJoinBR.agda, HopfNoAssoc.agda (`merid a (~ k ∧ ~ j)`), SubstrateCharge.agda.
module Interval where

open import Agda.Primitive using (Level)
open import Agda.Primitive.Cubical
  using (I; i0; i1; Partial)
  renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_)
open import Agda.Builtin.Cubical.Path using (_≡_; PathP)

private variable
  ℓ : Level
  A : Set ℓ
  x y : A

refl : x ≡ x
refl {x = x} = λ _ → x

sym : x ≡ y → y ≡ x
sym p i = p (~ i)

-- negation is a definitional involution
sym-sym : (p : x ≡ y) → sym (sym p) ≡ p
sym-sym p = refl

-- absorption and unit laws are definitional
∧-i1 : (p : x ≡ y) → (λ i → p (i ∧ i1)) ≡ p
∧-i1 p = refl

∨-i0 : (p : x ≡ y) → (λ i → p (i ∨ i0)) ≡ p
∨-i0 p = refl

∧-i0 : (p : x ≡ y) → PathP (λ _ → x ≡ x) (λ i → p (i ∧ i0)) refl
∧-i0 p = refl

∨-i1 : (p : x ≡ y) → PathP (λ _ → y ≡ y) (λ i → p (i ∨ i1)) refl
∨-i1 p = refl

-- De Morgan: ~ (i ∧ j) = ~ i ∨ ~ j, definitionally. Both squares below have
-- the same boundary (top refl at y, bottom sym p) and are the same term.
deMorganˡ : (p : x ≡ y) → PathP (λ i → y ≡ p (~ i)) refl (sym p)
deMorganˡ p i j = p (~ (i ∧ j))

deMorganʳ : (p : x ≡ y) → PathP (λ i → y ≡ p (~ i)) refl (sym p)
deMorganʳ p i j = p (~ i ∨ ~ j)

deMorgan : (p : x ≡ y) → deMorganˡ p ≡ deMorganʳ p
deMorgan p = refl

-- connection squares: the boundary check needs i0 ∧ j = i0, i1 ∧ j = j, etc.
∧-connection : (p : x ≡ y) → PathP (λ i → x ≡ p i) refl p
∧-connection p i j = p (i ∧ j)

∨-connection : (p : x ≡ y) → PathP (λ i → p i ≡ y) p refl
∨-connection p i j = p (i ∨ j)

-- a partial element on the boundary ~ i ∨ i (the shape every hcomp system has)
-- (explicit binders: an extended lambda under a generalised `A` produces a
--  spurious `y.A !=< A` on Agda 2.8.0 — recorded in FEATURES.md)
boundary : {B : Set ℓ} {u v : B} (p : u ≡ v) (i : I) → Partial (~ i ∨ i) B
boundary p i = λ { (i = i0) → p i0 ; (i = i1) → p i1 }
