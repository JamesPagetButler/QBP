{-# OPTIONS --cubical --no-import-sorts --guardedness #-}
------------------------------------------------------------------------
-- INTERACTIVE SCAFFOLD for BR's core 2-cell — the pushMul (push,push) square
-- that is the sole remaining hole of the Cayley–Dickson join-step (CDJoin.agda).
-- Goal: a filler for the twisted square, with the four faces wired and every
-- remaining obligation NAMED (with an explicit type) so it can be closed
-- goal-by-goal in an interactive Agda session.
------------------------------------------------------------------------
module SquareScaffold where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv ; invEq ; secEq ; retEq ; _≃_)
open import Cubical.HITs.Join using (join ; inl ; inr ; push)
open import Cubical.HITs.Join.Properties using (join-commFun)

private variable ℓ : Level

module Scaffold {A : Type ℓ}
  (_·_  : A → A → A)
  (conj : A → A)
  (neg  : A → A)
  -- the invertibility the filler needs (from CDStr.⊗-isEquivˡ):
  (·-isEquivˡ : (a : A) → isEquiv (a ·_))
  where

  JA : Type ℓ
  JA = join A A

  ------------------------------------------------------------------
  -- TOOLS (ready to hand — these type-check; a closer draws from them).
  ------------------------------------------------------------------
  -- left-multiplication as an equivalence, with its section/retraction:
  Rᵉ : (a : A) → A ≃ A
  Rᵉ a = (a ·_) , ·-isEquivˡ a
  Rsec : (a : A) (y : A) → a · (invEq (Rᵉ a) y) ≡ y
  Rsec a = secEq (Rᵉ a)
  Rret : (a : A) (x : A) → invEq (Rᵉ a) (a · x) ≡ x
  Rret a = retEq (Rᵉ a)

  ------------------------------------------------------------------
  -- THE GOAL — a filler for the twisted square. Four faces wired.
  ------------------------------------------------------------------
  square : (a b x y : A) →
    Square
      (λ k → push (a · x) (b · conj x) k)                    -- j=0 : inl(a·x)⟶inr(b·conj x)
      (λ k → sym (push (neg (b · conj y)) (a · y)) k)        -- j=1 : inr(a·y)⟶inl(neg(b·conj y))
      (λ j → push (a · x) (a · y) j)                         -- k=0 : inl(a·x)⟶inr(a·y)  [diagonal]
      (λ j → sym (push (neg (b · conj y)) (b · conj x)) j)   -- k=1 : inr(b·conj x)⟶inl(neg(b·conj y)) [swap-twist]

  -- OBLIGATION-1 (interior seed square). A degenerate "base" square the outer
  -- hcomp contracts onto — its own boundary is a fillable seed.  TYPE below.
  seed : (a b x y : A) →
    Square
      (λ k → push (a · x) (b · conj x) k)
      (λ k → sym (push (neg (b · conj y)) (a · y)) k)
      (λ j → push (a · x) (a · y) j)
      (λ j → sym (push (neg (b · conj y)) (b · conj x)) j)
  seed a b x y = {! SEED — build via Rsec/Rret morphing the diagonal edge (Hopf §93-122) !}

  -- The filler = the seed (this indirection lets the seed be attacked in isolation;
  -- once `seed` is closed, `square = seed` and the CDJoin hole closes).
  square a b x y = seed a b x y

------------------------------------------------------------------------
-- HOW TO CLOSE THIS SCAFFOLD (the interactive entry point for #578)
--
-- One typed obligation remains: `seed` (line ~57). Load this file in an Agda
-- editor (C-c C-l); the hole shows the Square goal with all four faces in scope.
--
-- RECOMMENDED FILLER (nested hcomp, mirroring Cubical.Homotopy.Hopf §93-122):
--
--   seed a b x y j k =
--     hcomp (λ l → λ
--       { (k = i0) → push (a · x) (a · y) j                    -- diagonal edge (fixed)
--       ; (k = i1) → sym (push (neg (b · conj y)) (b · conj x)) j
--       ; (j = i0) → << morph inl(a·x)⟶inr(b·conj x) via Rsec/Rret >>  -- HOLE m₀₋
--       ; (j = i1) → << morph inr(a·y)⟶inl(neg(b·conj y)) >>          -- HOLE m₁₋
--       })
--       (<< inner seed: contract using Rret (a·x) etc. >>)               -- HOLE base
--
--   The l-tube must agree with the base at l=i0 and reach the four faces at l=i1.
--   The morphs use  Rsec/Rret  (the section/retraction of (a·_)) exactly as the
--   Hopf section proof uses secEq/retEq of μ-eq'.
--
-- OBLIGATION MENU (the S¹-level tools, when A = S¹ at the S¹→S³ step):
--   · conj := invLooper   (Cubical.HITs.S1.Base)
--   · the S¹ cancellation lemmas  rotInv-2 / rotInv-3 / rotInv-4  discharge the
--     morph coherences (their faces match: invLooper (b · invLooper a) · b ≡ a).
--   · neg comes from the Bool→S¹ CD-join step (never defined on S¹ directly).
--
-- DEFINITIONAL (already free — no work): the k=0/k=1 faces ARE the joinMap
-- diagonal / join-commFun swap-twist edges by computation; only the interior
-- 2-cell (this seed) is content.
--
-- Once `seed` type-checks with zero holes: copy it into CDJoin.agda's
-- `pushMul a b (push x y j) k` case → the CD-join step is complete → instantiate
-- CDStr Bool → S¹ → S³ → feed S³-HSpace-from-join → the S³ H-space port is done.
------------------------------------------------------------------------
