{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibJoin — Cubical.HITs.Join.
-- Pins: join, inl, inr, push (binary path constructor), join∙, Iso→joinIso,
-- and that `push a b` is a path from `inl a` to `inr b` (Diamond.agda's whole
-- geometry is squares of pushes).
-- Used by QBP: Diamond.agda, CDJoinBR.agda, CDLawsBool.agda, QBPS3HSpace.agda,
-- S3FromCD.agda, CDAssocReduction.agda, CDAssocBool.agda, CDAssocCubesStatus.agda,
-- QuaternionicHopf.agda, HopfNoAssoc.agda.
module LibJoin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.HITs.Join using (join ; inl ; inr ; push ; join∙ ; Iso→joinIso)

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  A : Type ℓ
  B : Type ℓ'
  C : Type ℓ''
  D : Type ℓ'''

_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
_ = join

_ : A → join A B
_ = inl

_ : B → join A B
_ = inr

_ : (a : A) (b : B) → Path (join A B) (inl a) (inr b)
_ = push

_ : Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
_ = join∙

_ : Iso A C → Iso B D → Iso (join A B) (join C D)
_ = Iso→joinIso

-- the recursor by pattern matching on the library's HIT (what CDJoinBR's cd-mul does)
join-rec : (l : A → C) (r : B → C) (p : (a : A) (b : B) → l a ≡ r b) → join A B → C
join-rec l r p (inl a) = l a
join-rec l r p (inr b) = r b
join-rec l r p (push a b i) = p a b i
