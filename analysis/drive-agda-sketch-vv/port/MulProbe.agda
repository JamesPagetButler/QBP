{-# OPTIONS --cubical --no-import-sorts --guardedness #-}
------------------------------------------------------------------------
-- WORK IN PROGRESS — the Cayley-Dickson μ on join S¹ S¹ (Buchholtz–Rijke's
-- core). NOT --safe and NOT complete: one hole by design. This file DOCUMENTS
-- how far the construction reduces — it is not claimed to type-check clean.
--
-- RESULT: the entire quaternion multiplication is reduced to ONE explicit
-- coherence square (μ on push×push). All 8 other cases (points + 1-cells)
-- type-check and are mutually consistent. The square is confirmed NON-trivial
-- (naive connection/hcomp fillers fail) — it is BR's irreducible 2-cell.
--
-- CAVEAT (honest): the corner formulas below respect the UNIT laws on corners
-- but are not verified to be the TRUE quaternion product; getting the corners
-- right (so the square fills) is itself part of BR's content.
------------------------------------------------------------------------
module MulProbe where
open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1 using (S¹ ; base ; loop ; _·_ ; invLooper)
open import Cubical.HITs.Join using (join ; inl ; inr ; push)

μ : join S¹ S¹ → join S¹ S¹ → join S¹ S¹
-- points (corners):
μ (inl x) (inl y)       = inl (x · y)
μ (inl x) (inr w)       = inr (x · w)
μ (inr v) (inl y)       = inr (v · invLooper y)
μ (inr v) (inr w)       = inl (invLooper (v · invLooper w))
-- 1-cells (second-arg push, first-arg push) — ALL type-check & cohere:
μ (inl x) (push b c j)  = push (x · b) (x · c) j
μ (inr v) (push b c j)  = sym (push (invLooper (v · invLooper c)) (v · invLooper b)) j
μ (push a b i) (inl y)  = push (a · y) (b · invLooper y) i
μ (push a b i) (inr w)  = sym (push (invLooper (b · invLooper w)) (a · w)) i
-- THE ONE REMAINING OBLIGATION — BR's irreducible coherence square.
-- Required boundary (confirmed from Agda):
--   i=0 : push (a · c) (a · d) k
--   i=1 : sym (push (invLooper (b · invLooper d)) (b · invLooper c)) k
--   k=0 : push (a · c) (b · invLooper c) i
--   k=1 : sym (push (invLooper (b · invLooper d)) (a · d)) i
-- corners (i,k): (inl(a·c), inr(a·d), inr(b·invLooper c), inl(invLooper(b·invLooper d)))
μ (push a b i) (push c d k) = {! BR coherence square — open !}
