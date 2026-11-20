{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibLoopspace — Cubical.Homotopy.Loopspace.
-- Pins: Ω (the loop space of a pointed type) and Ω→ (the induced pointed map on
-- loop spaces), as used by SubstrateCharge.agda's Eckmann–Hilton step.
-- Used by QBP: SubstrateCharge.agda (`using (Ω→)`).
module LibLoopspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed ; _→∙_)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)

private variable
  ℓ ℓ' : Level

_ : Pointed ℓ → Pointed ℓ
_ = Ω

_ : {A : Pointed ℓ} {B : Pointed ℓ'} → (A →∙ B) → (Ω A →∙ Ω B)
_ = Ω→
