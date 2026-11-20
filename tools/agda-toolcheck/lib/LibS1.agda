{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibS1 — Cubical.HITs.S1.
-- Pins: S¹, base, loop, _·_ (the circle multiplication CDLawsBool conjugates
-- along S¹IsoSuspBool), invLooper, rotInv-1, rotInv-2, isGroupoidS¹; and the
-- definitional left unit `base · z ≡ z` CDLawsBool.agda's header relies on.
-- Used by QBP: CDLawsBool.agda, CDAssocBool.agda, S3FromCD.agda.
module LibS1 where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.S1 using (S¹ ; base ; loop ; _·_ ; invLooper ; rotInv-1 ; rotInv-2 ; isGroupoidS¹)

_ : Type₀
_ = S¹

_ : base ≡ base
_ = loop

_ : S¹ → S¹ → S¹
_ = _·_

_ : S¹ → S¹
_ = invLooper

_ : (a b : S¹) → b · a · invLooper b ≡ a
_ = rotInv-1

_ : (a b : S¹) → invLooper b · a · b ≡ a
_ = rotInv-2

_ : isGroupoid S¹
_ = isGroupoidS¹

-- left unit is definitional on the library's `_·_`
·-unitˡ : (z : S¹) → base · z ≡ z
·-unitˡ z = refl

-- invLooper reverses the loop, definitionally
invLooper-loop : (λ i → invLooper (loop i)) ≡ sym loop
invLooper-loop = refl
