{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibSusp — Cubical.HITs.Susp.
-- Pins: Susp, north, south, merid, SuspBool, SuspBool→S¹, S¹→SuspBool and
-- their two round-trips, S¹IsoSuspBool, toSusp; and the computation rule
-- CDLawsBool.agda is built on: SuspBool→S¹ (merid false i) ≡ loop i.
-- Used by QBP: CDJoinBR.agda, CDLawsBool.agda, CDAssocBool.agda, S3FromCD.agda,
-- CDAssocReduction.agda, CDAssocCubesStatus.agda, QuaternionicHopf.agda,
-- SubstrateCharge.agda, HopfNoAssoc.agda.
module LibSusp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed ; typ ; pt)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Bool using (Bool ; false)
open import Cubical.HITs.S1 using (S¹ ; base ; loop)
open import Cubical.HITs.Susp
  using (Susp ; north ; south ; merid ; SuspBool ; S¹IsoSuspBool ; toSusp
        ; SuspBool→S¹ ; S¹→SuspBool ; SuspBool→S¹→SuspBool ; S¹→SuspBool→S¹)
open import Cubical.Homotopy.Loopspace using (Ω)

private variable
  ℓ : Level
  A : Type ℓ

_ : Type ℓ → Type ℓ
_ = Susp

_ : Susp A
_ = north

_ : A → Path (Susp A) north south
_ = merid

_ : Type₀
_ = SuspBool

_ : SuspBool → S¹
_ = SuspBool→S¹

_ : S¹ → SuspBool
_ = S¹→SuspBool

_ : (x : SuspBool) → S¹→SuspBool (SuspBool→S¹ x) ≡ x
_ = SuspBool→S¹→SuspBool

_ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
_ = S¹→SuspBool→S¹

_ : Iso S¹ SuspBool
_ = S¹IsoSuspBool

_ : (A : Pointed ℓ) → typ A → typ (Ω (Susp (typ A) , north))
_ = toSusp

-- the meridian of `false` is the loop, definitionally
merid-false-is-loop : (λ i → SuspBool→S¹ (merid false i)) ≡ loop
merid-false-is-loop = refl
