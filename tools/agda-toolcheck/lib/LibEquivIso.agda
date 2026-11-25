{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibEquivIso — Cubical.Foundations.Equiv and .Isomorphism.
-- Pins: _≃_, idEquiv, isPropIsEquiv, equivToIso; Iso (record with fun/inv/sec/ret),
-- isoToEquiv, invIso, compIso.
-- Used by QBP: QBPS3HSpace.agda, S3FromCD.agda, AssocTransport.agda, HopfNoAssoc.agda,
-- QuaternionicHopf.agda, CDAssocCubesStatus.agda, SkyrmionCharge.agda.
module LibEquivIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; isEquiv ; idEquiv ; isPropIsEquiv ; equivToIso)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; invIso ; compIso)

private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  B : Type ℓ'
  C : Type ℓ''

_ : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
_ = _≃_

_ : (A : Type ℓ) → A ≃ A
_ = idEquiv

_ : (f : A → B) → isProp (isEquiv f)
_ = isPropIsEquiv

_ : A ≃ B → Iso A B
_ = equivToIso

_ : Iso A B → A ≃ B
_ = isoToEquiv

_ : Iso A B → Iso B A
_ = invIso

_ : Iso A B → Iso B C → Iso A C
_ = compIso

-- the Iso record has the four fields the port projects
_ : (e : Iso A B) → A → B
_ = Iso.fun

_ : (e : Iso A B) → B → A
_ = Iso.inv
