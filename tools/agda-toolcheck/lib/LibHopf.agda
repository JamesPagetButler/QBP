{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibHopf — Cubical.Homotopy.Hopf.
-- Pins the library's generic Hopf construction, `module Hopf {A} {e : HSpace A}
-- (e-ass : AssocHSpace e) (conA : (x y : typ A) → ∥ x ≡ y ∥₁)`, with the
-- symbols QBP instantiates: Hopf : Susp (typ A) → Type ℓ (the fibration), its
-- north fibre being the carrier (by refl), TotalSpaceHopfPush, joinIso₁,
-- TotalHopf. Instantiated here at a GENERIC pointed H-space, so nothing is
-- normalised — the same discipline as QuaternionicHopf.agda's `module WithAssoc`.
-- The e-ass parameter is exactly the associativity the pinned library demands
-- and that HopfNoAssoc.agda shows is unused by the assoc-free half.
-- Used by QBP: QuaternionicHopf.agda (`open import Cubical.Homotopy.Hopf using (module Hopf)`).
module LibHopf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed ; typ ; pt)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Join using (join)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Homotopy.HSpace using (HSpace ; AssocHSpace)
open import Cubical.Homotopy.Hopf using (module Hopf)

module _ {ℓ : Level} {A : Pointed ℓ} {e : HSpace A}
         (e-ass : AssocHSpace e) (conA : (x y : typ A) → ∥ x ≡ y ∥₁) where

  open Hopf e-ass conA

  _ : Susp (typ A) → Type ℓ
  _ = Hopf

  -- the fibre over the north pole is the H-space's carrier, definitionally
  Hopf-north : Hopf north ≡ typ A
  Hopf-north = refl

  _ : Type ℓ
  _ = TotalSpaceHopfPush

  _ : Iso TotalSpaceHopfPush (join (typ A) (typ A))
  _ = joinIso₁
