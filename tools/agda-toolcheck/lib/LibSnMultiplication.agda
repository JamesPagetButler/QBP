{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibSnMultiplication — Cubical.HITs.Sn.Multiplication.
-- Pins: IsoSphereJoin : Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m))) and
-- IsoSphereJoinPres∙ (basepoint preservation, by refl in the library). The
-- #575 reduction S³-HSpace-from-join transports along IsoSphereJoin 1 1
-- (join S¹ S¹ ≃ S³) and QuaternionicHopf uses IsoSphereJoin 3 3 (S³ * S³ ≃ S⁷).
-- Used by QBP: QBPS3HSpace.agda, QuaternionicHopf.agda, CDAssocCubesStatus.agda.
module LibSnMultiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.HITs.Join using (join ; inl)
open import Cubical.HITs.Sn using (S₊ ; ptSn)
open import Cubical.HITs.Sn.Multiplication using (IsoSphereJoin ; IsoSphereJoinPres∙)

_ : (n m : ℕ) → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
_ = IsoSphereJoin

_ : (n m : ℕ) → Iso.fun (IsoSphereJoin n m) (inl (ptSn n)) ≡ ptSn (suc (n + m))
_ = IsoSphereJoinPres∙

-- the two instances the port uses, at their concrete indices (types only; no
-- normalisation of the iso is forced by stating them)
join-S¹-S¹≅S³ : Iso (join (S₊ 1) (S₊ 1)) (S₊ 3)
join-S¹-S¹≅S³ = IsoSphereJoin 1 1

join-S³-S³≅S⁷ : Iso (join (S₊ 3) (S₊ 3)) (S₊ 7)
join-S³-S³≅S⁷ = IsoSphereJoin 3 3
