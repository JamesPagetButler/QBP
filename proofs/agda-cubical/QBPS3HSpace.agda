{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
------------------------------------------------------------------------
-- Porting Buchholtz–Rijke (arXiv:1610.01134), "The Cayley-Dickson
-- Construction in HoTT": the H-space structure on S³, into Cubical Agda,
-- against the verified cubical library, fully --safe (no postulates).
--
-- BR build the quaternion multiplication on the JOIN S¹ * S¹ and carry it to
-- S³ via S³ ≃ join S¹ S¹. We make that argument machine-checked:
--   (1) HSpace≃   : an H-space transports across a pointed equivalence.
--   (2) the library's pointed equivalence  join S¹ S¹ ≃ S³  (IsoSphereJoin).
--   (3) S³-HSpace-from-join : HSpace (join∙ S¹ S¹) → HSpace (S₊∙ 3).
-- This REDUCES the entire port to exactly one obligation — the Cayley-Dickson
-- multiplication HSpace (join∙ S¹ S¹) — which is BR's core (see §end).
------------------------------------------------------------------------
module QBPS3HSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv ; Iso)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Base using (ua∙)
open import Cubical.Homotopy.HSpace using (HSpace)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.Join using (join ; join∙)
open import Cubical.HITs.Sn.Multiplication using (IsoSphereJoin ; IsoSphereJoinPres∙)

private variable ℓ : Level

-- (1) GENERAL TRANSPORT (fully proven): an H-space carries across a pointed
-- equivalence, via pointed univalence (ua∙) + subst.
HSpace≃ : {A B : Pointed ℓ}
        → (e : fst A ≃ fst B) (p : fst e (pt A) ≡ pt B)
        → HSpace A → HSpace B
HSpace≃ e p = subst HSpace (ua∙ e p)

-- (2)+(3) THE REDUCTION (fully proven): the library's pointed equivalence
-- join S¹ S¹ ≃ S³ (IsoSphereJoin 1 1, basepoint-preserving by IsoSphereJoinPres∙)
-- carries any H-space on the join to one on S³.
S³-HSpace-from-join : HSpace (join∙ (S₊∙ 1) (S₊∙ 1)) → HSpace (S₊∙ 3)
S³-HSpace-from-join =
  HSpace≃ (isoToEquiv (IsoSphereJoin 1 1)) (IsoSphereJoinPres∙ 1 1)

-- The obligation HSpace (join∙ (S₊∙ 1) (S₊∙ 1)) — Buchholtz–Rijke's core,
-- the Cayley-Dickson (quaternion) multiplication on the join — is DISCHARGED
-- in this directory: Diamond.agda → CDJoinBR.agda → CDLawsBool.agda →
-- S3FromCD.agda, whose S³-HSpace : HSpace (S₊∙ 3) is the theorem.
------------------------------------------------------------------------
