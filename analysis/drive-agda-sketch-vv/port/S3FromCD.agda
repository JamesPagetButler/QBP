{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #578 AC3: the final wiring — from the concrete Cayley-Dickson H-space
-- on join (Susp Bool) (Susp Bool) (CDLawsBool.agda) to the H-space on S³.
--
--   HSpace (join SuspBool SuspBool , inl north)      [CDLawsBool]
--     → HSpace (join∙ (S₊∙ 1) (S₊∙ 1))               [Iso→joinIso both sides
--                                                      of S¹IsoSuspBool + HSpace≃]
--     → HSpace (S₊∙ 3)                               [IsoSphereJoin 1 1]
--
-- HSpace≃ / S³-HSpace-from-join are restated verbatim from
-- proofs/agda-cubical/QBPS3HSpace.agda (CI-green); the port-dir copy keeps
-- this directory self-contained until the AC6 consolidation moves the
-- finished chain into proofs/agda-cubical/.
--
-- This completes the Buchholtz–Rijke port: S³ is an H-space, --safe,
-- 0 postulates, machine-checked end to end.

module S3FromCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; invIso)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Base using (ua∙)
open import Cubical.Homotopy.HSpace using (HSpace)
open import Cubical.Data.Bool using (Bool)
open import Cubical.HITs.S1 using (S¹ ; base)
open import Cubical.HITs.Susp using (SuspBool ; S¹IsoSuspBool)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.Join using (join ; inl ; join∙ ; Iso→joinIso)
open import Cubical.HITs.Sn.Multiplication
  using (IsoSphereJoin ; IsoSphereJoinPres∙)

open import CDLawsBool using (JoinSuspBool-HSpace)

private variable ℓ : Level

-- (restated from QBPS3HSpace.agda) an H-space carries across a pointed
-- equivalence, via pointed univalence + subst
HSpace≃ : {A B : Pointed ℓ}
        → (e : fst A ≃ fst B) (p : fst e (pt A) ≡ pt B)
        → HSpace A → HSpace B
HSpace≃ e p = subst HSpace (ua∙ e p)

-- join congruence of S¹ ≃ Susp Bool, both sides (library Iso→joinIso;
-- basepoint inl north ↦ inl base definitionally)
joinBool≃joinS¹ : join SuspBool SuspBool ≃ join S¹ S¹
joinBool≃joinS¹ =
  isoToEquiv (Iso→joinIso (invIso S¹IsoSuspBool) (invIso S¹IsoSuspBool))

-- BR's core obligation, now concrete: the quaternion multiplication
-- H-space on join S¹ S¹
JoinS¹-HSpace : HSpace (join∙ (S₊∙ 1) (S₊∙ 1))
JoinS¹-HSpace = HSpace≃ joinBool≃joinS¹ refl JoinSuspBool-HSpace

-- (restated from QBPS3HSpace.agda) join S¹ S¹ ≃ S³ carries it home
S³-HSpace-from-join : HSpace (join∙ (S₊∙ 1) (S₊∙ 1)) → HSpace (S₊∙ 3)
S³-HSpace-from-join =
  HSpace≃ (isoToEquiv (IsoSphereJoin 1 1)) (IsoSphereJoinPres∙ 1 1)

-- ————————————————————————————————————————————————————————————————
-- THE THEOREM: S³ is an H-space (Buchholtz–Rijke, machine-checked)
-- ————————————————————————————————————————————————————————————————
S³-HSpace : HSpace (S₊∙ 3)
S³-HSpace = S³-HSpace-from-join JoinS¹-HSpace
