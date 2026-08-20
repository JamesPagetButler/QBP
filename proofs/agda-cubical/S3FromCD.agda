{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #578 AC3/AC6: the final wiring — from the concrete Cayley-Dickson
-- H-space on join (Susp Bool) (Susp Bool) (CDLawsBool.agda) to the
-- H-space on S³, discharging the obligation left open by QBPS3HSpace.agda.
--
--   HSpace (join SuspBool SuspBool , inl north)      [CDLawsBool]
--     → HSpace (join∙ (S₊∙ 1) (S₊∙ 1))               [Iso→joinIso both sides
--                                                      of S¹IsoSuspBool + HSpace≃]
--     → HSpace (S₊∙ 3)                               [S³-HSpace-from-join]
--
-- This completes the Buchholtz–Rijke port (arXiv:1610.01134): S³ is an
-- H-space, --safe, 0 postulates, machine-checked end to end. Chain:
-- Diamond → CDJoinBR → CDLawsBool → S3FromCD (+ QBPS3HSpace's reduction).

module S3FromCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; invIso)
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.HSpace using (HSpace)
open import Cubical.Data.Bool using (Bool)
open import Cubical.HITs.S1 using (S¹ ; base)
open import Cubical.HITs.Susp using (SuspBool ; S¹IsoSuspBool)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.Join using (join ; inl ; join∙ ; Iso→joinIso)

open import QBPS3HSpace using (HSpace≃ ; S³-HSpace-from-join)
open import CDLawsBool using (JoinSuspBool-HSpace)

-- join congruence of S¹ ≃ Susp Bool, both sides (library Iso→joinIso;
-- basepoint inl north ↦ inl base definitionally)
joinBool≃joinS¹ : join SuspBool SuspBool ≃ join S¹ S¹
joinBool≃joinS¹ =
  isoToEquiv (Iso→joinIso (invIso S¹IsoSuspBool) (invIso S¹IsoSuspBool))

-- BR's core obligation (QBPS3HSpace §end), now concrete: the quaternion
-- multiplication H-space on join S¹ S¹
JoinS¹-HSpace : HSpace (join∙ (S₊∙ 1) (S₊∙ 1))
JoinS¹-HSpace = HSpace≃ joinBool≃joinS¹ refl JoinSuspBool-HSpace

-- ————————————————————————————————————————————————————————————————
-- THE THEOREM: S³ is an H-space (Buchholtz–Rijke, machine-checked)
-- ————————————————————————————————————————————————————————————————
S³-HSpace : HSpace (S₊∙ 3)
S³-HSpace = S³-HSpace-from-join JoinS¹-HSpace
