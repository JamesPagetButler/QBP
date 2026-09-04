{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #579 Step A: associativity coherence transports along `HSpace≃`.
--
-- `HSpace≃ e p H = subst HSpace (ua∙ e p) H` (QBPS3HSpace.agda) carries an
-- H-space across a pointed equivalence. This file shows the SAME transport
-- carries an `AssocHSpace` witness with it:
--
--   AssocHSpace≃ e p H : AssocHSpace H → AssocHSpace (HSpace≃ e p H)
--
-- Proof discipline (README "Performance discipline"): the S³ multiplication
-- is a univalence-transported term whose normalization is structurally
-- divergent, so nothing here may ever compute with a concrete μ. The lemma
-- is proved by path induction (J) on the pointed path `ua∙ e p` with the
-- H-space `H` a *generic* argument: at `refl` the transported structure is
-- `subst HSpace refl H`, which `substRefl` identifies with `H`, and the
-- associativity witness is carried back along that identification by
-- `subst AssocHSpace`. No field of any H-space is ever projected.
--
-- Consequence: `AssocHSpace S³-HSpace` reduces, by two applications, to
-- `AssocHSpace JoinSuspBool-HSpace` — associativity of Buchholtz–Rijke's
-- Cayley–Dickson product on join (Susp Bool) (Susp Bool), the kernel
-- obligation stated in QuaternionicHopf.agda.

module AssocTransport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Pointed using (Pointed ; pt)
open import Cubical.Foundations.Pointed.Base using (ua∙)
open import Cubical.Homotopy.HSpace using (HSpace ; AssocHSpace)

open import QBPS3HSpace using (HSpace≃)

private variable ℓ : Level

-- associativity is carried along `subst HSpace` over ANY pointed path
AssocHSpace-subst : {A B : Pointed ℓ} (P : A ≡ B)
  → (H : HSpace A) → AssocHSpace H → AssocHSpace (subst HSpace P H)
AssocHSpace-subst {A = A} =
  J (λ B P → (H : HSpace A) → AssocHSpace H → AssocHSpace (subst HSpace P H))
    (λ H a → subst AssocHSpace (sym (substRefl {B = HSpace} H)) a)

-- … and hence along `HSpace≃` (the pointed-univalence transport)
AssocHSpace≃ : {A B : Pointed ℓ}
  → (e : fst A ≃ fst B) (p : fst e (pt A) ≡ pt B)
  → (H : HSpace A) → AssocHSpace H → AssocHSpace (HSpace≃ e p H)
AssocHSpace≃ e p = AssocHSpace-subst (ua∙ e p)
