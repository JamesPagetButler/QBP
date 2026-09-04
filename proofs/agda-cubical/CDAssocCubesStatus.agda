{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #579 Step B (iteration 17): the EXISTENCE STATUS of the seven open cubes
-- of CDAssocReduction, for the concrete Bool instance — i.e. exactly which
-- part of `AssocHSpace JoinSuspBool-HSpace` is a connectivity fact and which
-- part is genuine homotopical content.
--
-- join (Susp Bool) (Susp Bool) ≃ S³ is 2-connected (isConnected 4). An
-- n-fold iterated path type in a 2-connected type is (2−n)-connected, so:
--
--   * each two-push cube `Cube-··-·-at …` is a 3-fold path type
--     (PathP of PathP of ≡)  ⇒  isConnected 1  ⇒  MERELY inhabited.
--     Proved below for all six, pointwise:
--       Cube-xy-L-exists : ∀ a b c d e → ∥ Cube-xy-L-at a b c d e ∥₁   (etc.)
--     This is π₂(S³) = 0. It does NOT produce a term: the fillers form a
--     torsor over Ω³S³ (π₃(S³) = ℤ), so no two are (merely) equal and no
--     canonical choice is available; to build `μ-assoc` an EXPLICIT filler
--     must be constructed (by unfolding `pushMulSquare`'s transport — see
--     REFINEMENT-LOG iteration 17 for the reduction to a loop-equality in
--     (Susp Bool)⁴ and why it was not completed here).
--
--   * the three-push 4-cube `Cube-xyz-at …` is a 4-fold path type; the same
--     argument would need isConnected 5 (join …), i.e. π₃(S³) = 0, which is
--     FALSE (π₃(S³) = ℤ). Its existence is a degree computation — the
--     boundary 3-sphere of the 4-cube must have degree 0 in S³ — and its
--     fillers form a torsor over Ω⁴S³ (π₄(S³) = ℤ/2). Nothing is claimed
--     about it here; it is the irreducible content of AC1.
--
--   * the unit-coherence `Filler-at y z` (given the cubes) is a 2-fold path
--     type ⇒ isConnected 2 ⇒ merely inhabited pointwise (Filler-exists).
--
-- All statements are POINTWISE mere existence; ∥ ∀ x → P x ∥₁ does not
-- follow (no choice), and mere existence never yields the AssocHSpace term.
-- Nothing here feeds into any proof; it is the precise obstruction map.

module CDAssocCubesStatus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso ; compIso)
open import Cubical.Foundations.Equiv using (equivToIso)
open import Cubical.Data.Bool using (not)
open import Cubical.HITs.Join using (join)
open import Cubical.HITs.Susp using (SuspBool)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.HITs.Sn.Multiplication using (IsoSphereJoin)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.HITs.Truncation using (propTruncTrunc1Iso)
open import Cubical.Homotopy.Connected
  using (isConnected ; isConnectedPath ; isConnectedPathP
        ; isConnectedRetractFromIso ; isConnectedSubtr)

open import S3FromCD using (joinBool≃joinS¹)
open import CDAssocReduction
open import CDAssocBool

private
  J₂ : Type
  J₂ = join SuspBool SuspBool

  open BoolRed

-- join (Susp Bool)² ≃ S³ is 2-connected (library: sphereConnected 3)
J₂-connected : isConnected 4 J₂
J₂-connected =
  isConnectedRetractFromIso 4
    (compIso (equivToIso joinBool≃joinS¹) (IsoSphereJoin 1 1))
    (sphereConnected 3)

private
  -- isContr (∥ A ∥ 1)  ⇒  ∥ A ∥₁
  merely : {A : Type} → isConnected 1 A → ∥ A ∥₁
  merely c = Iso.inv propTruncTrunc1Iso (fst c)

  -- a 3-fold path type in J₂ is 0-connected
  cube-conn : {L R : (i j : I) → J₂}
    → {α : (i : I) → L i i0 ≡ R i i0} {β : (i : I) → L i i1 ≡ R i i1}
    → {γ : PathP (λ j → L i0 j ≡ R i0 j) (α i0) (β i0)}
    → {δ : PathP (λ j → L i1 j ≡ R i1 j) (α i1) (β i1)}
    → isConnected 1 (PathP (λ i → PathP (λ j → L i j ≡ R i j) (α i) (β i)) γ δ)
  cube-conn {L = L} {R = R} {α} {β} {γ} {δ} =
    isConnectedPathP 1
      (isConnectedPathP 2 (isConnectedPath 3 J₂-connected _ _) _ _) _ _

-- ————————————————————————————————————————————————————————————————
-- the six two-push cubes exist merely (π₂(S³) = 0)
-- ————————————————————————————————————————————————————————————————

Cube-xy-L-exists : ∀ a b c d e → ∥ Cube-xy-L-at a b c d e ∥₁
Cube-xy-L-exists a b c d e = merely cube-conn

Cube-xy-R-exists : ∀ a b c d f → ∥ Cube-xy-R-at a b c d f ∥₁
Cube-xy-R-exists a b c d f = merely cube-conn

Cube-xz-L-exists : ∀ a b c e f → ∥ Cube-xz-L-at a b c e f ∥₁
Cube-xz-L-exists a b c e f = merely cube-conn

Cube-xz-R-exists : ∀ a b d e f → ∥ Cube-xz-R-at a b d e f ∥₁
Cube-xz-R-exists a b d e f = merely cube-conn

Cube-yz-L-exists : ∀ a c d e f → ∥ Cube-yz-L-at a c d e f ∥₁
Cube-yz-L-exists a c d e f = merely cube-conn

Cube-yz-R-exists : ∀ b c d e f → ∥ Cube-yz-R-at b c d e f ∥₁
Cube-yz-R-exists b c d e f = merely cube-conn

-- ————————————————————————————————————————————————————————————————
-- given all seven cubes, the unit-coherence filler exists merely, pointwise
-- ————————————————————————————————————————————————————————————————

module _ (cxyL : Cube-xy-L) (cxyR : Cube-xy-R)
         (cxzL : Cube-xz-L) (cxzR : Cube-xz-R)
         (cyzL : Cube-yz-L) (cyzR : Cube-yz-R)
         (cxyz : Cube-xyz cxyL cxyR cxzL cxzR cyzL cyzR) where

  open AssumingCubes cxyL cxyR cxzL cxzR cyzL cyzR cxyz

  -- a 2-fold path type in J₂ is 1-connected; weaken to 0-connected
  Filler-exists : (y z : J₂) → ∥ Filler-at y z ∥₁
  Filler-exists y z =
    merely (isConnectedSubtr 1 1
             (isConnectedPathP 2 (isConnectedPath 3 J₂-connected _ _) _ _))
