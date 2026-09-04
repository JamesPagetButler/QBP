{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #579: the quaternionic Hopf fibration  S³ ↪ S⁷ ↠ S⁴  from the substrate's
-- quaternion multiplication (S3FromCD.S³-HSpace, the Buchholtz–Rijke port),
-- and the precise statement of what is still open (join-level associativity).
--
-- WHAT IS PROVED HERE (all --safe, no postulates/holes/pragmas):
--
--  (1) S³-connected : (x y : S₊ 3) → ∥ x ≡ y ∥₁            (sphere connectivity)
--
--  (2) HopfS³ : S₊ 4 → Type — the Hopf construction on the quaternion
--      H-space: HopfS³ north = S₊ 3, HopfS³ south = S₊ 3, and along merid a
--      the fibre is glued by right-multiplication (· a) : S³ ≃ S³ (the
--      equivalence exists because S³ is connected — HopfNoAssoc.μ-eq).
--      HopfS³-fibre  : HopfS³ north ≡ S₊ 3                       (by refl)
--      HopfS³-fibre∀ : (x : S₊ 4) → ∥ HopfS³ x ≃ S₊ 3 ∥₁          (every fibre)
--
--  (3) TotalHopfS³-Iso-join : Iso (Σ[ x ∈ S₊ 4 ] HopfS³ x) (join (S₊ 3) (S₊ 3))
--      TotalHopfS³-Iso-S⁷   : Iso (Σ[ x ∈ S₊ 4 ] HopfS³ x) (S₊ 7)
--      — the total space of the fibration is S⁷ (S³ * S³ ≃ S⁷, IsoSphereJoin).
--      Together with the projection fst : Σ HopfS³ → S₊ 4 this IS the
--      quaternionic Hopf fibration S³ ↪ S⁷ ↠ S⁴ as a type family over S⁴.
--
--  (4) S³-AssocHSpace-from-join :
--        AssocHSpace JoinSuspBool-HSpace → AssocHSpace S³-HSpace
--      — associativity coherence for the S³ H-space REDUCES (via the generic
--      transport lemma AssocTransport.AssocHSpace≃, twice) to associativity of
--      Buchholtz–Rijke's Cayley–Dickson product on join (Susp Bool) (Susp Bool).
--
--  (5) module WithAssoc (S³-assoc : AssocHSpace S³-HSpace): given the
--      associativity witness, the library module Cubical.Homotopy.Hopf.Hopf is
--      instantiated verbatim at the quaternion H-space (exporting its full
--      content, including the join-of-joins joinIso₂ that needs μ-assoc), and
--      its fibration is shown to coincide with HopfS³ (Hopf≡HopfS³).
--
-- WHAT IS OPEN (#579 AC1, honest gap — see README + REFINEMENT-LOG iters 15–17):
--
--      S³-AssocHSpace-kernel : Type
--      S³-AssocHSpace-kernel = AssocHSpace JoinSuspBool-HSpace
--
--  i.e. for BR's cd-mul on join (Susp Bool) (Susp Bool):
--      μ-assoc        : ∀ x y z → cd-mul (cd-mul x y) z ≡ cd-mul x (cd-mul y z)
--      μ-assoc-filler : ∀ y z → PathP (λ i → cd-mul (cd-unitˡ y i) z
--                                            ≡ cd-unitˡ (cd-mul y z) i)
--                                     (μ-assoc (inl north) y z) refl
--  No term of this type is claimed anywhere in this directory. The
--  quaternionic Hopf FIBRATION (2)–(3) does not depend on it; only the
--  library's join-of-joins section (5) does.
--
--  What IS proved of it (CDAssocReduction / CDAssocBool / CDAssocCubesStatus):
--  20 of the 27 clauses of the join induction for μ-assoc (all corner cases
--  and all one-push squares), and the reduction of the rest to 7 explicitly
--  typed cubes + the unit filler, exposed here as
--      S³-AssocHSpace-from-cubes : (6 two-push cubes) (3-push 4-cube)
--                                → Filler → AssocHSpace S³-HSpace
--  The six two-push cubes exist merely (π₂(S³)=0, CDAssocCubesStatus); the
--  4-cube is the irreducible content (a degree-0 boundary in S³).
--
-- Performance discipline (README): S³-HSpace's μ is univalence-transported
-- and must never be normalized. Every concrete object below is obtained by
-- plain application of a generically-checked module/lemma
-- (HopfNoAssoc.HopfNA, AssocTransport.AssocHSpace≃, Cubical.Homotopy.Hopf.Hopf)
-- to S³-HSpace — the checker substitutes, it never unfolds μ.
--
-- Scoping (#579 (a), binding): nothing here touches CDLaws / CDJoin-HSpace;
-- associativity is stated only for the concrete S³ / Bool instance.
-- Convention (#578 AC5): Baez CD convention throughout; no identification
-- with the Lean #474 Schafer-convention components is made.

module QuaternionicHopf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; isPropIsEquiv)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv ; compIso)
open import Cubical.Foundations.HLevels using (isProp→isOfHLevelSuc)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma using (Σ-syntax ; Σ≡Prop)

open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.HITs.Sn using (S₊ ; S₊∙)
open import Cubical.HITs.Sn.Properties using (sphereElim ; sphereElim2)
open import Cubical.HITs.Sn.Multiplication
  using (IsoSphereJoin ; IsoSphereJoinPres∙)
open import Cubical.HITs.Join using (join ; inl)

open import Cubical.Homotopy.HSpace using (HSpace ; AssocHSpace)
open import Cubical.Homotopy.Hopf using (module Hopf)

open import S3FromCD using (S³-HSpace ; JoinS¹-HSpace ; joinBool≃joinS¹)
open import CDLawsBool using (JoinSuspBool-HSpace)
open import AssocTransport using (AssocHSpace≃)
open import HopfNoAssoc using (module HopfNA)
open import CDAssocBool
  using (JoinSuspBool-AssocHSpace-from-cubes ; module BoolRed)

-- ————————————————————————————————————————————————————————————————
-- (1) S³ is connected (the library's sphere connectivity, in the form the
-- Hopf construction consumes)
-- ————————————————————————————————————————————————————————————————

S³-connected : (x y : S₊ 3) → ∥ x ≡ y ∥₁
S³-connected =
  sphereElim2 2 {A = λ x y → ∥ x ≡ y ∥₁}
    (λ _ _ → isProp→isOfHLevelSuc 2 squash₁) ∣ refl ∣₁

-- ————————————————————————————————————————————————————————————————
-- (2)+(3) THE FIBRATION: the Hopf construction on the quaternion H-space.
-- Plain application of the generically-checked HopfNA to S³-HSpace.
-- ————————————————————————————————————————————————————————————————

-- S₊ 4 ≐ Susp (S₊ 3): the base is S⁴
HopfS³ : S₊ 4 → Type
HopfS³ = HopfNA.Hopf S³-HSpace S³-connected

-- the fibre over the basepoint is S³ (definitionally)
HopfS³-fibre : HopfS³ north ≡ S₊ 3
HopfS³-fibre = refl

-- the gluing along merid a is right-multiplication by the unit quaternion a
HopfS³-merid : (a : S₊ 3)
  → cong HopfS³ (merid a) ≡ ua (HopfNA.μ-eq S³-HSpace S³-connected a)
HopfS³-merid a = refl

-- every fibre is (merely) S³ — S⁴ is connected and the statement is a prop
HopfS³-fibre∀ : (x : S₊ 4) → ∥ HopfS³ x ≃ S₊ 3 ∥₁
HopfS³-fibre∀ =
  sphereElim 3 {A = λ x → ∥ HopfS³ x ≃ S₊ 3 ∥₁}
    (λ _ → isProp→isOfHLevelSuc 3 squash₁) ∣ idEquiv (S₊ 3) ∣₁

-- the total space S⁷, with the projection to S⁴
TotalHopfS³ : Type
TotalHopfS³ = Σ[ x ∈ S₊ 4 ] HopfS³ x

HopfS³-proj : TotalHopfS³ → S₊ 4
HopfS³-proj = fst

TotalHopfS³-Iso-join : Iso TotalHopfS³ (join (S₊ 3) (S₊ 3))
TotalHopfS³-Iso-join = HopfNA.IsoTotalSpaceJoin S³-HSpace S³-connected

-- S³ * S³ ≃ S⁷ (IsoSphereJoin 3 3 : Iso (join (S₊ 3) (S₊ 3)) (S₊ (suc (3 + 3))))
TotalHopfS³-Iso-S⁷ : Iso TotalHopfS³ (S₊ 7)
TotalHopfS³-Iso-S⁷ = compIso TotalHopfS³-Iso-join (IsoSphereJoin 3 3)

TotalHopfS³≃S⁷ : TotalHopfS³ ≃ S₊ 7
TotalHopfS³≃S⁷ = isoToEquiv TotalHopfS³-Iso-S⁷

-- ————————————————————————————————————————————————————————————————
-- (4) The associativity reduction: S³ ⇐ join S¹ S¹ ⇐ join (Susp Bool)²
-- ————————————————————————————————————————————————————————————————

-- THE OPEN OBLIGATION (#579 AC1), stated as a type — no inhabitant claimed
S³-AssocHSpace-kernel : Type
S³-AssocHSpace-kernel = AssocHSpace JoinSuspBool-HSpace

S³-AssocHSpace-from-join : S³-AssocHSpace-kernel → AssocHSpace S³-HSpace
S³-AssocHSpace-from-join a =
  AssocHSpace≃ (isoToEquiv (IsoSphereJoin 1 1)) (IsoSphereJoinPres∙ 1 1)
    JoinS¹-HSpace
    (AssocHSpace≃ joinBool≃joinS¹ refl JoinSuspBool-HSpace a)

-- … and the kernel itself reduces to the 7 cubes + unit filler of
-- CDAssocReduction (20/27 clauses of the join induction already proved):
open BoolRed using (Cube-xy-L ; Cube-xy-R ; Cube-xz-L ; Cube-xz-R
                   ; Cube-yz-L ; Cube-yz-R ; Cube-xyz)

S³-AssocHSpace-from-cubes :
    (cxyL : Cube-xy-L) (cxyR : Cube-xy-R)
    (cxzL : Cube-xz-L) (cxzR : Cube-xz-R)
    (cyzL : Cube-yz-L) (cyzR : Cube-yz-R)
    (cxyz : Cube-xyz cxyL cxyR cxzL cxzR cyzL cyzR)
  → BoolRed.AssumingCubes.Filler cxyL cxyR cxzL cxzR cyzL cyzR cxyz
  → AssocHSpace S³-HSpace
S³-AssocHSpace-from-cubes cxyL cxyR cxzL cxzR cyzL cyzR cxyz fl =
  S³-AssocHSpace-from-join
    (JoinSuspBool-AssocHSpace-from-cubes cxyL cxyR cxzL cxzR cyzL cyzR cxyz fl)

-- ————————————————————————————————————————————————————————————————
-- (5) Given the witness: the library module, instantiated verbatim
-- ————————————————————————————————————————————————————————————————

module WithAssoc (S³-assoc : AssocHSpace S³-HSpace) where

  open Hopf S³-assoc S³-connected public

  -- the library's fibration IS the one above (pointwise, hence as families)
  private
    μ-eq-agree : (a : S₊ 3) → μ-eq a ≡ HopfNA.μ-eq S³-HSpace S³-connected a
    μ-eq-agree a = Σ≡Prop isPropIsEquiv refl

    pointwise : (x : S₊ 4) → Hopf x ≡ HopfS³ x
    pointwise north       = refl
    pointwise south       = refl
    pointwise (merid a i) = λ j → ua (μ-eq-agree a j) i

  Hopf≡HopfS³ : Hopf ≡ HopfS³
  Hopf≡HopfS³ = funExt pointwise
