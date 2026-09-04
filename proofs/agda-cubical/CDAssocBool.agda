{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #579 Step B (iteration 16, concrete instance): the extra base laws that
-- CDAssocReduction needs, for the imaginaroid Susp Bool ≃ S¹ = ℂ-level
-- (so that its Cayley–Dickson double is the associative ℍ-level).
--
--   SuspBool-CDCommLaws : CDCommLaws not SuspBool-CDLaws
--     ⊗-comm    : x ⊗Bool y ≡ y ⊗Bool x                (S¹ is commutative)
--     star-⊗    : starS (x ⊗Bool y) ≡ starS x ⊗Bool starS y
--     star-star : starS (starS x) ≡ x
--     ⊗-negˡ    : negS x ⊗Bool y ≡ negS (x ⊗Bool y)
--
-- and the instantiated reduction: the 8 corner cases and 12 one-push
-- squares of the associator of cd-mul on join (Susp Bool) (Susp Bool) are
-- PROVED (module `BoolRed`), and the full `AssocHSpace JoinSuspBool-HSpace`
-- — the kernel obligation of QuaternionicHopf.S³-AssocHSpace-kernel —
-- is reduced to the 7 cube types + unit filler:
--
--   JoinSuspBool-AssocHSpace-from-cubes :
--     (cxyL : Cube-xy-L) … (cyzR : Cube-yz-R) (cxyz : Cube-xyz …)
--     → Filler → AssocHSpace JoinSuspBool-HSpace
--
-- No inhabitant of any cube type is claimed. Scoping: CDLaws unchanged.
--
-- Method for ⊗-comm and the invLooper homomorphism: the wedge-connectivity
-- principle for S¹ × S¹ (Cubical.HITs.Sn.Properties.wedgeconFun 0 0), valid
-- because the targets are path types in the groupoid S¹ (h-level 2 = 1+1).
-- No point-level commutativity of S¹'s `_·_` exists in the pinned library
-- (only comm-ΩS¹ on loops), so it is derived here.

module CDAssocBool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; not)
open import Cubical.HITs.S1
  using (S¹ ; base ; loop ; _·_ ; invLooper ; isGroupoidS¹)
open import Cubical.HITs.Sn.Properties using (wedgeconFun)
open import Cubical.HITs.Susp
  using (Susp ; SuspBool ; north ; south ; merid
        ; SuspBool→S¹ ; S¹→SuspBool ; SuspBool→S¹→SuspBool ; S¹→SuspBool→S¹)
open import Cubical.HITs.Join using (join ; inl)
open import Cubical.Homotopy.HSpace using (HSpace ; AssocHSpace)

open import CDJoinBR using (negS ; starS ; CDLaws)
open import CDLawsBool
  using (_⊗Bool_ ; negS-id ; star-to ; SuspBool-CDLaws ; JoinSuspBool-HSpace)
open import CDAssocReduction

private
  to : SuspBool → S¹
  to = SuspBool→S¹

  fr : S¹ → SuspBool
  fr = S¹→SuspBool

  sec' : ∀ x → fr (to x) ≡ x
  sec' = SuspBool→S¹→SuspBool

  ret' : ∀ x → to (fr x) ≡ x
  ret' = S¹→SuspBool→S¹

  rUnitS¹ : (x : S¹) → x · base ≡ x
  rUnitS¹ base     = refl
  rUnitS¹ (loop i) = refl

  st : SuspBool → SuspBool
  st = starS not

  ng : SuspBool → SuspBool
  ng = negS not

-- ————————————————————————————————————————————————————————————————
-- S¹ facts by wedge connectivity (targets are sets: S¹ is a groupoid)
-- ————————————————————————————————————————————————————————————————

-- base · y ≐ y definitionally, so the left leg is the right-unit law
·-comm : (x y : S¹) → x · y ≡ y · x
·-comm =
  wedgeconFun 0 0 {A = λ x y → x · y ≡ y · x}
    (λ _ _ → isGroupoidS¹ _ _)
    (λ y → sym (rUnitS¹ y))
    (λ x → rUnitS¹ x)
    refl

-- invLooper is a homomorphism: invLooper base ≐ base, base · z ≐ z
invLooper-· : (x y : S¹) → invLooper (x · y) ≡ invLooper x · invLooper y
invLooper-· =
  wedgeconFun 0 0 {A = λ x y → invLooper (x · y) ≡ invLooper x · invLooper y}
    (λ _ _ → isGroupoidS¹ _ _)
    (λ y → refl)
    (λ x → cong invLooper (rUnitS¹ x) ∙ sym (rUnitS¹ (invLooper x)))
    (sym (rUnit refl))

-- ————————————————————————————————————————————————————————————————
-- the CDCommLaws fields
-- ————————————————————————————————————————————————————————————————

⊗-commBool : (x y : SuspBool) → x ⊗Bool y ≡ y ⊗Bool x
⊗-commBool x y = cong fr (·-comm (to x) (to y))

-- starS is invLooper transported along the iso (star-to, sec')
private
  star-fr : (x : SuspBool) → st x ≡ fr (invLooper (to x))
  star-fr x = sym (sec' (st x)) ∙ cong fr (star-to x)

star-⊗Bool : (x y : SuspBool) → st (x ⊗Bool y) ≡ st x ⊗Bool st y
star-⊗Bool x y =
    star-fr (x ⊗Bool y)
  ∙ cong (λ t → fr (invLooper t)) (ret' (to x · to y))
  ∙ cong fr (invLooper-· (to x) (to y))
  ∙ cong₂ (λ s t → fr (s · t)) (sym (star-to x)) (sym (star-to y))

-- not (not a) ≐ a on each constructor, so all clauses are refl
star-starBool : (x : SuspBool) → st (st x) ≡ x
star-starBool north           = refl
star-starBool south           = refl
star-starBool (merid true i)  = refl
star-starBool (merid false i) = refl

-- negation is the identity on Susp Bool (negS-id), on either side
⊗-negˡBool : (x y : SuspBool) → ng x ⊗Bool y ≡ ng (x ⊗Bool y)
⊗-negˡBool x y = cong (_⊗Bool y) (negS-id x) ∙ sym (negS-id (x ⊗Bool y))

SuspBool-CDCommLaws : CDCommLaws not SuspBool-CDLaws
SuspBool-CDCommLaws = record
  { ⊗-comm    = ⊗-commBool
  ; star-⊗    = star-⊗Bool
  ; star-star = star-starBool
  ; ⊗-negˡ    = ⊗-negˡBool
  }

-- ————————————————————————————————————————————————————————————————
-- the instantiated reduction
-- ————————————————————————————————————————————————————————————————

-- proved: assoc-corner (8), assocₓ / assoc-y / assoc-z (12 squares);
-- stated: Cube-xy-L … Cube-yz-R, Cube-xyz, Filler
module BoolRed = Reduction not SuspBool-CDLaws SuspBool-CDCommLaws

open BoolRed using (Cube-xy-L ; Cube-xy-R ; Cube-xz-L ; Cube-xz-R
                   ; Cube-yz-L ; Cube-yz-R ; Cube-xyz)

-- the kernel obligation of #579 AC1, reduced to the 7 cubes + filler.
-- (JoinSuspBool-HSpace ≐ CDBool.CDJoin-HSpace, so the target is exactly
-- QuaternionicHopf.S³-AssocHSpace-kernel.)
JoinSuspBool-AssocHSpace-from-cubes :
    (cxyL : Cube-xy-L) (cxyR : Cube-xy-R)
    (cxzL : Cube-xz-L) (cxzR : Cube-xz-R)
    (cyzL : Cube-yz-L) (cyzR : Cube-yz-R)
    (cxyz : Cube-xyz cxyL cxyR cxzL cxzR cyzL cyzR)
  → BoolRed.AssumingCubes.Filler cxyL cxyR cxzL cxzR cyzL cyzR cxyz
  → AssocHSpace JoinSuspBool-HSpace
JoinSuspBool-AssocHSpace-from-cubes cxyL cxyR cxzL cxzR cyzL cyzR cxyz =
  BoolRed.AssumingCubes.CDJoin-AssocHSpace cxyL cxyR cxzL cxzR cyzL cyzR cxyz
