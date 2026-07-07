{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- The Bool instantiation of the Cayley-Dickson join step — Cubical Agda
-- port of Buchholtz–Rijke's quaternionic_hopf.hlean (leanprover/lean2,
-- Apache 2.0, © 2016 U. Buchholtz, E. Rijke).
--
-- A₀ = Bool, neg₀ = not, so S = Susp Bool ≃ S¹.  The imaginaroid mult
-- is the circle multiplication conjugated along S¹IsoSuspBool:
--   x ⊗ y = S¹→SuspBool (SuspBool→S¹ x · SuspBool→S¹ y)
-- The CDLaws fields discharge via:
--   * units:  base · z ≐ z (left unit definitional), a pattern-match
--     right unit (rotLoop base = loop), and the iso's round-trips;
--   * ⊗-negʳ: negS ~ id on Susp Bool (BR circle_neg_id) — negation is
--     the antipodal map, degree 1, homotopic to the identity;
--   * norms:  starS corresponds to invLooper across the iso (star-to,
--     four interval one-liners), then rotInv-1 / rotInv-2;
--   * assoc:  the library's S1-AssocHSpace (wedge-connectivity proof).
--
-- Payoff: HSpace (join (Susp Bool) (Susp Bool) , inl north) — the
-- concrete quaternionic H-space, ready for the join-equivalence
-- transport to HSpace (join S¹ S¹) and then S³ (#578 AC3).

module CDLawsBool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (rUnit ; lCancel)
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Data.Bool using (Bool ; true ; false ; not)
open import Cubical.HITs.S1
  using (S¹ ; base ; loop ; _·_ ; invLooper ; rotInv-1 ; rotInv-2)
open import Cubical.HITs.Susp
  using (Susp ; north ; south ; merid ; SuspBool ;
         SuspBool→S¹ ; S¹→SuspBool ; SuspBool→S¹→SuspBool ; S¹→SuspBool→S¹)
open import Cubical.HITs.Join using (join ; inl)
open import Cubical.Homotopy.HSpace
  using (HSpace ; AssocHSpace ; S1-HSpace ; S1-AssocHSpace)

open import Diamond using (degSquare)
open import CDJoinBR

private
  to : SuspBool → S¹
  to = SuspBool→S¹

  fr : S¹ → SuspBool
  fr = S¹→SuspBool

  sec' : ∀ x → fr (to x) ≡ x
  sec' = SuspBool→S¹→SuspBool

  ret' : ∀ x → to (fr x) ≡ x
  ret' = S¹→SuspBool→S¹

  -- right unit on S¹ is a pattern-match refl (rotLoop base = loop)
  rUnitS¹ : (x : S¹) → x · base ≡ x
  rUnitS¹ base     = refl
  rUnitS¹ (loop i) = refl

  -- associativity from the library (S₊ 1 ≐ S¹, so this is on the circle)
  assocS¹ : (x y z : S¹) → (x · y) · z ≡ x · (y · z)
  assocS¹ = AssocHSpace.μ-assoc S1-AssocHSpace

  -- x · x⁻¹ ≡ 1 and x⁻¹ · x ≡ 1, from rotInv-1/2 at a := base
  -- (rotInv-1 : (b · a) · invLooper b ≡ a, left-assoc parse)
  ·-invʳ : (b : S¹) → b · invLooper b ≡ base
  ·-invʳ b = cong (_· invLooper b) (sym (rUnitS¹ b)) ∙ rotInv-1 base b

  ·-invˡ : (b : S¹) → invLooper b · b ≡ base
  ·-invˡ b = cong (_· b) (sym (rUnitS¹ (invLooper b))) ∙ rotInv-2 base b

-- the imaginaroid multiplication: circle mult conjugated along the iso
_⊗Bool_ : SuspBool → SuspBool → SuspBool
x ⊗Bool y = fr (to x · to y)

-- ————————————————————————————————————————————————————————————————
-- negS ~ id on Susp Bool (BR circle_neg_id)
-- ————————————————————————————————————————————————————————————————

-- Endpoint choice: north ↦ sym (merid false), south ↦ merid true.
-- Then the (merid true) case is exactly degSquare, and the
-- (merid false) case is the square witnessing that both boundary
-- composites cancel (lCancel on each meridian).
negS-id : (x : SuspBool) → negS not x ≡ x
negS-id north           = sym (merid false)
negS-id south           = merid true
negS-id (merid true i)  = degSquare (sym (merid false)) (merid true) i
negS-id (merid false i) =
  compPath→Square
    {p = sym (merid true)} {q = merid false}
    {r = sym (merid false)} {s = merid true}
    (lCancel (merid true) ∙ sym (lCancel (merid false)))
    i

-- ————————————————————————————————————————————————————————————————
-- starS corresponds to invLooper across the iso (BR circle_star_eq)
-- ————————————————————————————————————————————————————————————————

-- Endpoint choice: north ↦ refl, south ↦ sym loop.  Both meridian
-- squares are then single connections on `loop`.
star-to : (x : SuspBool) → to (starS not x) ≡ invLooper (to x)
star-to north             = refl
star-to south             = sym loop
star-to (merid false i) j = loop (~ (i ∧ j))
star-to (merid true i)  j = loop (i ∧ ~ j)

-- ————————————————————————————————————————————————————————————————
-- the CDLaws fields
-- ————————————————————————————————————————————————————————————————

-- left unit: to north ≐ base, base · z ≐ z, so this is just the
-- iso round-trip
⊗-unitˡBool : (x : SuspBool) → north ⊗Bool x ≡ x
⊗-unitˡBool = sec'

⊗-unitʳBool : (x : SuspBool) → x ⊗Bool north ≡ x
⊗-unitʳBool x = cong fr (rUnitS¹ (to x)) ∙ sec' x

-- at north both sides are refl-built: LHS ≐ refl, RHS ≐ refl ∙ refl
⊗-cohBool : ⊗-unitˡBool north ≡ ⊗-unitʳBool north
⊗-cohBool = rUnit refl

⊗-negBool : (x y : SuspBool) → x ⊗Bool negS not y ≡ negS not (x ⊗Bool y)
⊗-negBool x y = cong (x ⊗Bool_) (negS-id y) ∙ sym (negS-id (x ⊗Bool y))

normBoolʳ : (x : SuspBool) → x ⊗Bool starS not x ≡ north
normBoolʳ x =
    cong (λ t → fr (to x · t)) (star-to x)
  ∙ cong fr (·-invʳ (to x))

normBoolˡ : (x : SuspBool) → starS not x ⊗Bool x ≡ north
normBoolˡ x =
    cong (λ t → fr (t · to x)) (star-to x)
  ∙ cong fr (·-invˡ (to x))

⊗-assocBool : (x y z : SuspBool)
            → (x ⊗Bool y) ⊗Bool z ≡ x ⊗Bool (y ⊗Bool z)
⊗-assocBool x y z =
    cong (λ t → fr (t · to z)) (ret' (to x · to y))
  ∙ cong fr (assocS¹ (to x) (to y) (to z))
  ∙ cong (λ t → fr (to x · t)) (sym (ret' (to y · to z)))

-- ————————————————————————————————————————————————————————————————
-- the instantiated record and the payoff
-- ————————————————————————————————————————————————————————————————

SuspBool-CDLaws : CDLaws not
SuspBool-CDLaws = record
  { _⊗_        = _⊗Bool_
  ; ⊗-unitˡ    = ⊗-unitˡBool
  ; ⊗-unitʳ    = ⊗-unitʳBool
  ; ⊗-unit-coh = ⊗-cohBool
  ; ⊗-negʳ     = ⊗-negBool
  ; normʳ      = normBoolʳ
  ; normˡ      = normBoolˡ
  ; ⊗-assoc    = ⊗-assocBool
  }

module CDBool = CD not SuspBool-CDLaws

-- HSpace (S³-as-join-of-circles), in Susp Bool clothing: AC2 complete.
JoinSuspBool-HSpace : HSpace (join SuspBool SuspBool , inl north)
JoinSuspBool-HSpace = CDBool.CDJoin-HSpace
