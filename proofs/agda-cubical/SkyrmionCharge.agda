{-# OPTIONS --cubical --safe --no-import-sorts --guardedness --lossy-unification #-}

-- #595 first step: the Skyrmion topological charge (baryon number) as a
-- verified integer — the homotopy-layer "baryon-number primitive".
--
-- Physics (mandate B): in the Skyrme model a static configuration is a map
-- U : ℝ³ ∪ {∞} ≅ S³ → SU(2) ≅ S³ (unit quaternions), with the boundary
-- condition U(∞) = 1 making it pointed. Derrick's theorem forbids a stable
-- localized lump on geometry alone; what traps the "ducky in the water" is
-- the conserved TOPOLOGICAL charge: the degree of the map, i.e. its class
-- in π₃(S³) = ℤ. That integer is the baryon number B.
--
-- What is proved here (plain math), all on the S₊∙ 3 presentation — the
-- same pointed sphere that carries the quaternionic H-space of the #575
-- BR port (S3FromCD.S³-HSpace, re-exported below as S³-carrier-HSpace):
--
--   1. baryonNumber : (S³ → S³) → ℤ  — a callable charge function (degree).
--   2. B(vacuum)         = 0         (constant map).
--   3. B(hedgehog)       = 1         (identity map — the unit Skyrmion).
--   4. B(f ∙Π g)         = B f + B g (charge additivity under the pinch
--                                     sum: two lumps side by side).
--   5. B(-Π f)           = - B f     (the anti-Skyrmion negates charge).
--   6. skyrmionℤ z with B(skyrmionℤ z) = z : EVERY integer charge sector
--      is realized by an explicit configuration (charge-z multi-Skyrmion).
--   7. π₃(S³) ≅ ℤ as groups, the hedgehog ↦ 1 and generates — baryon
--      number is exactly the π₃ class.
--   8. ∥ S³ → S³ ∥₂ ≅ ℤ via baryonNumber: the charge is a COMPLETE
--      homotopy invariant — configurations are deformable into one another
--      iff their baryon numbers agree (charge conservation + classification;
--      the Derrick escape hatch made precise).
--
-- Note the +1 orientation convention: "degree of idfun = +1" fixes the sign
-- of B; the anti-Skyrmion is then B = −1 by theorem, not by convention.
--
-- All charge values are pinned to SPECIFIC integers (pos 1, pos 0, negsuc 0,
-- pos n, …) — never a bare existence claim. Everything below is --safe with
-- agda/cubical @ 7b9019b2 (cubical-0.9); the library's degree is computed
-- through Hⁿ(Sⁿ,ℤ) (Cubical.HITs.Sn.Degree) for computational behaviour.
--
-- Performance notes (they shape two statements, not their content):
--  * --lossy-unification is required: without it, checking any use of
--    Cubical.Homotopy.Group.PinSn's concrete-index lemmas (πₙ'Sⁿ≅ℤ 2, …)
--    diverges in conversion (>25 min, killed). The flag is --safe-compatible
--    and is what PinSn/Pi3S2/Pi4S3.Summary themselves use.
--  * The two π₃ contract statements are spelled VERBATIM in the library's
--    form (idfun∙ (S₊∙ 3), fun (fst (πₙ'Sⁿ≅ℤ 2))) rather than through the
--    hedgehog/π₃S³≅ℤ aliases: routing them through aliases forces full
--    normalization of the PinSn iso (observed 6 GB / >30 min, killed).
--    hedgehog-is-idfun∙ below certifies the identification by refl, so
--    nothing is weakened.

module SkyrmionCharge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (_→∙_ ; idfun∙ ; pt)
open import Cubical.Foundations.Isomorphism using (Iso)

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; -_ ; +Comm)
  renaming (_+_ to _+ℤ_)

open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.SetTruncation using (∥_∥₂ ; ∣_∣₂)
open import Cubical.HITs.Sn.Degree
  using (degree ; degreeIdfun ; degreeConst ; degreeHom ; degree∥₂ ; degree∥₂Iso)

open import Cubical.Homotopy.Group.Base
  using (π'Gr ; ∙Π ; -Π ; 1Π ; ∙Π-rCancel)
open import Cubical.Homotopy.Group.PinSn
  using (πₙ'Sⁿ≅ℤ ; πₙ'Sⁿ≅ℤ-idfun∙ ; πₙ'Sⁿ-gen-by-idfun)
open import Cubical.Homotopy.HSpace using (HSpace)

open import Cubical.Algebra.Group.Morphisms using (GroupIso)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.ZAction using (gen₁-by)

open import S3FromCD using (S³-HSpace)

open Iso
open GroupTheory ℤGroup using (invUniqueR)

-- ————————————————————————————————————————————————————————————————
-- Configurations: compactified space S³ → target S³ (= unit quaternions).
-- The pointed variant is the physical one (vacuum boundary condition
-- U(∞) = 1).
-- ————————————————————————————————————————————————————————————————

SkyrmeConfig : Type₀
SkyrmeConfig = S₊ 3 → S₊ 3

SkyrmeConfig∙ : Type₀
SkyrmeConfig∙ = S₊∙ 3 →∙ S₊∙ 3

-- The target S₊∙ 3 is the very sphere the #575 Buchholtz–Rijke port
-- equips with quaternion multiplication; re-exported here so the link
-- is checked at the type level (projecting μ out of the transported
-- structure is a performance follow-up — see header note).
S³-carrier-HSpace : HSpace (S₊∙ 3)
S³-carrier-HSpace = S³-HSpace

-- ————————————————————————————————————————————————————————————————
-- Mandate C, the callable primitive: baryon number = degree of the map
-- ————————————————————————————————————————————————————————————————

baryonNumber : SkyrmeConfig → ℤ
baryonNumber = degree 3

baryonNumber∙ : SkyrmeConfig∙ → ℤ
baryonNumber∙ f = baryonNumber (fst f)

-- ————————————————————————————————————————————————————————————————
-- The elementary configurations and their pinned charges
-- ————————————————————————————————————————————————————————————————

-- the vacuum: everything sits at the basepoint (identity quaternion)
vacuum : SkyrmeConfig
vacuum _ = ptSn 3

-- the unit Skyrmion ("hedgehog"): the identity S³ → S³
hedgehog : SkyrmeConfig∙
hedgehog = idfun∙ (S₊∙ 3)

-- the anti-Skyrmion: the hedgehog with reversed orientation
antihedgehog : SkyrmeConfig∙
antihedgehog = -Π hedgehog

-- B(vacuum) = 0 : no topological protection, Derrick collapse allowed
baryonNumber-vacuum-correct : baryonNumber vacuum ≡ pos 0
baryonNumber-vacuum-correct = degreeConst 3

-- B(hedgehog) = 1 : the single baryon
baryonNumber-hedgehog-correct : baryonNumber∙ hedgehog ≡ pos 1
baryonNumber-hedgehog-correct = degreeIdfun 3

-- ————————————————————————————————————————————————————————————————
-- Charge algebra: additivity under the pinch sum, negation under -Π
-- ————————————————————————————————————————————————————————————————

-- B(f ∙Π g) = B f + B g : two lumps carry the sum of the charges
baryonNumber-additive : (f g : SkyrmeConfig∙)
  → baryonNumber∙ (∙Π f g) ≡ baryonNumber∙ f +ℤ baryonNumber∙ g
baryonNumber-additive = degreeHom {n = 2}

-- B(-Π f) = - B f : orientation reversal negates the charge
baryonNumber-negate : (f : SkyrmeConfig∙)
  → baryonNumber∙ (-Π f) ≡ - baryonNumber∙ f
baryonNumber-negate f = invUniqueR
  (sym (baryonNumber-additive f (-Π f))
   ∙ cong baryonNumber∙ (∙Π-rCancel f)
   ∙ degreeConst 3)

-- B(antihedgehog) = -1 : the antibaryon (a theorem, not a convention)
baryonNumber-antihedgehog-correct : baryonNumber∙ antihedgehog ≡ negsuc 0
baryonNumber-antihedgehog-correct =
  baryonNumber-negate hedgehog ∙ cong -_ baryonNumber-hedgehog-correct

-- ————————————————————————————————————————————————————————————————
-- Every charge sector is inhabited: the explicit charge-z configuration
-- ————————————————————————————————————————————————————————————————

-- n-fold pinch sum of hedgehogs: the charge-n multi-Skyrmion
skyrmion : ℕ → SkyrmeConfig∙
skyrmion zero = 1Π
skyrmion (suc n) = ∙Π hedgehog (skyrmion n)

baryonNumber-skyrmion-correct : (n : ℕ)
  → baryonNumber∙ (skyrmion n) ≡ pos n
baryonNumber-skyrmion-correct zero = degreeConst 3
baryonNumber-skyrmion-correct (suc n) =
    baryonNumber-additive hedgehog (skyrmion n)
  ∙ cong₂ _+ℤ_ (baryonNumber-hedgehog-correct)
               (baryonNumber-skyrmion-correct n)
  ∙ +Comm (pos 1) (pos n)

-- all of ℤ: negative sectors via the anti-Skyrmion
skyrmionℤ : ℤ → SkyrmeConfig∙
skyrmionℤ (pos n) = skyrmion n
skyrmionℤ (negsuc n) = -Π (skyrmion (suc n))

-- B(skyrmionℤ z) = z : the baryon-number primitive is surjective, with an
-- explicit witness in every sector
baryonNumber-skyrmionℤ-correct : (z : ℤ)
  → baryonNumber∙ (skyrmionℤ z) ≡ z
baryonNumber-skyrmionℤ-correct (pos n) = baryonNumber-skyrmion-correct n
baryonNumber-skyrmionℤ-correct (negsuc n) =
    baryonNumber-negate (skyrmion (suc n))
  ∙ cong -_ (baryonNumber-skyrmion-correct (suc n))

-- ————————————————————————————————————————————————————————————————
-- The charge group: π₃(S³) ≅ ℤ, generated by the hedgehog
--
-- The two contract statements below are spelled in the library's verbatim
-- form (see header performance note); hedgehog-is-idfun∙ pins the
-- identification with our hedgehog by refl, so they are statements about
-- the hedgehog on the nose.
-- ————————————————————————————————————————————————————————————————

π₃S³≅ℤ : GroupIso (π'Gr 2 (S₊∙ 3)) ℤGroup
π₃S³≅ℤ = πₙ'Sⁿ≅ℤ 2

hedgehog-is-idfun∙ : hedgehog ≡ idfun∙ (S₊∙ 3)
hedgehog-is-idfun∙ = refl

-- the iso sends the hedgehog's π₃ class to 1 ∈ ℤ …
π₃S³≅ℤ-hedgehog-correct :
  fun (fst (πₙ'Sⁿ≅ℤ 2)) ∣ idfun∙ (S₊∙ 3) ∣₂ ≡ pos 1
π₃S³≅ℤ-hedgehog-correct = πₙ'Sⁿ≅ℤ-idfun∙ 2

-- … and the hedgehog generates π₃(S³): every sector is a multiple of B = 1
π₃S³-gen-by-hedgehog : gen₁-by (π'Gr 2 (S₊∙ 3)) ∣ idfun∙ (S₊∙ 3) ∣₂
π₃S³-gen-by-hedgehog = πₙ'Sⁿ-gen-by-idfun 2

-- ————————————————————————————————————————————————————————————————
-- Conservation and completeness: B is a complete homotopy invariant
-- ————————————————————————————————————————————————————————————————

-- B descends to homotopy classes of configurations …
baryonNumber∥₂ : ∥ SkyrmeConfig ∥₂ → ℤ
baryonNumber∥₂ = degree∥₂ 2

baryonNumber∥₂-correct : (f : SkyrmeConfig)
  → baryonNumber∥₂ ∣ f ∣₂ ≡ baryonNumber f
baryonNumber∥₂-correct f = refl

-- … and classifies them completely: sectors ↔ ℤ. Deforming a configuration
-- (a path f ≡ g IS a homotopy, cubically) cannot change B, and equal B
-- means deformable into one another. This is the topological trap that
-- Derrick's theorem demands.
skyrmionSectorsIso : Iso ∥ SkyrmeConfig ∥₂ ℤ
skyrmionSectorsIso = degree∥₂Iso 2

skyrmionSectorsIso-is-baryonNumber : (f : SkyrmeConfig)
  → fun skyrmionSectorsIso ∣ f ∣₂ ≡ baryonNumber f
skyrmionSectorsIso-is-baryonNumber f = refl

-- charge conservation, explicitly: a homotopy of configurations preserves B
baryonNumber-conserved : {f g : SkyrmeConfig} → f ≡ g
  → baryonNumber f ≡ baryonNumber g
baryonNumber-conserved = cong baryonNumber

-- completeness, explicitly: equal charge ⇒ configurations are homotopic
-- (equal in the set truncation of the configuration space)
baryonNumber-complete : (f g : SkyrmeConfig)
  → baryonNumber f ≡ baryonNumber g
  → Path ∥ SkyrmeConfig ∥₂ ∣ f ∣₂ ∣ g ∣₂
baryonNumber-complete f g p =
    sym (ret skyrmionSectorsIso ∣ f ∣₂)
  ∙ cong (inv skyrmionSectorsIso) p
  ∙ ret skyrmionSectorsIso ∣ g ∣₂
