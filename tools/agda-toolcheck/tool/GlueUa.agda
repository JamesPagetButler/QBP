{-# OPTIONS --cubical --safe #-}
-- TOOLCHECK tool/GlueUa — univalence computes: Glue / glue / unglue / ua / uaβ.
--
-- Feature: `primGlue`, `prim^glue`, `prim^unglue`, the builtin `isEquiv`
-- record (`equiv-proof` by copattern), `ua` built from Glue, its endpoint
-- reductions (Glue with φ = i1 reduces to the glued type), the glue/unglue
-- β-rule, and `uaβ : transport (ua e) x ≡ e x` (transp over Glue computes).
--
-- Used by QBP: proofs/agda-cubical/HopfNoAssoc.agda (`ua (μ-eq a)`,
-- `ua-gluePt`, `ua-unglue`, `ua→`, `EquivJ`), QuaternionicHopf.agda
-- (`cong HopfS³ (merid a) ≡ ua …`), QBPS3HSpace.agda (`ua∙`).
module GlueUa where

open import Agda.Primitive using (Level)
open import Agda.Primitive.Cubical
  using (I; i0; i1)
  renaming (primTransp to transp; primINeg to ~_; primIMax to _∨_)
open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Cubical.Glue
  using (primGlue; prim^glue; prim^unglue; isEquiv; _≃_; equivFun)
open import Agda.Builtin.Bool using (Bool; true; false)

open isEquiv

private variable
  ℓ : Level
  A B : Set ℓ
  x : A

refl : x ≡ x
refl {x = x} = λ _ → x

transport : A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

transportRefl : (a : A) → transport refl a ≡ a
transportRefl {A = A} a i = transp (λ _ → A) i a

-- the identity equivalence, from the builtin isEquiv record (no-eta → copattern)
idIsEquiv : isEquiv (λ (a : A) → a)
idIsEquiv .equiv-proof b =
  (b , refl) , λ fib i → snd fib (~ i) , λ j → snd fib (~ i ∨ j)

idEquiv : A ≃ A
idEquiv = (λ a → a) , idIsEquiv

-- univalence as a Glue type over B, glued to A at i0 and to B at i1
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i =
  primGlue B {φ = ~ i ∨ i}
    (λ { (i = i0) → A ; (i = i1) → B })
    (λ { (i = i0) → e ; (i = i1) → idEquiv })

-- Glue with a total system reduces to the glued type: the endpoints are definitional
ua-i0 : (e : A ≃ B) → ua e i0 ≡ A
ua-i0 e = refl

ua-i1 : (e : A ≃ B) → ua e i1 ≡ B
ua-i1 e = refl

-- the β-rule: transport along ua is the function (transp over Glue computes)
uaβ : (e : A ≃ B) (a : A) → transport (ua e) a ≡ equivFun e a
uaβ e a = transportRefl (equivFun e a)

-- glue points and unglue
ua-gluePt : (e : A ≃ B) (i : I) (a : A) → ua e i
ua-gluePt e i a =
  prim^glue {φ = ~ i ∨ i} (λ { (i = i0) → a ; (i = i1) → equivFun e a }) (equivFun e a)

ua-unglue : (e : A ≃ B) (i : I) → ua e i → B
ua-unglue e i g = prim^unglue {φ = ~ i ∨ i} g

unglue-glue : (e : A ≃ B) (i : I) (a : A) → ua-unglue e i (ua-gluePt e i a) ≡ equivFun e a
unglue-glue e i a = refl

gluePt-i0 : (e : A ≃ B) (a : A) → ua-gluePt e i0 a ≡ a
gluePt-i0 e a = refl

gluePt-i1 : (e : A ≃ B) (a : A) → ua-gluePt e i1 a ≡ equivFun e a
gluePt-i1 e a = refl

-- a concrete instance on Bool
ua-id-Bool : (b : Bool) → transport (ua (idEquiv {A = Bool})) b ≡ b
ua-id-Bool = uaβ idEquiv
