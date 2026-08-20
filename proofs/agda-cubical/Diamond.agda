{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- Diamonds in joins — Cubical Agda port of Buchholtz–Rijke's join.hlean
-- (leanprover/lean2 hott/homotopy/join.hlean, Apache 2.0, © 2016 U. Buchholtz, E. Rijke).
--
-- THE KEY to the CD-join coherence square (the hole that resisted ~7 direct
-- hcomp attempts): a `diamond` is exactly the twisted push×push square, and
-- BR close it NOT by explicit filling but by
--   (1) rewriting all four corners as images of ONE generalized point under
--       two maps f, g            (imaginaroid lemmas 1–4),
--   (2) `apDiamond f g` of a UNIVERSAL one-variable diamond,
--   (3) suspension induction on that single variable:
--       poles → degenerate diamonds (vdiamond/hdiamond),
--       meridian → `twistDiamond`, a pure path-induction lemma.
-- No connectivity, no nested hcomp grinding — "very little type theoretic
-- machinery" (BR §Introduction), and it is all J/JRefl.

module Diamond where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Join using (join ; inl ; inr ; push)

private
  variable
    ℓ ℓ' : Level

-- ————————————————————————————————————————————————————————————————
-- Generic degenerate squares (pure path algebra, any type)
-- ————————————————————————————————————————————————————————————————

-- Square with top = left = p and bottom = right = refl: the ∨-square.
orSquare : {X : Type ℓ} {x y : X} (p : x ≡ y) → Square p refl p refl
orSquare p j k = p (j ∨ k)

-- Square with top = p, bottom = left = refl, right = sym p: the ∧-square.
andSquare : {X : Type ℓ} {x y : X} (p : x ≡ y) → Square p refl refl (sym p)
andSquare p j k = p (~ j ∧ k)

-- top = left = p, bottom = right = r  (BR's vdiamond core).
degSquare : {X : Type ℓ} {x y z : X} (p : x ≡ y) (r : y ≡ z)
          → Square p r p r
degSquare p = J (λ _ r → Square p r p r) (orSquare p)

-- top = P, left = Q, bottom = sym Q, right = sym P  (BR's hdiamond core).
hdegSquare : {X : Type ℓ} {x y z : X} (P : x ≡ y) (Q : x ≡ z)
           → Square P (sym Q) Q (sym P)
hdegSquare P = J (λ _ Q → Square P (sym Q) Q (sym P)) (andSquare P)

-- The two degenerate squares agree on the shared instance
-- (BR's symm_diamond, in its generic form).
sqLemma : {X : Type ℓ} {x y : X} (P : x ≡ y)
        → degSquare P (sym P) ≡ hdegSquare P P
sqLemma {X = X} =
  J (λ _ P → degSquare P (sym P) ≡ hdegSquare P P)
    ( JRefl (λ _ r → Square refl r refl r) (orSquare refl)
    ∙ sym (JRefl (λ _ Q → Square refl (sym Q) Q refl) (andSquare refl)))

-- ————————————————————————————————————————————————————————————————
-- Diamonds in join A B  (BR join.hlean §"Diamonds in joins")
-- ————————————————————————————————————————————————————————————————

module _ {A : Type ℓ} {B : Type ℓ'} where

  -- the twisted push×push square shape:
  --        push a b
  --   inl a ———————→ inr b
  --     |               |
  --     | push a b'     | sym (push a' b)
  --     ↓               ↓
  --   inr b' ——————→ inl a'
  --      sym (push a' b')
  diamond : (a a' : A) (b b' : B) → Type (ℓ-max ℓ ℓ')
  diamond a a' b b' =
    Square (push a b) (sym (push a' b')) (push a b') (sym (push a' b))

  -- degenerate diamond from a path on the B side
  vdiamond : (a a' : A) {b b' : B} (q : b ≡ b') → diamond a a' b b'
  vdiamond a a' {b} =
    J (λ b' _ → diamond a a' b b')
      (degSquare (push a b) (sym (push a' b)))

  -- degenerate diamond from a path on the A side
  hdiamond : {a a' : A} (b b' : B) (p : a ≡ a') → diamond a a' b b'
  hdiamond {a = a} b b' =
    J (λ a' _ → diamond a a' b b')
      (hdegSquare (push a b) (push a b'))

  -- the two degenerate refl-diamonds agree (BR symm_diamond)
  symmDiamond : (a : A) (b : B) → vdiamond a a refl ≡ hdiamond b b refl
  symmDiamond a b =
      JRefl (λ b' _ → diamond a a b b')
            (degSquare (push a b) (sym (push a b)))
    ∙ sqLemma (push a b)
    ∙ sym (JRefl (λ a' _ → diamond a a' b b)
                 (hdegSquare (push a b) (push a b)))

-- The universal twist (BR twist_diamond): over a path p : a ≡ a' in A,
-- the two degenerate diamonds are connected in the family
-- diamond a' (p i) a (p i)  ⊂  join A A.
twistDiamond : {A : Type ℓ} {a a' : A} (p : a ≡ a')
             → PathP (λ i → diamond a' (p i) a (p i))
                     (vdiamond a' a refl)
                     (hdiamond a a' refl)
twistDiamond {a = a} =
  J (λ a' p → PathP (λ i → diamond a' (p i) a (p i))
              (vdiamond a' a refl) (hdiamond a a' refl))
    (symmDiamond a a)

-- ————————————————————————————————————————————————————————————————
-- Functoriality (trivial in cubical: push is a binary constructor)
-- ————————————————————————————————————————————————————————————————

joinMap : {A B C D : Type ℓ} → (A → C) → (B → D) → join A B → join C D
joinMap f g (inl a)      = inl (f a)
joinMap f g (inr b)      = inr (g b)
joinMap f g (push a b i) = push (f a) (g b) i

-- BR's ap_diamond needed aps + 6 rewrites in Lean 2; here it is literal.
apDiamond : {A B C D : Type ℓ} (f : A → C) (g : B → D)
            {a a' : A} {b b' : B}
          → diamond a a' b b' → diamond (f a) (f a') (g b) (g b')
apDiamond f g s j k = joinMap f g (s j k)

-- BR's join.hsquare, cubical-style: push respects paths in both arguments.
pushCong : {A : Type ℓ} {B : Type ℓ'} {a a' : A} {b b' : B}
           (p : a ≡ a') (q : b ≡ b')
         → Square (cong inl p) (cong inr q) (push a b) (push a' b')
pushCong p q j k = push (p k) (q k) j
