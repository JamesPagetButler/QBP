{-# OPTIONS --cubical --no-import-sorts --guardedness #-}
------------------------------------------------------------------------
-- The abstract Cayley–Dickson join-step (Buchholtz–Rijke's actual method).
-- A "CD-structure" carries unit + multiplication + conjugation + NEGATION
-- (negation is in the package precisely so it lifts up from S⁰ = Bool's `not`,
-- where it IS definable — never defined on S¹ directly). The CD-join step lifts
-- a CD-structure on A to one on (join A A) = the unit sphere of the doubled
-- algebra. Applied twice from Bool: Bool → S¹ → S³.
--
-- STATE (type-checked, one hole): CDStr record + lifted conjugation (conjJ) +
-- lifted negation (negJ) + multiplication _*J_'s 4 corners + all 4 one-cells —
-- ALL build. The entire step is reduced to ONE parametric coherence square
-- (push×push). With `neg` available this is the TRUE CD formula's square (the
-- concrete S¹ attempt could not even express it). Remaining: fill that square
-- using CDStr laws (add laws as needed) + instantiate at Bool → S¹ → S³.
------------------------------------------------------------------------
module CDJoin where
open import Cubical.Foundations.Prelude
open import Cubical.HITs.Join using (join ; inl ; inr ; push)

private variable ℓ : Level

-- A Cayley–Dickson structure on A: the data the join-step needs.
record CDStr (A : Type ℓ) : Type ℓ where
  field
    e      : A
    _⊗_    : A → A → A
    conj   : A → A
    neg    : A → A
    -- the minimal laws used by the lifted unit:
    ⊗-unitˡ : (a : A) → e ⊗ a ≡ a
    ⊗-unitʳ : (a : A) → a ⊗ e ≡ a
    conj-e  : conj e ≡ e

open CDStr

module _ {A : Type ℓ} (S : CDStr A) where
  private
    _·_ = _⊗_ S
    c   = conj S
    n   = neg S
    1A  = e S

  -- the lifted carrier and unit:
  JA : Type ℓ
  JA = join A A
  1J : JA
  1J = inl 1A

  -- lifted CONJUGATION on join A A (swap the two copies + conjugate):
  conjJ : JA → JA
  conjJ (inl a)      = inl (c a)
  conjJ (inr b)      = inr (n b)            -- conj of the j-part flips sign
  conjJ (push a b i) = push (c a) (n b) i

  -- lifted NEGATION on join A A:
  negJ : JA → JA
  negJ (inl a)      = inl (n a)
  negJ (inr b)      = inr (n b)
  negJ (push a b i) = push (n a) (n b) i

  -- lifted MULTIPLICATION — corners from the CD formula expressed via ·, conj, neg
  -- (so it has a two-sided unit inl 1A; see the unit laws below):
  _*J_ : JA → JA → JA
  inl a *J inl c'      = inl (a · c')
  inl a *J inr d       = inr (d · a)
  inr b *J inl c'      = inr (b · c c')
  inr b *J inr d       = inl (n (b · c d))
  -- 1-cells (second-arg push, first-arg push):
  inl a *J push c' d j = push (a · c') (d · a) j
  inr b *J push c' d j = sym (push (n (b · c d)) (b · c c')) j
  -- first-arg push: inner induction on the second argument
  push a b i *J inl c'      = push (a · c') (b · c c') i
  push a b i *J inr d       = sym (push (n (b · c d)) (d · a)) i
  push a b i *J push c' d k = {! THE abstract BR coherence SQUARE !}
