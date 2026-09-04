{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- #579 Step B (iteration 16): the associativity of Buchholtz–Rijke's
-- Cayley–Dickson product on join S S, REDUCED to its irreducible cubes.
--
-- Scoping (#579 (a), binding): `CDLaws` and `CDJoin-HSpace` (CDJoinBR.agda)
-- are untouched and stay associativity-agnostic (S⁷/octonions). This module
-- takes `CDLaws` PLUS a separate record `CDCommLaws` (base commutativity and
-- its consequences — exactly what makes the Cayley–Dickson double of a
-- commutative associative algebra associative: ℂ ⇒ ℍ, but not ℍ ⇒ 𝕆) and
-- derives associativity of cd-mul on the sub-complex where at least two of
-- the three arguments lie in the corner subspace inl S ∪ inr S:
--
--   assoc-corner : (x y z : Corner)                       -- 8 cases
--   assocₓ       : (x : join S S) (y z : Corner)           -- + 4 squares
--   assoc-y      : (x : Corner) (y : join S S) (z : Corner)-- + 4 squares
--   assoc-z      : (x y : Corner) (z : join S S)           -- + 4 squares
--
-- (20 of the 27 clauses of the triple join induction — every one a
-- `cong inl/inr` of a base equation or a `push`-square of two of them: the
-- 12 squares reuse the SAME 8 corner paths eq₁…eq₈, which is the
-- consistency condition that makes them assemble.)
--
-- The remaining 7 clauses are stated as explicit types — the six two-push
-- cubes `Cube-xy-L … Cube-yz-R` (one argument at a corner) and the
-- three-push 4-cube `Cube-xyz` — and `AssumingCubes.μ-assoc` assembles the
-- full associator from them, so that
--
--   CDJoin-AssocHSpace : (7 cubes) → (unit-coherence filler) → AssocHSpace CDJoin-HSpace
--
-- is a checked implication. NO inhabitant of any cube type is claimed here
-- (see REFINEMENT-LOG iteration 17 for why they are the genuine content:
-- each two-push cube compares two `pushMulSquare` diamonds — transported
-- images of `genDiamond` at different universal points — and the 4-cube
-- compares cd-mul applied to a diamond against a diamond of cd-mul's).

module CDAssocReduction where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Join using (join ; inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.Homotopy.HSpace using (HSpace ; AssocHSpace)

open import CDJoinBR

private
  variable
    ℓ : Level

module _ {A₀ : Type ℓ} (neg₀ : A₀ → A₀) (L : CDLaws neg₀) where

  open CDLaws L
  open CD neg₀ L

  private
    st : S neg₀ → S neg₀
    st = starS neg₀

    ng : S neg₀ → S neg₀
    ng = negS neg₀

  -- conjugation and negation commute — by cases, all clauses refl
  -- (both are defined by pattern matching on the suspension)
  star-neg : (x : S neg₀) → st (ng x) ≡ ng (st x)
  star-neg north       = refl
  star-neg south       = refl
  star-neg (merid a i) = refl

  -- the extra hypotheses (NOT part of CDLaws): a commutative base.
  -- star-⊗ is the *homomorphism* form, which is what holds when the base
  -- is commutative (in general conjugation is an anti-homomorphism).
  record CDCommLaws : Type ℓ where
    field
      ⊗-comm    : ∀ x y → x ⊗ y ≡ y ⊗ x
      star-⊗    : ∀ x y → st (x ⊗ y) ≡ st x ⊗ st y
      star-star : ∀ x → st (st x) ≡ x
      ⊗-negˡ    : ∀ x y → ng x ⊗ y ≡ ng (x ⊗ y)

  -- the corner subspace inl S ∪ inr S of the join
  data Corner : Type ℓ where
    cl cr : S neg₀ → Corner

  ⌜_⌝ : Corner → join (S neg₀) (S neg₀)
  ⌜ cl a ⌝ = inl a
  ⌜ cr b ⌝ = inr b

  module Reduction (C : CDCommLaws) where
    open CDCommLaws C

    private
      -- x ⊗ (y ⊗ z) ≡ y ⊗ (x ⊗ z)
      swap₁₂ : ∀ x y z → x ⊗ (y ⊗ z) ≡ y ⊗ (x ⊗ z)
      swap₁₂ x y z =
        sym (⊗-assoc x y z) ∙ cong (_⊗ z) (⊗-comm x y) ∙ ⊗-assoc y x z

    -- ——————————————————————————————————————————————————————————
    -- the 8 corner paths (base-level algebra)
    -- ——————————————————————————————————————————————————————————

    eq₁ : ∀ a c e → (a ⊗ c) ⊗ e ≡ a ⊗ (c ⊗ e)
    eq₁ = ⊗-assoc

    eq₂ : ∀ a c f → st (a ⊗ c) ⊗ f ≡ st a ⊗ (st c ⊗ f)
    eq₂ a c f = cong (_⊗ f) (star-⊗ a c) ∙ ⊗-assoc (st a) (st c) f

    eq₃ : ∀ a d e → e ⊗ (st a ⊗ d) ≡ st a ⊗ (e ⊗ d)
    eq₃ a d e = swap₁₂ e (st a) d

    eq₄ : ∀ a d f → ng (f ⊗ st (st a ⊗ d)) ≡ a ⊗ ng (f ⊗ st d)
    eq₄ a d f =
        cong (λ t → ng (f ⊗ t)) (star-⊗ (st a) d ∙ cong (_⊗ st d) (star-star a))
      ∙ cong ng (swap₁₂ f a (st d))
      ∙ sym (⊗-negʳ a (f ⊗ st d))

    eq₅ : ∀ b c e → e ⊗ (c ⊗ b) ≡ (c ⊗ e) ⊗ b
    eq₅ b c e = swap₁₂ e c b ∙ sym (⊗-assoc c e b)

    eq₆ : ∀ b c f → ng (f ⊗ st (c ⊗ b)) ≡ ng ((st c ⊗ f) ⊗ st b)
    eq₆ b c f =
      cong ng ( cong (f ⊗_) (star-⊗ c b)
              ∙ swap₁₂ f (st c) (st b)
              ∙ sym (⊗-assoc (st c) f (st b)))

    eq₇ : ∀ b d e → ng (d ⊗ st b) ⊗ e ≡ ng ((e ⊗ d) ⊗ st b)
    eq₇ b d e =
        ⊗-negˡ (d ⊗ st b) e
      ∙ cong ng ( ⊗-assoc d (st b) e
                ∙ cong (d ⊗_) (⊗-comm (st b) e)
                ∙ swap₁₂ d e (st b)
                ∙ sym (⊗-assoc e d (st b)))

    eq₈ : ∀ b d f → st (ng (d ⊗ st b)) ⊗ f ≡ ng (f ⊗ st d) ⊗ b
    eq₈ b d f =
        cong (_⊗ f) (star-neg (d ⊗ st b))
      ∙ ⊗-negˡ (st (d ⊗ st b)) f
      ∙ cong ng ( cong (_⊗ f) (star-⊗ d (st b) ∙ cong (st d ⊗_) (star-star b))
                ∙ ⊗-assoc (st d) b f
                ∙ cong (st d ⊗_) (⊗-comm b f)
                ∙ sym (⊗-assoc (st d) f b)
                ∙ cong (_⊗ b) (⊗-comm (st d) f))
      ∙ sym (⊗-negˡ (f ⊗ st d) b)

    -- ——————————————————————————————————————————————————————————
    -- associativity on corners (8 clauses)
    -- ——————————————————————————————————————————————————————————

    assoc-corner : (x y z : Corner)
      → cd-mul (cd-mul ⌜ x ⌝ ⌜ y ⌝) ⌜ z ⌝ ≡ cd-mul ⌜ x ⌝ (cd-mul ⌜ y ⌝ ⌜ z ⌝)
    assoc-corner (cl a) (cl c) (cl e) = cong inl (eq₁ a c e)
    assoc-corner (cl a) (cl c) (cr f) = cong inr (eq₂ a c f)
    assoc-corner (cl a) (cr d) (cl e) = cong inr (eq₃ a d e)
    assoc-corner (cl a) (cr d) (cr f) = cong inl (eq₄ a d f)
    assoc-corner (cr b) (cl c) (cl e) = cong inr (eq₅ b c e)
    assoc-corner (cr b) (cl c) (cr f) = cong inl (eq₆ b c f)
    assoc-corner (cr b) (cr d) (cl e) = cong inl (eq₇ b d e)
    assoc-corner (cr b) (cr d) (cr f) = cong inr (eq₈ b d f)

    -- ——————————————————————————————————————————————————————————
    -- one argument free, the other two at corners (3 × 4 squares)
    -- ——————————————————————————————————————————————————————————

    assocₓ : (x : join (S neg₀) (S neg₀)) (y z : Corner)
      → cd-mul (cd-mul x ⌜ y ⌝) ⌜ z ⌝ ≡ cd-mul x (cd-mul ⌜ y ⌝ ⌜ z ⌝)
    assocₓ (inl a)      y z = assoc-corner (cl a) y z
    assocₓ (inr b)      y z = assoc-corner (cr b) y z
    assocₓ (push a b i) (cl c) (cl e) k = push (eq₁ a c e k) (eq₅ b c e k) i
    assocₓ (push a b i) (cl c) (cr f) k = push (eq₆ b c f k) (eq₂ a c f k) (~ i)
    assocₓ (push a b i) (cr d) (cl e) k = push (eq₇ b d e k) (eq₃ a d e k) (~ i)
    assocₓ (push a b i) (cr d) (cr f) k = push (eq₄ a d f k) (eq₈ b d f k) i

    assoc-y : (x : Corner) (y : join (S neg₀) (S neg₀)) (z : Corner)
      → cd-mul (cd-mul ⌜ x ⌝ y) ⌜ z ⌝ ≡ cd-mul ⌜ x ⌝ (cd-mul y ⌜ z ⌝)
    assoc-y x (inl c)      z = assoc-corner x (cl c) z
    assoc-y x (inr d)      z = assoc-corner x (cr d) z
    assoc-y (cl a) (push c d j) (cl e) k = push (eq₁ a c e k) (eq₃ a d e k) j
    assoc-y (cl a) (push c d j) (cr f) k = push (eq₄ a d f k) (eq₂ a c f k) (~ j)
    assoc-y (cr b) (push c d j) (cl e) k = push (eq₇ b d e k) (eq₅ b c e k) (~ j)
    assoc-y (cr b) (push c d j) (cr f) k = push (eq₆ b c f k) (eq₈ b d f k) j

    assoc-z : (x y : Corner) (z : join (S neg₀) (S neg₀))
      → cd-mul (cd-mul ⌜ x ⌝ ⌜ y ⌝) z ≡ cd-mul ⌜ x ⌝ (cd-mul ⌜ y ⌝ z)
    assoc-z x y (inl e)      = assoc-corner x y (cl e)
    assoc-z x y (inr f)      = assoc-corner x y (cr f)
    assoc-z (cl a) (cl c) (push e f k) k' = push (eq₁ a c e k') (eq₂ a c f k') k
    assoc-z (cl a) (cr d) (push e f k) k' = push (eq₄ a d f k') (eq₃ a d e k') (~ k)
    assoc-z (cr b) (cl c) (push e f k) k' = push (eq₆ b c f k') (eq₅ b c e k') (~ k)
    assoc-z (cr b) (cr d) (push e f k) k' = push (eq₇ b d e k') (eq₈ b d f k') k

    -- ——————————————————————————————————————————————————————————
    -- THE OPEN CONTENT: the six two-push cubes …
    -- (boundaries = the squares above; NO inhabitants claimed)
    -- ——————————————————————————————————————————————————————————

    private
      J₂ = join (S neg₀) (S neg₀)

    Cube-xy-L-at : (a b c d e : S neg₀) → Type ℓ
    Cube-xy-L-at a b c d e =
        PathP (λ i → PathP (λ j → cd-mul (cd-mul (push a b i) (push c d j)) (inl e)
                                 ≡ cd-mul (push a b i) (cd-mul (push c d j) (inl e)))
                            (assocₓ (push a b i) (cl c) (cl e))
                            (assocₓ (push a b i) (cr d) (cl e)))
              (λ j → assoc-y (cl a) (push c d j) (cl e))
              (λ j → assoc-y (cr b) (push c d j) (cl e))

    Cube-xy-L : Type ℓ
    Cube-xy-L = ∀ a b c d e → Cube-xy-L-at a b c d e

    Cube-xy-R-at : (a b c d f : S neg₀) → Type ℓ
    Cube-xy-R-at a b c d f =
        PathP (λ i → PathP (λ j → cd-mul (cd-mul (push a b i) (push c d j)) (inr f)
                                 ≡ cd-mul (push a b i) (cd-mul (push c d j) (inr f)))
                            (assocₓ (push a b i) (cl c) (cr f))
                            (assocₓ (push a b i) (cr d) (cr f)))
              (λ j → assoc-y (cl a) (push c d j) (cr f))
              (λ j → assoc-y (cr b) (push c d j) (cr f))

    Cube-xy-R : Type ℓ
    Cube-xy-R = ∀ a b c d f → Cube-xy-R-at a b c d f

    Cube-xz-L-at : (a b c e f : S neg₀) → Type ℓ
    Cube-xz-L-at a b c e f =
        PathP (λ i → PathP (λ k → cd-mul (cd-mul (push a b i) (inl c)) (push e f k)
                                 ≡ cd-mul (push a b i) (cd-mul (inl c) (push e f k)))
                            (assocₓ (push a b i) (cl c) (cl e))
                            (assocₓ (push a b i) (cl c) (cr f)))
              (λ k → assoc-z (cl a) (cl c) (push e f k))
              (λ k → assoc-z (cr b) (cl c) (push e f k))

    Cube-xz-L : Type ℓ
    Cube-xz-L = ∀ a b c e f → Cube-xz-L-at a b c e f

    Cube-xz-R-at : (a b d e f : S neg₀) → Type ℓ
    Cube-xz-R-at a b d e f =
        PathP (λ i → PathP (λ k → cd-mul (cd-mul (push a b i) (inr d)) (push e f k)
                                 ≡ cd-mul (push a b i) (cd-mul (inr d) (push e f k)))
                            (assocₓ (push a b i) (cr d) (cl e))
                            (assocₓ (push a b i) (cr d) (cr f)))
              (λ k → assoc-z (cl a) (cr d) (push e f k))
              (λ k → assoc-z (cr b) (cr d) (push e f k))

    Cube-xz-R : Type ℓ
    Cube-xz-R = ∀ a b d e f → Cube-xz-R-at a b d e f

    Cube-yz-L-at : (a c d e f : S neg₀) → Type ℓ
    Cube-yz-L-at a c d e f =
        PathP (λ j → PathP (λ k → cd-mul (cd-mul (inl a) (push c d j)) (push e f k)
                                 ≡ cd-mul (inl a) (cd-mul (push c d j) (push e f k)))
                            (assoc-y (cl a) (push c d j) (cl e))
                            (assoc-y (cl a) (push c d j) (cr f)))
              (λ k → assoc-z (cl a) (cl c) (push e f k))
              (λ k → assoc-z (cl a) (cr d) (push e f k))

    Cube-yz-L : Type ℓ
    Cube-yz-L = ∀ a c d e f → Cube-yz-L-at a c d e f

    Cube-yz-R-at : (b c d e f : S neg₀) → Type ℓ
    Cube-yz-R-at b c d e f =
        PathP (λ j → PathP (λ k → cd-mul (cd-mul (inr b) (push c d j)) (push e f k)
                                 ≡ cd-mul (inr b) (cd-mul (push c d j) (push e f k)))
                            (assoc-y (cr b) (push c d j) (cl e))
                            (assoc-y (cr b) (push c d j) (cr f)))
              (λ k → assoc-z (cr b) (cl c) (push e f k))
              (λ k → assoc-z (cr b) (cr d) (push e f k))

    Cube-yz-R : Type ℓ
    Cube-yz-R = ∀ b c d e f → Cube-yz-R-at b c d e f

    -- … and, given those, the three-push 4-cube, whose six faces they are
    module _ (cxyL : Cube-xy-L) (cxyR : Cube-xy-R)
             (cxzL : Cube-xz-L) (cxzR : Cube-xz-R)
             (cyzL : Cube-yz-L) (cyzR : Cube-yz-R) where

      Cube-xyz-at : (a b c d e f : S neg₀) → Type ℓ
      Cube-xyz-at a b c d e f =
          PathP (λ i → PathP (λ j → PathP (λ k →
                     cd-mul (cd-mul (push a b i) (push c d j)) (push e f k)
                   ≡ cd-mul (push a b i) (cd-mul (push c d j) (push e f k)))
                   (cxyL a b c d e i j) (cxyR a b c d f i j))
                 (λ k → cxzL a b c e f i k) (λ k → cxzR a b d e f i k))
                (λ j k → cyzL a c d e f j k) (λ j k → cyzR b c d e f j k)

      Cube-xyz : Type ℓ
      Cube-xyz = ∀ a b c d e f → Cube-xyz-at a b c d e f

      -- ————————————————————————————————————————————————————————
      -- assembling the full associator (the 27-clause join induction)
      -- ————————————————————————————————————————————————————————
      module AssumingCubes (cxyz : Cube-xyz) where

        μ-assoc : (x y z : J₂) → cd-mul (cd-mul x y) z ≡ cd-mul x (cd-mul y z)
        -- corners (8)
        μ-assoc (inl a) (inl c) (inl e) = assoc-corner (cl a) (cl c) (cl e)
        μ-assoc (inl a) (inl c) (inr f) = assoc-corner (cl a) (cl c) (cr f)
        μ-assoc (inl a) (inr d) (inl e) = assoc-corner (cl a) (cr d) (cl e)
        μ-assoc (inl a) (inr d) (inr f) = assoc-corner (cl a) (cr d) (cr f)
        μ-assoc (inr b) (inl c) (inl e) = assoc-corner (cr b) (cl c) (cl e)
        μ-assoc (inr b) (inl c) (inr f) = assoc-corner (cr b) (cl c) (cr f)
        μ-assoc (inr b) (inr d) (inl e) = assoc-corner (cr b) (cr d) (cl e)
        μ-assoc (inr b) (inr d) (inr f) = assoc-corner (cr b) (cr d) (cr f)
        -- one push (12)
        μ-assoc (push a b i) (inl c) (inl e) = assocₓ (push a b i) (cl c) (cl e)
        μ-assoc (push a b i) (inl c) (inr f) = assocₓ (push a b i) (cl c) (cr f)
        μ-assoc (push a b i) (inr d) (inl e) = assocₓ (push a b i) (cr d) (cl e)
        μ-assoc (push a b i) (inr d) (inr f) = assocₓ (push a b i) (cr d) (cr f)
        μ-assoc (inl a) (push c d j) (inl e) = assoc-y (cl a) (push c d j) (cl e)
        μ-assoc (inl a) (push c d j) (inr f) = assoc-y (cl a) (push c d j) (cr f)
        μ-assoc (inr b) (push c d j) (inl e) = assoc-y (cr b) (push c d j) (cl e)
        μ-assoc (inr b) (push c d j) (inr f) = assoc-y (cr b) (push c d j) (cr f)
        μ-assoc (inl a) (inl c) (push e f k) = assoc-z (cl a) (cl c) (push e f k)
        μ-assoc (inl a) (inr d) (push e f k) = assoc-z (cl a) (cr d) (push e f k)
        μ-assoc (inr b) (inl c) (push e f k) = assoc-z (cr b) (cl c) (push e f k)
        μ-assoc (inr b) (inr d) (push e f k) = assoc-z (cr b) (cr d) (push e f k)
        -- two pushes (6)
        μ-assoc (push a b i) (push c d j) (inl e) = cxyL a b c d e i j
        μ-assoc (push a b i) (push c d j) (inr f) = cxyR a b c d f i j
        μ-assoc (push a b i) (inl c) (push e f k) = cxzL a b c e f i k
        μ-assoc (push a b i) (inr d) (push e f k) = cxzR a b d e f i k
        μ-assoc (inl a) (push c d j) (push e f k) = cyzL a c d e f j k
        μ-assoc (inr b) (push c d j) (push e f k) = cyzR b c d e f j k
        -- three pushes (1)
        μ-assoc (push a b i) (push c d j) (push e f k) = cxyz a b c d e f i j k

        -- the unit-coherence of the associator (AssocHSpace.μ-assoc-filler)
        Filler-at : (y z : J₂) → Type ℓ
        Filler-at y z =
          PathP (λ i → cd-mul (cd-unitˡ y i) z ≡ cd-unitˡ (cd-mul y z) i)
                (μ-assoc (inl (oneS neg₀)) y z) refl

        Filler : Type ℓ
        Filler = ∀ y z → Filler-at y z

        -- THE IMPLICATION: 7 cubes + filler ⇒ the S³-level AssocHSpace
        CDJoin-AssocHSpace : Filler → AssocHSpace CDJoin-HSpace
        AssocHSpace.μ-assoc        (CDJoin-AssocHSpace fl) = μ-assoc
        AssocHSpace.μ-assoc-filler (CDJoin-AssocHSpace fl) = fl
