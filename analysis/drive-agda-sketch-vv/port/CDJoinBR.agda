{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

-- The Cayley-Dickson join step, BR-faithful — Cubical Agda port of
-- Buchholtz–Rijke's imaginaroid.hlean (leanprover/lean2, Apache 2.0,
-- © 2016 U. Buchholtz, E. Rijke; paper: arXiv:1610.01134 §"imaginaroids").
--
-- Carrier: S = Susp A₀ (the carrier MUST be a suspension — the final
-- suspension induction in `genDiamond` is what closes the coherence square;
-- this is the deep reason the earlier abstract-CDStr attempt could not
-- close it on an arbitrary carrier).
-- Negation swaps the poles; conjugation fixes the poles and negates
-- meridians — both definable by pattern matching, which dissolves the
-- S¹-negation obstruction found in MulProbe.agda.
--
-- Given the imaginaroid laws + associativity on S, `join S S` is an H-space:
--   (a,b)·(c,d) = (a·c − d·b*, a*·d + c·b)   [spherical form]
--
-- Deviations from BR (noted per the V&V discipline):
--  * BR derive norm' (x*·x=1) from star_mul/star_star; we take normˡ as a
--    field (at instantiation both norms come directly from rotInv laws).
--  * The cubical HSpace record needs the unit-law coherence μₗᵣ; BR's
--    h_space does not have it, so we add the field ⊗-unit-coh.

module CDJoinBR where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed using (Pointed ; typ ; pt)
open import Cubical.HITs.Join using (join ; inl ; inr ; push)
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.Homotopy.HSpace using (HSpace)

open import Diamond

private
  variable
    ℓ : Level

module _ {A₀ : Type ℓ} (neg₀ : A₀ → A₀) where

  S : Type ℓ
  S = Susp A₀

  oneS : S
  oneS = north

  -- negation: swap the poles (−1 = south), reverse negated meridians
  negS : S → S
  negS north       = south
  negS south       = north
  negS (merid a i) = sym (merid (neg₀ a)) i

  -- conjugation: fix the poles, negate meridians
  starS : S → S
  starS north       = north
  starS south       = south
  starS (merid a i) = merid (neg₀ a) i

  -- the imaginaroid laws (BR imaginaroid + assoc, adapted per header note)
  record CDLaws : Type ℓ where
    field
      _⊗_        : S → S → S
      ⊗-unitˡ    : ∀ x → oneS ⊗ x ≡ x
      ⊗-unitʳ    : ∀ x → x ⊗ oneS ≡ x
      ⊗-unit-coh : ⊗-unitˡ oneS ≡ ⊗-unitʳ oneS
      ⊗-negʳ     : ∀ x y → x ⊗ negS y ≡ negS (x ⊗ y)
      normʳ      : ∀ x → x ⊗ starS x ≡ oneS
      normˡ      : ∀ x → starS x ⊗ x ≡ oneS
      ⊗-assoc    : ∀ x y z → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)

  module CD (L : CDLaws) where
    open CDLaws L

    private
      -- BR's two corner maps and the single generalized point
      f : (a c : S) → S → S
      f a c x = (a ⊗ c) ⊗ negS x

      g : (b c : S) → S → S
      g b c y = (c ⊗ y) ⊗ b

      w : (a b c d : S) → S
      w a b c d = ((starS c ⊗ starS a) ⊗ d) ⊗ starS b

    -- BR lemma 1:  f(−1) = a·c   (negS (negS oneS) = oneS definitionally)
    lemma₁ : ∀ a c → f a c (negS oneS) ≡ a ⊗ c
    lemma₁ a c = ⊗-unitʳ (a ⊗ c)

    -- BR lemma 2:  f(w) = −(d·b*)
    lemma₂ : ∀ a b c d → f a c (w a b c d) ≡ negS (d ⊗ starS b)
    lemma₂ a b c d =
        ⊗-negʳ (a ⊗ c) (w a b c d)
      ∙ cong negS
          ( sym (⊗-assoc (a ⊗ c) ((starS c ⊗ starS a) ⊗ d) (starS b))
          ∙ cong (_⊗ starS b)
              ( sym (⊗-assoc (a ⊗ c) (starS c ⊗ starS a) d)
              ∙ cong (_⊗ d)
                  ( sym (⊗-assoc (a ⊗ c) (starS c) (starS a))
                  ∙ cong (_⊗ starS a) (⊗-assoc a c (starS c))
                  ∙ cong (λ t → (a ⊗ t) ⊗ starS a) (normʳ c)
                  ∙ cong (_⊗ starS a) (⊗-unitʳ a)
                  ∙ normʳ a)
              ∙ ⊗-unitˡ d))

    -- BR lemma 3:  g(1) = c·b
    lemma₃ : ∀ b c → g b c oneS ≡ c ⊗ b
    lemma₃ b c = cong (_⊗ b) (⊗-unitʳ c)

    -- BR lemma 4:  g(w) = a*·d
    lemma₄ : ∀ a b c d → g b c (w a b c d) ≡ starS a ⊗ d
    lemma₄ a b c d =
        cong (_⊗ b)
          ( sym (⊗-assoc c ((starS c ⊗ starS a) ⊗ d) (starS b))
          ∙ cong (_⊗ starS b)
              ( sym (⊗-assoc c (starS c ⊗ starS a) d)
              ∙ cong (_⊗ d)
                  ( sym (⊗-assoc c (starS c) (starS a))
                  ∙ cong (_⊗ starS a) (normʳ c)
                  ∙ ⊗-unitˡ (starS a))))
      ∙ ⊗-assoc (starS a ⊗ d) (starS b) b
      ∙ cong ((starS a ⊗ d) ⊗_) (normˡ b)
      ∙ ⊗-unitʳ (starS a ⊗ d)

    -- THE universal one-variable diamond — closed by suspension induction:
    -- poles are degenerate, the meridian is twistDiamond. This is the step
    -- that requires the carrier to be a suspension.
    genDiamond : (x : S) → diamond {A = S} {B = S} (negS oneS) x oneS x
    genDiamond north       = vdiamond south north refl
    genDiamond south       = hdiamond north south refl
    genDiamond (merid a i) = twistDiamond (merid a) i

    -- the coherence square that resisted 7 direct attempts, now a transport
    -- of the image of the universal diamond (BR's cd_mul glue-glue case)
    pushMulSquare : ∀ a b c d
      → diamond (a ⊗ c) (negS (d ⊗ starS b)) (c ⊗ b) (starS a ⊗ d)
    pushMulSquare a b c d =
      transport
        (λ i → diamond (lemma₁ a c i) (lemma₂ a b c d i)
                       (lemma₃ b c i) (lemma₄ a b c d i))
        (apDiamond (f a c) (g b c) (genDiamond (w a b c d)))

    -- the Cayley-Dickson multiplication on join S S (BR cd_mul)
    cd-mul : join S S → join S S → join S S
    cd-mul (inl a)      (inl c)      = inl (a ⊗ c)
    cd-mul (inl a)      (inr d)      = inr (starS a ⊗ d)
    cd-mul (inl a)      (push c d j) = push (a ⊗ c) (starS a ⊗ d) j
    cd-mul (inr b)      (inl c)      = inr (c ⊗ b)
    cd-mul (inr b)      (inr d)      = inl (negS (d ⊗ starS b))
    cd-mul (inr b)      (push c d j) =
      sym (push (negS (d ⊗ starS b)) (c ⊗ b)) j
    cd-mul (push a b i) (inl c)      = push (a ⊗ c) (c ⊗ b) i
    cd-mul (push a b i) (inr d)      =
      sym (push (negS (d ⊗ starS b)) (starS a ⊗ d)) i
    cd-mul (push a b i) (push c d j) = pushMulSquare a b c d j i

    -- unit laws (BR cd_one_mul / cd_mul_one; the push cases are one-line
    -- squares because push is a binary constructor)
    cd-unitˡ : ∀ z → cd-mul (inl oneS) z ≡ z
    cd-unitˡ (inl c)      = cong inl (⊗-unitˡ c)
    cd-unitˡ (inr d)      = cong inr (⊗-unitˡ d)
    cd-unitˡ (push c d j) = λ k → push (⊗-unitˡ c k) (⊗-unitˡ d k) j

    cd-unitʳ : ∀ z → cd-mul z (inl oneS) ≡ z
    cd-unitʳ (inl a)      = cong inl (⊗-unitʳ a)
    cd-unitʳ (inr b)      = cong inr (⊗-unitˡ b)
    cd-unitʳ (push a b i) = λ k → push (⊗-unitʳ a k) (⊗-unitˡ b k) i

    -- the payoff: join S S is an H-space
    CDJoin-HSpace : HSpace (join S S , inl oneS)
    HSpace.μ   CDJoin-HSpace = cd-mul
    HSpace.μₗ  CDJoin-HSpace = cd-unitˡ
    HSpace.μᵣ  CDJoin-HSpace = cd-unitʳ
    HSpace.μₗᵣ CDJoin-HSpace = cong (cong inl) ⊗-unit-coh
