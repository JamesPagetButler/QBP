{-# OPTIONS --cubical --safe #-}
------------------------------------------------------------------------
-- QBP substrate — first executable Cubical Agda brick.
--
-- Context: the #560 substrate resolution named the cubical/computing axis
-- (Buchholtz–Rijke, synthetic S¹/S³ HITs) as the foundation the QBP substrate
-- needs, and #573 flagged the substrate as "non-concrete." This file makes a
-- first piece concrete and machine-checkable: function extensionality from
-- cubical paths, and the circle S¹ as a Higher Inductive Type (the base of the
-- Cayley–Dickson-in-HoTT tower). It uses ONLY Agda's builtin cubical
-- primitives (no external library), so the CI type-check is light.
--
-- The type-check (CI: `agda --safe`) IS the executable-binary verification.
------------------------------------------------------------------------
module QBPSubstrate where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Cubical.Path using (_≡_)

private
  variable
    ℓ ℓ′ : Level
    A : Set ℓ
    B : Set ℓ′

-- Reflexivity: the constant path.
refl-path : {x : A} → x ≡ x
refl-path {x = x} = λ _ → x

-- Function extensionality — the canonical "why cubical" result: pointwise
-- equal functions are equal. A one-liner from paths; not provable in plain MLTT.
funext : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funext p = λ i x → p x i

-- congruence of a function over a path.
cong-path : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong-path f p = λ i → f (p i)

-- The circle S¹ as a Higher Inductive Type (the ℂ-level Hopf circle; the base
-- of the Buchholtz–Rijke CD-in-HoTT tower). Expressible ONLY in cubical/HoTT:
-- a point `base` plus a non-trivial path `loop : base ≡ base`.
data S¹ : Set where
  base : S¹
  loop : base ≡ base

-- A genuine S¹ map: the "double" map sending loop to loop ∙ loop would need
-- path composition; here the minimal checkable fact is the recursor's action —
-- any (point, loop) target induces a map out of S¹.
S¹-rec : {C : Set ℓ} (b : C) (l : b ≡ b) → S¹ → C
S¹-rec b l base     = b
S¹-rec b l (loop i) = l i

------------------------------------------------------------------------
-- VERIFICATION: machine-checked confirmations that the above DOES WHAT
-- IT CLAIMS. Each `_≡_` proved by `refl-path` is a definitional-computation
-- check — it type-checks IFF the stated computation rule actually holds.
-- Under --safe there are no postulates/holes, so these are genuine proofs,
-- not assertions.
------------------------------------------------------------------------

-- happly: the inverse direction of funext (evaluate a function-path pointwise).
happly : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
happly q x = λ i → q i x

-- funext β-rule: happly ∘ funext ≡ id. Confirms `funext` genuinely IS function
-- extensionality (round-trips), not merely something of the right type.
funext-β : {f g : A → B} (p : (x : A) → f x ≡ g x) → happly (funext p) ≡ p
funext-β p = refl-path

-- cong on refl is refl (functoriality on the trivial path).
cong-refl : (f : A → B) {x : A} → cong-path f (refl-path {x = x}) ≡ refl-path
cong-refl f = refl-path

-- S¹ recursor β-rule on the point constructor.
S¹-rec-base : {C : Set} (b : C) (l : b ≡ b) → S¹-rec b l base ≡ b
S¹-rec-base b l = refl-path

-- S¹ recursor β-rule on the PATH constructor — the genuine HIT computation rule
-- (this is the part that only exists because S¹ is a real Higher Inductive Type).
S¹-rec-loop : {C : Set} (b : C) (l : b ≡ b) → (λ i → S¹-rec b l (loop i)) ≡ l
S¹-rec-loop b l = refl-path
