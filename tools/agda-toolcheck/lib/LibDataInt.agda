{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibDataInt — Cubical.Data.Int and .Int.Properties.
-- Pins: ℤ, pos, negsuc, -_, _+_ (renamed _+ℤ_ as SkyrmionCharge does), +Comm, isSetℤ.
-- The charge values of SkyrmionCharge.agda are pinned to these constructors
-- (pos 1, pos 0, negsuc 0), so their shape is load-bearing.
-- Used by QBP: SkyrmionCharge.agda, SubstrateCharge.agda.
module LibDataInt where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; -_ ; +Comm) renaming (_+_ to _+ℤ_)
open import Cubical.Data.Int.Properties using (isSetℤ)
open import Cubical.Data.Nat using (ℕ)

_ : Type₀
_ = ℤ

_ : ℕ → ℤ
_ = pos

_ : ℕ → ℤ
_ = negsuc

_ : ℤ → ℤ
_ = -_

_ : ℤ → ℤ → ℤ
_ = _+ℤ_

_ : (m n : ℤ) → m +ℤ n ≡ n +ℤ m
_ = +Comm

_ : isSet ℤ
_ = isSetℤ

-- the integer literals the charge contracts use, and one computation
one : ℤ
one = pos 1

minus-one : ℤ
minus-one = negsuc 0

neg-one : - one ≡ minus-one
neg-one = refl

one-plus-minus-one : one +ℤ minus-one ≡ pos 0
one-plus-minus-one = refl
