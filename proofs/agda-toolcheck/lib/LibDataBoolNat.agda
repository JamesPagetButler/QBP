{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}
-- TOOLCHECK lib/LibDataBoolNat — Cubical.Data.Bool and Cubical.Data.Nat.
-- Pins: Bool, true, false, not (the imaginaroid A₀ = Bool, neg₀ = not of
-- CDLawsBool.agda); ℕ, zero, suc (sphere indices).
-- Used by QBP: CDLawsBool.agda, CDAssocBool.agda, S3FromCD.agda, CDAssocCubesStatus.agda,
-- SkyrmionCharge.agda.
module LibDataBoolNat where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; not)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

_ : Type₀
_ = Bool

_ : Bool → Bool
_ = not

not-not : (b : Bool) → not (not b) ≡ b
not-not true  = refl
not-not false = refl

_ : Type₀
_ = ℕ

_ : ℕ → ℕ
_ = suc

three : ℕ
three = suc (suc (suc zero))
