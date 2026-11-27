{-# OPTIONS --cubical --safe #-}
-- MUSTFAIL: a claimed path between two DISTINCT points.
-- `λ _ → true` has type `true ≡ true`; ascribing it `true ≡ false` must fail
-- the endpoint (boundary) check at i1. This is the control for the #472-class
-- vacuity: a path type's endpoints are checked definitionally, so a "proof"
-- of a false equation cannot slip through as a constant path.
-- EXPECT: UnequalTerms
module BadPath where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Cubical.Path using (_≡_)

bad : true ≡ false
bad = λ _ → true
