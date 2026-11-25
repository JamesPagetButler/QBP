{-# OPTIONS --cubical --safe #-}
-- CONTROL FIXTURE B2 (PR #826 Red Team bypass of a comment-aware scanner):
-- the identifier `a--b` is read as the start of a line comment by a naive
-- `--` stripper, hiding the forbidden declaration later on the same line.
-- Raw-text scanning must still flag it. Never type-checked.
-- PLANTED: 1
module B2IdentifierDashDash where

open import Agda.Builtin.Unit using (⊤; tt)

data ⊥ : Set where

bad : ⊥
bad = let a--b = tt ; postulate p : ⊥ in p
