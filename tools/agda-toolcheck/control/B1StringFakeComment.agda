{-# OPTIONS --cubical --safe #-}
-- CONTROL FIXTURE B1 (PR #826 Red Team bypass of a comment-aware scanner):
-- a string literal opens a fake block comment, so a lexer that tracks
-- `{-` … `-}` skips the forbidden declaration two lines later. Raw-text
-- scanning must still flag it. Never type-checked.
-- PLANTED: 1
module B1StringFakeComment where

open import Agda.Builtin.String using (String)

data ⊥ : Set where

s : String
s = "{-"

bad : ⊥
bad = let postulate p : ⊥ in p

t : String
t = "-}"
