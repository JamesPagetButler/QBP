{-# OPTIONS --cubical --safe #-}
-- MUSTFAIL: an interaction hole `?` left in the file.
-- A hole is an unproved goal; batch-mode `agda` must report it as an error
-- (unsolved interaction meta) and exit non-zero, so a file with holes can
-- never pass CI. (`{!!}` is the same construct in the other spelling.)
-- EXPECT: Unsolved interaction metas
module Hole where

open import Agda.Builtin.Nat using (Nat; zero; suc)

answer : Nat
answer = ?
