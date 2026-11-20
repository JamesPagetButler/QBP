{-# OPTIONS --cubical --safe #-}
-- MUSTFAIL: a top-level `postulate` under --safe.
-- This is the Agda analogue of Lean's `sorry`: it asserts inhabitation
-- without a proof. `--safe` must reject it, and because `--safe` is
-- transitive, a green check of any QBP file certifies its whole import
-- closure free of this.
-- EXPECT: Cannot postulate
module Postulate where

postulate
  bad : Set
