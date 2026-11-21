{-# OPTIONS --cubical --safe #-}
-- MUSTFAIL: `{-# TERMINATING #-}` under --safe.
-- The pragma tells the checker to trust a recursion it cannot verify; with
-- it, `loop : ⊥` would be accepted. `--safe` must refuse the pragma itself.
-- EXPECT: TERMINATING
module Terminating where

data ⊥ : Set where

{-# TERMINATING #-}
loop : ⊥
loop = loop
