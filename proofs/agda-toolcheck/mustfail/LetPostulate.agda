{-# OPTIONS --cubical --safe #-}
-- MUSTFAIL-KNOWN-HOLE: a `postulate` hidden inside a `let`, under --safe.
-- agda/agda issue 8341 ("Postulates in safe mode", a regression in 2.8.0,
-- closed by agda/agda PR 8340 and shipped in Agda 2.9.0): Agda 2.8.0 ACCEPTS
-- this file, i.e. the --safe gate has a hole on the current pin.
--
-- The runner treats a KNOWN-HOLE file specially:
--   * accepted  → status KNOWN-HOLE (reported, not a suite failure; the
--                 lexical control `no-postulate-token` in run.sh covers the
--                 gap for every CI-gated QBP file);
--   * rejected  → status FIXED (the pin has moved past the fix; promote this
--                 file to a plain MUSTFAIL and update FEATURES.md).
-- EXPECT: postulate
module LetPostulate where

data ⊥ : Set where

bad : ⊥
bad = let postulate p : ⊥ in p
