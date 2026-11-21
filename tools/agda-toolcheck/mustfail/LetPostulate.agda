{-# OPTIONS --cubical --safe #-}
-- MUSTFAIL-KNOWN-HOLE: a `postulate` hidden inside a `let`, under --safe.
-- agda/agda issue 8341 ("Postulates in safe mode", a regression in 2.8.0,
-- closed by agda/agda PR 8340 and shipped in Agda 2.9.0): Agda 2.8.0 ACCEPTS
-- this file, i.e. the --safe gate has a hole on the current pin.
--
-- The hole is keyed to the Agda version (Red Team F2). From the issue and
-- the fix PR (agda/agda PR 8340, merged 2026-01-27, milestone 2.9.0):
--   AFFECTED: 2.8.0 2.8.0.1 2.8.0.2
--   FIXED-IN: 2.9.0
-- The runner reads FIXED-IN and grades:
--   * Agda  < FIXED-IN, accepted → KNOWN-HOLE (reported, not a suite failure;
--                 the lexical control forbidden_tokens.sh covers the gap for
--                 every CI-gated QBP file);
--   * Agda  < FIXED-IN, rejected → FIXED-EARLY (not a failure; update FIXED-IN);
--   * Agda >= FIXED-IN, rejected with EXPECT → FIXED;
--   * Agda >= FIXED-IN, accepted → ACCEPTED = SUITE FAILURE (a regression).
-- EXPECT: postulate
module LetPostulate where

data ⊥ : Set where

bad : ⊥
bad = let postulate p : ⊥ in p
