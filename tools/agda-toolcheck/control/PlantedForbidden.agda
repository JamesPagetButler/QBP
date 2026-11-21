{-# OPTIONS --cubical --safe --type-in-type #-}
-- CONTROL FIXTURE for forbidden_tokens.sh (Red Team F3c). Never type-checked:
-- run.sh scans it and REQUIRES exactly PLANTED hits (the scan is raw text,
-- so every planted name counts once per line it appears on). Too few = the
-- scan has gone blind; too many = it flags the decoys.
--
-- PLANTED: 9
--   line 1 flag · four pragmas below · a let-bound axiom · an axiom block ·
--   the two trusted primitives · a hole
--
-- Decoys that must NOT be hit: the identifiers `postulated` and
-- `rewriting-free` (whole-word matching), and `--safe`.
module PlantedForbidden where

data ⊥ : Set where

postulated : Set
postulated = Set

rewriting-free : Set
rewriting-free = Set

{-# TERMINATING #-}
loop : ⊥
loop = loop

{-# NO_POSITIVITY_CHECK #-}
data Bad : Set where
  bad : (Bad → ⊥) → Bad

{-# REWRITE loop #-}

bad₁ : ⊥
bad₁ = let postulate p : ⊥ in p

postulate
  bad₂ : ⊥

trust : ⊥
trust = primTrustMe

erase : ⊥
erase = primEraseEquality

hole : ⊥
hole = {!!}
