{-# OPTIONS --cubical --safe --no-import-sorts --guardedness -WnoUnsupportedIndexedMatch #-}
-- TOOLCHECK tool/LibFlags — the library tree's exact flag string.
--
-- Feature: the OPTIONS pragma every proofs/agda-cubical/*.agda file carries,
-- `--cubical --safe --no-import-sorts --guardedness` (qbp-cubical.agda-lib),
-- plus the warning flag agda/cubical's own cubical.agda-lib adds
-- (`-WnoUnsupportedIndexedMatch`), all accepted together. Under
-- `--no-import-sorts` the sorts are NOT in scope until imported, so this file
-- must (and does) `open import Agda.Primitive using (Set)`.
--
-- Used by QBP: all 13 proofs/agda-cubical/*.agda files; .github/workflows/agda-cubical.yml.
module LibFlags where

open import Agda.Primitive using (Set; Level)
open import Agda.Builtin.Cubical.Path using (_≡_)

private variable
  ℓ : Level
  A : Set ℓ

refl : {x : A} → x ≡ x
refl {x = x} = λ _ → x

data Unit : Set where
  tt : Unit

unit-unique : (u : Unit) → u ≡ tt
unit-unique tt = refl
