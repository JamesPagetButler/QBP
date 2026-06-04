# Sedenion Basis Indexing Convention (F5)

**Status:** RATIFIED — qbp-architecture, pr407-conflict-resolution seq=55, 2026-05-29  
**Resolves:** QBP foundations rebuild Phase 0.5, convention question F5; QBP #461  
**Authorised by:** qbp-architecture  
**Author:** qbp-implementor

---

## Canonical indexing

The 16 sedenion basis elements are indexed **e₀ through e₁₅**, with:

- **e₀ = 1** — the real unit (multiplicative identity)
- **e₁ through e₁₅** — the 15 imaginary units (each squares to −1)

Indices run from 0 to 15 inclusive (`Nat` values; matches `Fin 16` in Lean).

## Hierarchical structure via iterated Cayley-Dickson doubling

The index ranges reflect the iterated doubling construction (see `docs/conventions/cd-doubling.md`):

| Algebra | Index range | Notes |
|---------|------------|-------|
| ℝ | {0} | e₀ = 1 only |
| ℂ | {0, 1} | e₀ = 1, e₁ = i |
| ℍ | {0, 1, 2, 3} | e₀ = 1, e₁ = i, e₂ = j, e₃ = k |
| 𝕆 | {0, 1, ..., 7} | e₀ = 1, e₁..e₇ imaginary; see `docs/conventions/fano-orientation.md` |
| 𝕊 | {0, 1, ..., 15} | e₀ = 1, e₁..e₁₅ imaginary |

At each CD doubling step, the second copy occupies the upper half of the index range:
- 𝕊 = CD(𝕆): indices 0..7 form the first 𝕆-copy; indices 8..15 form the second 𝕆-copy
- e₈ is the second-copy identity element (the "imaginary unit" that, when paired with e₀, generates 𝕊 from 𝕆)

## Lean correspondence

In `proofs/Sprint12-Inherited/Sedenion.lean`, basis elements are identified by `Fin 16` values 0..15. The correspondence is:

```lean
-- e₀ = (0 : Fin 16) = 1 (identity, confirmed by checkLeftIdentity: mulSign 0 j == 1)
-- e_k = (k : Fin 16) for k ∈ 1..15 (each squares to -1,
--        confirmed by checkSquareMinusOne: (i+1) for i ∈ 0..14)
```

Quaternion subalgebra indices: `{0, 1, 2, 3}` — confirmed in `Quaternion.lean` (`isQuaternionIdx`).

Octonion first-copy indices: `{0, 1, ..., 7}` — confirmed in `QBP_Octonion.lean`.

Octonion second-copy indices: `{8, 9, ..., 15}` — e₈ acts as the second-copy "1", but within 𝕊 it is imaginary (e₈² = −1 as a sedenion element).

## Prose convention

In QBP prose documents, basis elements are written as subscripted e:

- Single elements: e₀, e₁, e₂, ..., e₁₅
- Ranges: e₁..e₇ (octonion imaginaries), e₈..e₁₅ (sedenion second-copy)
- The identity is written as "e₀" or "1" interchangeably; "e₀ = 1" when the identification needs to be explicit

Do not use 1-based indexing (e₁..e₁₆) for sedenions. Do not use mixed conventions where e₀ = i (imaginary). Always: **e₀ is the real unit**.

## Zero divisors

The sedenions contain zero divisors — non-zero elements whose product is zero. This is the defining algebraic break at level 4 and is tracked in `PROOF-42zd` ("42 zero divisors"). The 42 zero divisors exist among the imaginary units e₁..e₁₅; e₀ = 1 is never a zero divisor (it is the identity).

The zero divisor structure depends on the sedenion multiplication table, which is determined by the iterated CD doubling from the octonion multiplication table. The octonion table in turn depends on the Fano orientation (see `docs/conventions/fano-orientation.md`). The sedenion zero divisor count (42) is orientation-independent — it holds for all Fano orientations — but the specific zero divisor pairs depend on the chosen Fano orientation.

## Reference

Baez, J.C. (2002). "The Octonions." *Bull. Amer. Math. Soc.* 39(2):145–205. §1 (Cayley-Dickson construction, level notation).

de Marrais, R. (2000). "The 42 Assessors and the Box-Kite they fly: Diagonal Axis-Pair Systems of Zero-Divisors in the Sedenions' 16 Dimensions." — establishes the 42 zero-divisor structure used in PROOF-42zd and PROOF-hessian.

## Change history

| Date | Author | Change |
|------|--------|--------|
| 2026-05-29 | qbp-implementor | v1.0 — initial ratification per F5 architect decision |
