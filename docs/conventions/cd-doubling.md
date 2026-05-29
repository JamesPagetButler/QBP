# Cayley-Dickson Doubling Formula (F3)

**Status:** RATIFIED — qbp-architecture, pr407-conflict-resolution seq=55, 2026-05-29  
**Resolves:** QBP foundations rebuild Phase 0.5, convention question F3  
**Authorised by:** qbp-architecture  
**Author:** qbp-implementor

---

## Canonical formula

Given an algebra A with conjugation (\*), the Cayley-Dickson doubling CD(A) has elements of the form (a₁, a₂) where a₁, a₂ ∈ A. Multiplication is defined as:

```
(a₁, a₂)(b₁, b₂) = (a₁b₁ − conj(b₂)·a₂,  b₂·a₁ + a₂·conj(b₁))
```

In the shorthand notation used throughout QBP prose (where \* denotes conjugation as superscript):

```
(a, b)(c, d) = (ac − d*b,  da + bc*)
```

These are the same formula. The first form makes the asymmetry explicit (conjugate applied to the *right* factor, not the left). The second is the compact form used in Baez (2002) and Furey (2014–2018).

## Conjugation propagation

Conjugation on CD(A) is defined recursively from conjugation on A:

```
conj(a₁, a₂) = (conj(a₁), −a₂)
```

This gives the correct norm: `(a₁,a₂)·conj(a₁,a₂) = (|a₁|² + |a₂|², 0)`.

## Norm propagation

The norm on CD(A) is:

```
|(a₁, a₂)|² = |a₁|² + |a₂|²
```

Norm multiplicativity (`|xy|² = |x|²|y|²`) holds at levels ℝ, ℂ, ℍ, 𝕆 (the four normed division algebras per PROOF-hurwitz). It fails at 𝕊 (Sedenion level) — see PROOF-loss-of-hurwitz-norm-O-to-S.

## Level instantiation

| Level | A | CD(A) | Dimension |
|-------|---|-------|-----------|
| 0 | — | ℝ | 1 |
| 1 | ℝ | ℂ | 2 |
| 2 | ℂ | ℍ | 4 |
| 3 | ℍ | 𝕆 | 8 |
| 4 | 𝕆 | 𝕊 | 16 |
| n | A_{n-1} | A_n | 2ⁿ |

The construction is parametric in level. Levels beyond 𝕊 (pathions at dim 32, chingons at dim 64, etc.) are defined by the same formula and are in scope for QBP if downstream physics requires them.

## Lean implementation

The canonical formula is implemented in `archive/QBP_CayleyDickson_Basic.lean` as `CD.mul`:

```lean
def CD.mul (x y : CD α) : CD α where
  fst := x.fst * y.fst - (star y.snd) * x.snd
  snd := y.snd * x.fst + x.snd * (star y.fst)
```

This matches the canonical formula above with `star` as conjugation. The file also proves `CD.mul_comm_of_comm` for ℂ (commutativity is preserved at level 1) and states commutativity loss at higher levels via `PROOF-loss-of-commutativity-C-to-H`.

The Lean convention for the CD doubling formula is the one above — no deviation is permitted without updating this file.

## Reference

Baez, J.C. (2002). "The Octonions." *Bulletin of the American Mathematical Society* 39(2): 145–205. §1.1, equation immediately following "the Cayley-Dickson construction." [arXiv:math/0105155](https://arxiv.org/abs/math/0105155)

This is the authoritative reference for the QBP programme. Furey (2014–2018) uses the same convention throughout her division algebra + Standard Model programme.

## Change history

| Date | Author | Change |
|------|--------|--------|
| 2026-05-29 | qbp-implementor | v1.0 — initial ratification per F3 architect decision |
