# Fano Plane Orientation Convention (F4)

**Status:** RATIFIED — qbp-architecture, pr407-conflict-resolution seq=55, 2026-05-29  
**Resolves:** QBP foundations rebuild Phase 0.5, convention question F4; QBP #460  
**Authorised by:** qbp-architecture  
**Author:** qbp-implementor

---

## Canonical orientation

QBP adopts the **Baez/Furey standard orientation** of the Fano plane, matching Baez (2002) Table 1 and used throughout Furey's division algebra + Standard Model programme (2014–2018).

The 7 positive triples (lines of the Fano plane) with their canonical multiplication direction are:

| Triple | Product rule |
|--------|-------------|
| {1, 2, 3} | e₁e₂ = e₃ |
| {1, 4, 5} | e₁e₄ = e₅ |
| {1, 6, 7} | e₁e₆ = e₇ |
| {2, 4, 6} | e₂e₄ = e₆ |
| {2, 5, 7} | e₂e₅ = e₇ |
| {3, 4, 7} | e₃e₄ = e₇ |
| {3, 5, 6} | e₃e₅ = e₆ |

In each triple {a, b, c}, the product eₐeᵦ = eᵧ holds cyclically: eₐeᵦ = eᵧ, eᵦeᵧ = eₐ, eᵧeₐ = eᵦ. The reverse product picks up a sign: eᵦeₐ = −eᵧ.

## Full imaginary multiplication table

The complete 7×7 antisymmetric multiplication table for Im 𝕆 = {e₁, ..., e₇}, where eₐeᵦ is the (a,b) entry:

|   | e₁ | e₂ | e₃ | e₄ | e₅ | e₆ | e₇ |
|---|----|----|----|----|----|----|-----|
| **e₁** | −1 | e₃ | −e₂ | e₅ | −e₄ | e₇ | −e₆ |
| **e₂** | −e₃ | −1 | e₁ | e₆ | e₇ | −e₄ | −e₅ |
| **e₃** | e₂ | −e₁ | −1 | e₇ | −e₆ | e₅ | −e₄ |
| **e₄** | −e₅ | −e₆ | −e₇ | −1 | e₁ | e₂ | e₃ |
| **e₅** | e₄ | −e₇ | e₆ | −e₁ | −1 | −e₃ | e₂ |
| **e₆** | −e₇ | e₄ | −e₅ | −e₂ | e₃ | −1 | e₁ |
| **e₇** | e₆ | e₅ | e₄ | −e₃ | −e₂ | −e₁ | −1 |

Each eₐ² = −1. Off-diagonal entries are read as eₐeᵦ (row a, column b).

The quaternion subalgebra ℍ ⊂ 𝕆 is spanned by {e₀, e₁, e₂, e₃}, where e₁e₂ = e₃ matches the standard quaternion convention i·j = k.

## Fano plane diagram

The Fano plane has 7 points (e₁..e₇) and 7 lines (the 7 triples above). Each line contains 3 points; each point lies on 3 lines. The orientation assigns a cyclic order to each line.

```
        e₁
       / | \
      /  |  \
    e₂---e₄---e₆
    |\ ↗ | ↗ /|
    | ×  |  × |
    |/ ↘ | ↘ \|
    e₃---e₅---e₇
         e₄ (centre)
```

The centre point is e₄. The six outer points connect via the three "diameter" lines {1,4,5}, {2,4,6}, {3,4,7}.

(See Baez 2002 Figure 1 for the standard diagram with directed cycle arrows.)

## Why there are 480 orientations — and why this one

**Group theory.** The Fano plane's automorphism group is the simple group G₂ of order 168 (also written PSL(2,7) = GL(3,2) — the projective special linear group over GF(7)). These 168 automorphisms permute the 7 points while preserving all 7 lines and their incidence structure.

Starting from one signed orientation (choice of cyclic direction for each line), applying any of the 168 automorphisms gives another valid orientation. Additionally, each line's cyclic direction can be independently reversed, but reversing all 7 simultaneously just negates all products (an orientation with all signs flipped is isomorphic via e_k ↦ −e_k). Counting carefully:

- 480 = 168 × (480/168) — all sign-consistent orientations form a set of size 480
- These 480 orientations fall into equivalence classes under G₂ (related by automorphisms of the Fano plane)
- The Baez/Furey orientation is the unique one (up to G₂ automorphism) that gives the "standard" embedding of ℍ ⊂ 𝕆 with {e₁, e₂, e₃} = {i, j, k} and e₁e₂ = e₃

**Why this matters for QBP.** The proof of associativity loss `PROOF-loss-of-associativity-H-to-O` requires a specific non-associative triple as a witness. The witness triple {e₁, e₂, e₄} (satisfying (e₁e₂)e₄ ≠ e₁(e₂e₄) in 𝕆) depends on this orientation. Any of the 480 orientations would give a valid witness, but the witness element changes. This convention pins the witness so proofs are reproducible.

## Lean implementation

The canonical orientation is implemented in `archive/QBP_Octonion.lean` as `FanoLine`, with the comment explicitly identifying this as "the 'common' convention used in most physics literature (matching Baez, Furey, etc.)":

```lean
-- The 7 lines of the Fano plane (positive triples)
def FanoLines : Finset (Fin 7 × Fin 7 × Fin 7) := {
  (0, 1, 2),  -- e₁e₂ = e₃ (indices shifted: 0→1, 1→2, 2→3)
  (0, 3, 4),  -- e₁e₄ = e₅
  ...
}
```

Note: `archive/QBP_Octonion.lean` uses 0-based indexing internally (Fin 7: 0..6 for the 7 imaginary units e₁..e₇). The Lean index k corresponds to eₖ₊₁ in the prose convention.

## Sedenion multiplication table

The sedenion multiplication table is determined by applying the Cayley-Dickson doubling formula to this octonion table. The zero divisor structure (42 zero divisors, per PROOF-42zd) and the box-kite / assessor structure (per PROOF-hessian) are computed from this orientation.

See `docs/conventions/sedenion-indexing.md` for the sedenion index convention.

## Reference

Baez, J.C. (2002). "The Octonions." *Bull. Amer. Math. Soc.* 39(2):145–205. §2.2 Table 1 — the canonical multiplication table. [arXiv:math/0105155](https://arxiv.org/abs/math/0105155)

Furey, C. (2014). "Generations: Three Prints, in Colour." *JHEP* 2014(10):046 — uses this Fano orientation throughout for the Standard Model embedding.

Conway, J.H. and Smith, D.A. (2003). *On Quaternions and Octonions*. A.K. Peters/CRC Press. — comprehensive reference on all 480 orientations and their symmetry structure.

## Change history

| Date | Author | Change |
|------|--------|--------|
| 2026-05-29 | qbp-implementor | v1.0 — initial ratification per F4 architect decision |
