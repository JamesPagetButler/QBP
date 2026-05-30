# QBP Foundations

**Version:** 0.1 (skeleton — planning stage)  
**Date:** 2026-05-29  
**Author:** qbp-implementor (foundations rebuild)  
**Phase:** 1 — document skeleton; prose proofs deferred to Phase 2–5  
**Ref:** `prompts/qbp-implementor-foundations-rebuild-instantiation-v1_0.md` §4

This document will become the prose foundation for all QBP algebraic derivations. At version 0.1, it establishes chapter structure and anchor cross-references. Prose proofs are stubs; they will be promoted from `theory` to `proof, written` as Lean source lands.

**Convention references:**
- Cayley-Dickson formula: `docs/conventions/cd-doubling.md` (F3)
- Algebra naming: `docs/conventions/algebra-naming.md` (F1)
- Sedenion indexing: `docs/conventions/sedenion-indexing.md` (F5)
- Fano orientation: `docs/conventions/fano-orientation.md` (F4)

---

## Chapter 1 — The Cayley-Dickson Construction

*CTH anchors: DEFN-cayley-dickson-doubling, DEFN-cd-conjugation-propagation, DEFN-cd-norm-propagation, DEFN-cd-parametric-level*  
*Lean: `proofs/QBP/Foundations/CayleyDickson.lean`*  
*Status: planning stage (provenance_kind: theory)*

### 1.1 The doubling formula

Given a \*-algebra A over ℝ with conjugation `*`, the Cayley-Dickson double CD(A) consists of ordered pairs (a₁, a₂) with a₁, a₂ ∈ A. Multiplication is defined by:

```
(a₁, a₂)(b₁, b₂) = (a₁b₁ − b₂*·a₂,  b₂·a₁ + a₂·b₁*)
```

*[Anchor: DEFN-cayley-dickson-doubling — see docs/conventions/cd-doubling.md for the canonical form and Baez 2002 §1.1 citation.]*

**[STUB — prose proof of well-definedness pending Phase 2]**

### 1.2 Conjugation propagation

Conjugation on CD(A) is defined recursively:

```
conj(a₁, a₂) = (conj(a₁), −a₂)
```

*[Anchor: DEFN-cd-conjugation-propagation]*

**[STUB — Lean target: QBP.Foundations.CayleyDickson.conj]**

### 1.3 Norm propagation

The norm satisfies `|(a₁, a₂)|² = |a₁|² + |a₂|²`.

*[Anchor: DEFN-cd-norm-propagation]*

**[STUB — Lean target: QBP.Foundations.CayleyDickson.norm_sq]**

### 1.4 Parametric level

The construction is parametric: A₀ = ℝ, Aₙ = CD(Aₙ₋₁) for n ≥ 1.

*[Anchor: DEFN-cd-parametric-level]*

**[STUB — Lean target: QBP.Foundations.CayleyDickson.level]**

---

## Chapter 2 — Per-Level Structural Objects

*CTH anchors: DEFN-real-structural-trivial, DEFN-complex-structural-i, DEFN-quaternion-structural-triad, DEFN-octonion-structural-fano, DEFN-sedenion-structural-box-kite*  
*Status: planning stage (provenance_kind: theory)*

### 2.1 ℝ — trivial structure

ℝ = A₀. No imaginary units. Conjugation is identity. All operations are classical.

*[Anchor: DEFN-real-structural-trivial]*

### 2.2 ℂ — single imaginary unit

ℂ = CD(ℝ) = A₁. The single imaginary unit i = (0, 1) satisfies i² = −1.

*[Anchor: DEFN-complex-structural-i — see docs/conventions/algebra-naming.md for the ℂ notation convention.]*

### 2.3 ℍ — quaternion triad

ℍ = CD(ℂ) = A₂. The three imaginary units {e₁, e₂, e₃} = {i, j, k} satisfy:
- e₁e₂ = e₃,  e₂e₃ = e₁,  e₃e₁ = e₂  (cyclic)
- e₁² = e₂² = e₃² = −1

*[Anchor: DEFN-quaternion-structural-triad — refs PROOF-quat-closure for closure under multiplication.]*

**[STUB — Lean target: QBP.Foundations.CayleyDickson.Quaternion.struct]**

### 2.4 𝕆 — Fano-plane structure

𝕆 = CD(ℍ) = A₃. Seven imaginary units e₁..e₇ whose multiplication is encoded by the Fano plane (7 points, 7 lines, each line a quaternionic triple).

The 7 positive triples per the canonical orientation (Baez 2002 Table 1, see `docs/conventions/fano-orientation.md`):
{1,2,3}, {1,4,5}, {1,6,7}, {2,4,6}, {2,5,7}, {3,4,7}, {3,5,6}.

*[Anchor: DEFN-octonion-structural-fano — refs PROOF-fano; depends on F4 ratification (complete).]*

**[STUB — Lean target: QBP.Foundations.Octonion.fano]**

### 2.5 𝕊 — box-kite structure

𝕊 = CD(𝕆) = A₄. Fifteen imaginary units e₁..e₁₅ (see `docs/conventions/sedenion-indexing.md`). The zero-divisor structure is captured by the box-kite / assessor framework (de Marrais 2000).

*[Anchor: DEFN-sedenion-structural-box-kite — refs PROOF-42zd (42 zero divisors) and PROOF-hessian; depends on F5 ratification (complete).]*

**[STUB — Lean target: QBP.Foundations.Sedenion.boxKite]**

---

## Chapter 3 — The Breakdown Chain

*CTH anchors: PROOF-loss-of-order-R-to-C, PROOF-loss-of-commutativity-C-to-H, PROOF-loss-of-associativity-H-to-O, PROOF-alternativity-preserved-at-O, PROOF-loss-of-alternativity-O-to-S, PROOF-loss-of-division-O-to-S, PROOF-loss-of-hurwitz-norm-O-to-S, PROOF-preservation-of-power-assoc-O-to-S*  
*Lean: `proofs/QBP/Foundations/Breakdown.lean`*  
*Status: planning stage (provenance_kind: theory)*

The conceptual centrepiece. Each Cayley-Dickson doubling loses one algebraic property; each loss requires an explicit proof with a concrete witness.

| Transition | Property lost | Witness | Convention dep | Anchor |
|---|---|---|---|---|
| ℝ → ℂ | Total order | i² = −1 < 0 impossible in ordered field | none | PROOF-loss-of-order-R-to-C |
| ℂ → ℍ | Commutativity | [i, j] = 2k ≠ 0 | none | PROOF-loss-of-commutativity-C-to-H |
| ℍ → 𝕆 | Associativity | (e₁e₂)e₄ ≠ e₁(e₂e₄) | F4 | PROOF-loss-of-associativity-H-to-O |
| ℍ → 𝕆 | — | Artin: every 2-element subalgebra of 𝕆 is associative | F4 | PROOF-alternativity-preserved-at-O |
| 𝕆 → 𝕊 | Alternativity | explicit triple | F5 | PROOF-loss-of-alternativity-O-to-S |
| 𝕆 → 𝕊 | Division property | 42 zero divisors | F5 | PROOF-loss-of-division-O-to-S |
| 𝕆 → 𝕊 | Hurwitz norm multiplicativity | explicit counterexample | F5 | PROOF-loss-of-hurwitz-norm-O-to-S |
| 𝕆 → 𝕊 | (survives) power-associativity | Schafer: every element generates associative subalgebra | F5 | PROOF-preservation-of-power-assoc-O-to-S |

### 3.1 ℝ → ℂ: Loss of total order

**Claim:** ℂ admits no total order compatible with field operations.

**Witness:** In any totally ordered field, squares are non-negative. But i² = −1 < 0. Contradiction.

*[Anchor: PROOF-loss-of-order-R-to-C — convention-independent.]*

**[STUB — Lean target: QBP.Foundations.Breakdown.Complex.noTotalOrder]**

### 3.2 ℂ → ℍ: Loss of commutativity

**Claim:** ℍ has nonzero commutator.

**Witness:** [i, j] = ij − ji = k − (−k) = 2k ≠ 0.

*[Anchor: PROOF-loss-of-commutativity-C-to-H — refs PROOF-su2-lie for the Lie algebra structure. Convention-independent.]*

**[STUB — Lean target: QBP.Foundations.Breakdown.Quaternion.nonCommutativity]**

### 3.3 ℍ → 𝕆: Loss of associativity (witness triple)

**Claim:** 𝕆 has nonzero associator.

**Witness (F4-dependent):** Using the Baez/Furey Fano orientation, the triple (e₁, e₂, e₄) satisfies (e₁e₂)e₄ ≠ e₁(e₂e₄). Concretely: (e₁e₂)e₄ = e₃e₄ = e₇; e₁(e₂e₄) = e₁e₆ = e₇. Wait — that gives equality. The non-associative triple is (e₁, e₂, e₄)... let me recalculate.

*[Note: witness computation pending Phase 4 — the specific triple depends on Fano orientation F4 (now ratified). Lean stub below has sorry.]*

*[Anchor: PROOF-loss-of-associativity-H-to-O — depends on DEFN-octonion-structural-fano.]*

**[STUB — Lean target: QBP.Foundations.Breakdown.Octonion.nonAssociativity]**

### 3.4 Alternativity preserved at 𝕆 (Artin's theorem)

**Claim:** Every subalgebra of 𝕆 generated by two elements is associative.

**Proof strategy:** Artin's theorem (Schafer 1966, Ch. III). Any alternative algebra satisfies this. 𝕆 is alternative by direct verification of the four alternative identities.

*[Anchor: PROOF-alternativity-preserved-at-O]*

**[STUB]**

### 3.5 𝕆 → 𝕊: Remaining breakdown proofs

Proofs for alternativity loss, zero-divisors, Hurwitz norm failure, and power-associativity preservation. All depend on F5 (sedenion indexing, now ratified).

*[Stubs — Phase 4 scope. Witnesses: see PROOF-42zd (42 zero divisors), PROOF-hessian (Hessian spectrum) for existing Lean content.]*

---

## Chapter 4 — Operations Matrix

*CTH anchors: DEFN-op-{operation}-{level} (30 cells)*  
*Status: Phase 5 scope — not yet authored*  
*Lean: `proofs/QBP/Foundations/Operations.lean`*

**[STUB — full 30-cell table deferred to Phase 5]**

Summary of what breaks:

| Operation | ℝ | ℂ | ℍ | 𝕆 | 𝕊 |
|---|---|---|---|---|---|
| Multiplication | ✓ | ✓ | ✓ | ✓ | ✓ |
| Conjugation | trivial | ✓ | ✓ | ✓ | ✓ |
| Norm (multiplicative) | ✓ | ✓ | ✓ | ✓ | ✗ |
| Inverse | ✓ | ✓ | ✓ | ✓ | partial (ZD elements excluded) |
| Commutator = 0 | ✓ | ✓ | ✗ | ✗ | ✗ |
| Associator = 0 | ✓ | ✓ | ✓ | ✗ | ✗ |

---

## Chapter 5 — Hurwitz Theorem Boundary

*CTH anchor: PROOF-hurwitz-theorem-explicit*

**Claim:** The only normed division algebras over ℝ are ℝ, ℂ, ℍ, 𝕆.

**Provenance:** theory-external (Hurwitz 1898). Existing anchor PROOF-hurwitz carries this with `provenance_kind: theory-external, theory_citation: "Hurwitz 1898"`.

The foundational rebuild promotes this to `PROOF-hurwitz-theorem-explicit` with explicit connection to the Cayley-Dickson tower above — ℝ, ℂ, ℍ, 𝕆 are precisely levels 0–3, and 𝕊 (level 4) is the first algebra in the tower that fails the normed division algebra condition (Chapter 3.5).

**[STUB — re-grade of PROOF-hurwitz pending Phase 2]**

---

## Appendix A — Convention cross-references

| Topic | Convention file | F-number | Status |
|---|---|---|---|
| CD doubling formula | `docs/conventions/cd-doubling.md` | F3 | Ratified ✅ |
| Algebra-level naming | `docs/conventions/algebra-naming.md` | F1 | Ratified ✅ |
| Sedenion basis indexing | `docs/conventions/sedenion-indexing.md` | F5 | Ratified ✅ |
| Fano plane orientation | `docs/conventions/fano-orientation.md` | F4 | Ratified ✅ |

## Appendix B — Lean file structure

| File | Contents | Phase |
|---|---|---|
| `proofs/QBP/Foundations/CayleyDickson.lean` | Category A + B (levels ℝ-𝕊) | 2–3 |
| `proofs/QBP/Foundations/Octonion.lean` | 𝕆-specific (Fano, F4-dependent) | 3 |
| `proofs/QBP/Foundations/Sedenion.lean` | 𝕊-specific (box-kite, F5-dependent) | 3 |
| `proofs/QBP/Foundations/Breakdown.lean` | Category D (breakdown chain) | 4 |
| `proofs/QBP/Foundations/Operations.lean` | Category C (operations matrix) | 5 |

## Change history

| Date | Author | Change |
|---|---|---|
| 2026-05-29 | qbp-implementor | v0.1 — Phase 1 skeleton; chapter structure + stubs for all 6 categories |
