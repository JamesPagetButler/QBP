# QBP Foundations — Master DEFN-* Anchor Inventory

**Version:** 0.1  
**Date:** 2026-05-29  
**Author:** qbp-implementor (foundations rebuild)  
**Phase:** 1 — planning-stage anchor minting  
**Ref:** `prompts/qbp-implementor-foundations-rebuild-instantiation-v1_0.md` §5 Phase 1

This document is the master inventory of every foundational CTH anchor planned for the foundations rebuild. Each anchor is listed with its priority, convention dependencies, provenance trajectory, and dependencies on other anchors.

**Reading key:**
- **Provenance trajectory:** `theory` → `proof, written` → `proof, partial` → `proof, verified`
- **Status at Phase 1:** all anchors below are `provenance_kind: theory, proof_state: null`
- **Convention deps:** F1 = naming, F3 = CD formula, F4 = Fano orientation, F5 = sedenion indexing
- **Priority:** P1 = highest (unblocks most downstream), P3 = lowest among foundational

---

## Category A — Cayley-Dickson construction (convention-independent)

| Anchor ID | Name | Priority | Conv. deps | Lean target | Dependencies |
|---|---|---|---|---|---|
| `DEFN-cayley-dickson-doubling` | CD doubling construction | **P1** | F3 ✅ | `CayleyDickson.lean::CD.mul` | none |
| `DEFN-cd-conjugation-propagation` | Conjugate on CD(A) from A | P1 | F3 ✅ | `CayleyDickson.lean::CD.conj` | DEFN-cayley-dickson-doubling |
| `DEFN-cd-norm-propagation` | Norm on CD(A) from A | P1 | F3 ✅ | `CayleyDickson.lean::CD.norm` | DEFN-cd-conjugation-propagation |
| `DEFN-cd-parametric-level` | Construction parametric in level n | P2 | F3 ✅ | `CayleyDickson.lean::CD.level` | DEFN-cayley-dickson-doubling |

## Category B — Per-level structural objects

| Anchor ID | Name | Priority | Conv. deps | Lean target | Dependencies |
|---|---|---|---|---|---|
| `DEFN-real-structural-trivial` | ℝ — trivial (no imaginary units) | P2 | F1 ✅ | `CayleyDickson.lean::Real.struct` | none |
| `DEFN-complex-structural-i` | ℂ — single imaginary unit i, i²=−1 | P2 | F1 ✅ | `CayleyDickson.lean::Complex.struct` | DEFN-real-structural-trivial |
| `DEFN-quaternion-structural-triad` | ℍ — {i,j,k}, ij=k, i²=j²=k²=−1 | P1 | F1 ✅ | `CayleyDickson.lean::Quaternion.struct` | PROOF-quat-closure |
| `DEFN-octonion-structural-fano` | 𝕆 — Fano plane with 7 imaginary units | P1 | F1 ✅, F4 ✅ | `Octonion.lean::Octonion.fano` | PROOF-fano, DEFN-quaternion-structural-triad |
| `DEFN-sedenion-structural-box-kite` | 𝕊 — box-kite / assessor structure | P2 | F1 ✅, F5 ✅ | `Sedenion.lean::Sedenion.boxKite` | PROOF-42zd, PROOF-hessian, DEFN-octonion-structural-fano |

## Category C — Operations matrix (5 levels × 6 operations = 30 cells)

Operations: `multiplication`, `conjugation`, `norm`, `inverse`, `commutator`, `associator`

Naming: `DEFN-op-{operation}-{level}` where level ∈ {R, C, H, O, S}

| Anchor | Lean/Mathlib source | Notes |
|---|---|---|
| `DEFN-op-multiplication-R` | Mathlib `Real.mul` | inherit |
| `DEFN-op-multiplication-C` | Mathlib `Complex.mul` | inherit |
| `DEFN-op-multiplication-H` | Mathlib `Quaternion.mul` | inherit |
| `DEFN-op-multiplication-O` | `QBP_Octonion.lean` | QBP-local |
| `DEFN-op-multiplication-S` | `Sedenion.lean` | QBP-local |
| `DEFN-op-conjugation-R` | trivial (identity) | — |
| `DEFN-op-conjugation-C` | Mathlib `Complex.conj` | inherit |
| `DEFN-op-conjugation-H` | Mathlib `Quaternion.conj` | inherit |
| `DEFN-op-conjugation-O` | `CayleyDickson.lean::CD.conj` | from DEFN-cd-conjugation-propagation |
| `DEFN-op-conjugation-S` | `CayleyDickson.lean::CD.conj` | from DEFN-cd-conjugation-propagation |
| `DEFN-op-norm-R` through `DEFN-op-norm-S` | propagation chain | from DEFN-cd-norm-propagation |
| `DEFN-op-inverse-R` through `DEFN-op-inverse-O` | norm multiplicativity | ℝ,ℂ,ℍ,𝕆 have well-defined inverse |
| `DEFN-op-inverse-S` | PROOF-42zd + PROOF-loss-of-division | inverse undefined for ZD elements |
| `DEFN-op-commutator-*` | 5 cells | C=0, H/O/S nonzero |
| `DEFN-op-associator-*` | 5 cells | R/C/H=0, O nonzero (alternative), S nonzero |

*Category C anchors are Phase 5 scope. Listed here for completeness.*

## Category D — Breakdown chain proofs (conceptual centrepiece)

| Anchor ID | Name | Priority | Conv. deps | Lean target | Dependencies |
|---|---|---|---|---|---|
| `PROOF-loss-of-order-R-to-C` | ℂ admits no total order | **P1** | none ✅ | `Breakdown.lean::Complex.noOrder` | none |
| `PROOF-loss-of-commutativity-C-to-H` | ℍ has nonzero commutator | **P1** | none ✅ | `Breakdown.lean::Quaternion.nonComm` | PROOF-su2-lie |
| `PROOF-loss-of-associativity-H-to-O` | 𝕆 has nonzero associator | P1 | F4 ✅ | `Breakdown.lean::Octonion.nonAssoc` | DEFN-octonion-structural-fano |
| `PROOF-alternativity-preserved-at-O` | Artin's theorem for 𝕆 | P1 | F4 ✅ | `Breakdown.lean::Octonion.alternative` | DEFN-octonion-structural-fano |
| `PROOF-loss-of-alternativity-O-to-S` | 𝕊 is not alternative | P1 | F5 ✅ | `Breakdown.lean::Sedenion.nonAlternative` | DEFN-sedenion-structural-box-kite |
| `PROOF-loss-of-division-O-to-S` | 𝕊 has zero divisors | P1 | F5 ✅ | `Breakdown.lean::Sedenion.zeroDivisors` | PROOF-42zd, DEFN-sedenion-structural-box-kite |
| `PROOF-loss-of-hurwitz-norm-O-to-S` | Hurwitz norm mult fails | P2 | F5 ✅ | `Breakdown.lean::Sedenion.normFails` | DEFN-sedenion-structural-box-kite |
| `PROOF-preservation-of-power-assoc-O-to-S` | Power-associativity survives | P2 | F5 ✅ | `Breakdown.lean::Sedenion.powerAssoc` | DEFN-sedenion-structural-box-kite |

## Category E — Hurwitz theorem boundary

| Anchor ID | Name | Priority | Conv. deps | Notes |
|---|---|---|---|---|
| `PROOF-hurwitz-theorem-explicit` | Only ℝ,ℂ,ℍ,𝕆 are normed division algebras | P1 | none ✅ | Re-grade of existing PROOF-hurwitz (theory-external) |

## Category F — Re-grading and inverse audit

*(Mechanical work — tracked via QBP #464, #465, migration-report-v5_3-to-v0_3.md)*

---

## Phase 1 priority order (top 8 — planning anchors minted this PR)

1. `DEFN-cayley-dickson-doubling` — central to all of Category A; gates everything
2. `DEFN-real-structural-trivial` — simplest; establishes pattern
3. `DEFN-complex-structural-i` — single imaginary unit
4. `DEFN-quaternion-structural-triad` — refs PROOF-quat-closure (already wired)
5. `DEFN-octonion-structural-fano` — Fano structure; refs PROOF-fano; F4 now ratified
6. `DEFN-sedenion-structural-box-kite` — box-kite; refs PROOF-42zd, PROOF-hessian; F5 ratified
7. `PROOF-loss-of-order-R-to-C` — first breakdown proof; convention-independent
8. `PROOF-loss-of-commutativity-C-to-H` — second breakdown proof; refs PROOF-su2-lie

All 8 are at `provenance_kind: theory, proof_state: null` in the CTH inventory as of Phase 1.

## Dependency graph (simplified)

```
DEFN-cayley-dickson-doubling
  └── DEFN-cd-conjugation-propagation
        └── DEFN-cd-norm-propagation
              └── DEFN-op-norm-* (Phase 5)

DEFN-real-structural-trivial
  └── DEFN-complex-structural-i
        └── DEFN-quaternion-structural-triad (+ PROOF-quat-closure)
              └── DEFN-octonion-structural-fano (+ PROOF-fano, F4)
                    └── DEFN-sedenion-structural-box-kite (+ PROOF-42zd, F5)

PROOF-loss-of-order-R-to-C          [independent]
PROOF-loss-of-commutativity-C-to-H  [+ PROOF-su2-lie]
  └── PROOF-loss-of-associativity-H-to-O (+ F4)
        └── PROOF-loss-of-alternativity-O-to-S (+ F5)
              └── PROOF-loss-of-division-O-to-S
```

## Change history

| Date | Author | Change |
|---|---|---|
| 2026-05-29 | qbp-implementor | v0.1 — Phase 1 master inventory; 8 priority anchors minted as planning-stage |
