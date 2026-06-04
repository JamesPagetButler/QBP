# Algebra-Level Naming Convention (F1)

**Status:** RATIFIED — qbp-architecture, pr407-conflict-resolution seq=55, 2026-05-29  
**Resolves:** QBP foundations rebuild Phase 0.5, convention question F1; also QBP #462 (anchor prefix policy, F1 subsection)  
**Authorised by:** qbp-architecture  
**Author:** qbp-implementor

---

## Dual convention

QBP uses a dual naming convention: **Unicode glyphs in prose**, **Mathlib-style identifiers in Lean**.

| Level | Prose (Unicode) | Lean (Mathlib-style) | Notes |
|-------|----------------|---------------------|-------|
| ℝ (reals) | ℝ | `Real` | Mathlib4 canonical |
| ℂ (complex) | ℂ | `Complex` | Mathlib4 canonical |
| ℍ (quaternions) | ℍ | `Quaternion` | Mathlib4 canonical |
| 𝕆 (octonions) | 𝕆 | `Octonion` | Mathlib4 canonical |
| 𝕊 (sedenions) | 𝕊 | `Sedenion` | QBP-local type (no Mathlib4 equivalent) |

**Prose** includes: paper text, CTH anchor names and descriptions, markdown documentation, comments in Lean source files.

**Lean source** includes: type names, theorem statements, `def` and `theorem` identifiers, module names.

## Basis element labels

Subscripted basis element labels (e₀, e₁, ...) are acceptable in **both** prose and Lean doc-comments as labels for specific basis vectors. This is separate from algebra-type naming.

| Algebra | Basis elements | Convention |
|---------|---------------|------------|
| ℝ | 1 | e₀ = 1 (or just "1") |
| ℂ | 1, i | e₀ = 1, e₁ = i |
| ℍ | 1, i, j, k | e₀ = 1, e₁ = i, e₂ = j, e₃ = k |
| 𝕆 | 1, e₁..e₇ | e₀ = 1, e₁..e₇ imaginary; see `docs/conventions/fano-orientation.md` |
| 𝕊 | 1, e₁..e₁₅ | e₀ = 1, e₁..e₁₅ imaginary; see `docs/conventions/sedenion-indexing.md` |

## CTH anchor naming

CTH anchor IDs use the Unicode glyph form for algebra references, consistent with the inventory baseline `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json`.

Examples:
- `DEFN-ℍ-hamilton-product` (not `DEFN-H-hamilton-product` or `DEFN-quaternion-hamilton-product`)
- `PROOF-loss-of-commutativity-ℂ-to-ℍ` (not `PROOF-loss-of-commutativity-C-to-H`)
- `DEFN-op-norm-𝕆` (not `DEFN-op-norm-O`)

The Unicode glyph is the canonical anchor name component. ASCII fallback suffixes (e.g. `-O`, `-H`) are not used in new anchors.

## Lean module naming

Lean module names and file names use English descriptive names, not Unicode glyphs:

| Module | File |
|--------|------|
| Cayley-Dickson construction | `proofs/QBP/Foundations/CayleyDickson.lean` |
| Octonion foundations | `proofs/QBP/Foundations/Octonion.lean` |
| Sedenion foundations | `proofs/QBP/Foundations/Sedenion.lean` |
| Breakdown chain | `proofs/QBP/Foundations/Breakdown.lean` |

Internal theorem and definition names follow Mathlib4 naming conventions (snake_case, descriptive).

## Rationale

Unicode glyphs in prose are conventional in the mathematics and theoretical physics literature that QBP builds on (Baez, Furey, Harvey, Lawson-Michelsohn). Using them in prose gives QBP documents the same notational register as their citations.

Mathlib-style identifiers in Lean are required for Mathlib4 compatibility: the existing `Mathlib.Algebra.Quaternion` uses `Quaternion`, not ℍ, as the type name. QBP Lean proofs that import Mathlib types must use consistent names.

## Reference

Mathlib4 algebra type names: `Mathlib.Analysis.SpecialFunctions.Complex.Circle`, `Mathlib.Algebra.Quaternion`, `Mathlib.Analysis.Octonion`.

Baez, J.C. (2002). "The Octonions." *Bull. Amer. Math. Soc.* 39(2):145–205 — uses ℝ, ℂ, ℍ, 𝕆 throughout.

## Change history

| Date | Author | Change |
|------|--------|--------|
| 2026-05-29 | qbp-implementor | v1.0 — initial ratification per F1 architect decision |
