# Fano Plane Orientation Convention (F4)

**Status:** RATIFIED — qbp-architecture, pr407-conflict-resolution seq=55, 2026-05-29  
**Resolves:** QBP foundations rebuild Phase 0.5, convention question F4; QBP #460  
**Authorised by:** qbp-architecture  
**Author:** qbp-implementor

---

## Canonical orientation

**Orientation source: F3-FORCED.** QBP's Fano-plane orientation is **not** an
independent literature pin. It is the orientation *uniquely determined* by the
ratified F3 Cayley–Dickson doubling formula (`docs/conventions/cd-doubling.md`)
applied along the standard tower ℝ → ℂ → ℍ → 𝕆 with the ℍ-triad e₁ = i, e₂ = j,
e₃ = k. Once F3 and the ℍ-triad are fixed, the full 8×8 octonion table — including
all 7 oriented triples below — is forced; there is no free choice.

This is **kernel-checked** in `proofs/QBP/Foundations/FanoOrientationF3.lean`:
`fanoTableF4_eq_cayleyDickson` proves the literal transcription of the table in
this doc equals the F3-derived products on **all 64 basis pairs (0 mismatches)**;
`cayleyDickson8_sq_neg_one` proves every eᵢ²=−1 (i∈1..7);
`cayleyDickson8_alternative_on_basis` proves the product is alternative on all
basis triples (the property the broken archive table fails); and
`fanoTriple_oriented_123 … _356` prove each of the 7 oriented triples below holds
with sign +1. All proofs close by the Lean **kernel** `decide` and pass the
`#print axioms` gate ({propext} only — no `native_decide`, no `sorry`).

This is **one of 480 valid signed orientations** of the Fano plane; F3 selects
this one. All 480 are G₂-isomorphic, and QBP matches only **G₂-invariant**
predictions (re-derive-native: QBP does not import Furey's literal operators).
Baez (2002) is retained as **informal background reading only** (see References) —
equivalence of this F3-forced orientation to Baez (2002) Table 1's specific
second-copy sign labeling is **not claimed and not needed**: F3 is the authority.

The 7 positive triples (lines of the Fano plane) with their canonical multiplication direction are:

| Triple | Product rule |
|--------|-------------|
| {1, 2, 3} | e₁e₂ = e₃ |
| {1, 4, 5} | e₁e₄ = e₅ |
| {1, 6, 7} | e₁e₇ = e₆ |
| {2, 4, 6} | e₂e₄ = e₆ |
| {2, 5, 7} | e₂e₅ = e₇ |
| {3, 4, 7} | e₃e₄ = e₇ |
| {3, 5, 6} | e₃e₆ = e₅ |

In each triple {a, b, c}, the product eₐeᵦ = eᵧ holds cyclically: eₐeᵦ = eᵧ, eᵦeᵧ = eₐ, eᵧeₐ = eᵦ. The reverse product picks up a sign: eᵦeₐ = −eᵧ.

**Provenance note (Tier-3 review finding, 2026-05-31; escalation settled, 2026-06-04):** the orientation above is the one *forced by the ratified F3 Cayley-Dickson construction* (`docs/conventions/cd-doubling.md`) applied to the standard quaternion embedding e₁=i, e₂=j, e₃=k. It is **not** independently chosen — once F3 and the ℍ-triad are fixed, the full octonion table is determined. This is now **kernel-checked**, not merely "verified programmatically": `proofs/QBP/Foundations/FanoOrientationF3.lean` builds 𝕆 from the literal F3 doubling formula and proves (a) the table in this doc equals the F3 products on all 64 basis pairs — 0 mismatches (`fanoTableF4_eq_cayleyDickson`), (b) every eᵢ²=−1 (`cayleyDickson8_sq_neg_one`), and (c) the product is alternative on all basis triples (`cayleyDickson8_alternative_on_basis`); all by the Lean kernel `decide`, `#print axioms` ⊆ {propext}. The earlier "Baez 2002 Table 1" citation has been **dropped as the orientation source** (the F3-induced orientation is the authority; equivalence to Baez's specific Table-1 labeling is not claimed and not needed). The inherited `archive/QBP_Octonion.lean` `octonionMul` table disagrees with the F3-forced orientation on **18 of 42** imaginary entries and is **non-alternative** (its `octonionMul_alternative_left` is a `True := by trivial` stub — issue #472). The same Lean file records a single witnessed disagreement (`archiveTable_disagrees_cd`: F3 gives e₁·e₆=−e₇, archive claims +e₇); do **not** use the archive table for anything except, optionally, refutation.

## Full imaginary multiplication table

The complete 7×7 antisymmetric multiplication table for Im 𝕆 = {e₁, ..., e₇}, where eₐeᵦ is the (a,b) entry:

|   | e₁ | e₂ | e₃ | e₄ | e₅ | e₆ | e₇ |
|---|----|----|----|----|----|----|-----|
| **e₁** | −1 | e₃ | −e₂ | e₅ | −e₄ | −e₇ | e₆ |
| **e₂** | −e₃ | −1 | e₁ | e₆ | e₇ | −e₄ | −e₅ |
| **e₃** | e₂ | −e₁ | −1 | e₇ | −e₆ | e₅ | −e₄ |
| **e₄** | −e₅ | −e₆ | −e₇ | −1 | e₁ | e₂ | e₃ |
| **e₅** | e₄ | −e₇ | e₆ | −e₁ | −1 | −e₃ | e₂ |
| **e₆** | e₇ | e₄ | −e₅ | −e₂ | e₃ | −1 | −e₁ |
| **e₇** | −e₆ | e₅ | e₄ | −e₃ | −e₂ | e₁ | −1 |

Each eₐ² = −1. Off-diagonal entries are read as eₐeᵦ (row a, column b). This table is **computed from the F3 Cayley-Dickson construction** (octonions built by doubling ℍ via the ratified F3 formula) and is **kernel-checked** to equal the F3 products on all 64 basis pairs (`fanoTableF4_eq_cayleyDickson` in `proofs/QBP/Foundations/FanoOrientationF3.lean`, by Lean `decide`) — it is the orientation F3 forces, not a hand-transcription. The same file kernel-checks alternativity on all basis triples (`cayleyDickson8_alternative_on_basis`) and eᵢ²=−1 (`cayleyDickson8_sq_neg_one`). The inherited `archive/QBP_Octonion.lean` `octonionMul` table differs from this on 18 of 42 entries and is non-alternative (its `octonionMul_alternative_left` is a `True := by trivial` stub — issue #472); a single witnessed disagreement is recorded as `archiveTable_disagrees_cd`. **Do not use the archive table.**

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

(Baez 2002 Figure 1 shows a standard Fano diagram with directed cycle arrows — informal background; the binding orientation is F3-forced as above.)

## Why there are 480 orientations — and why this one

**Group theory.** The Fano plane's automorphism group is the simple group G₂ of order 168 (also written PSL(2,7) = GL(3,2) — the projective special linear group over GF(7)). These 168 automorphisms permute the 7 points while preserving all 7 lines and their incidence structure.

Starting from one signed orientation (choice of cyclic direction for each line), applying any of the 168 automorphisms gives another valid orientation. Additionally, each line's cyclic direction can be independently reversed, but reversing all 7 simultaneously just negates all products (an orientation with all signs flipped is isomorphic via e_k ↦ −e_k). Counting carefully:

- 480 = 168 × (480/168) — all sign-consistent orientations form a set of size 480
- These 480 orientations fall into equivalence classes under G₂ (related by automorphisms of the Fano plane)
- The F3-forced orientation is the one (up to G₂ automorphism) that gives the "standard" embedding of ℍ ⊂ 𝕆 with {e₁, e₂, e₃} = {i, j, k} and e₁e₂ = e₃ — F3 + the ℍ-triad fix the signs of all 7 lines uniquely (it is not asserted to coincide with Baez 2002 Table 1's specific labeling)

**Why this matters for QBP.** The proof of associativity loss `PROOF-loss-of-associativity-H-to-O` requires a specific non-associative triple as a witness. The witness triple {e₁, e₂, e₄} (satisfying (e₁e₂)e₄ ≠ e₁(e₂e₄) in 𝕆) depends on this orientation. Any of the 480 orientations would give a valid witness, but the witness element changes. This convention pins the witness so proofs are reproducible.

## Lean implementation

The canonical orientation is kernel-checked in **`proofs/QBP/Foundations/FanoOrientationF3.lean`**. That file builds the Cayley–Dickson tower ℝ→ℂ→ℍ→𝕆 directly from the **literal F3 doubling formula** (`docs/conventions/cd-doubling.md`) over `Int` coordinates, defines basis element `eᵢ`, and transcribes the 7×7 table of this doc verbatim as `fanoTableF4 : Fin 8 → Fin 8 → Int × Fin 8`. The provenance theorems (all by Lean **kernel** `decide`; `#print axioms` ⊆ {propext}, no `native_decide`, no `sorry`):

```lean
-- the F4 doc table equals the F3-derived products on all 64 basis pairs (0 mismatches)
theorem fanoTableF4_eq_cayleyDickson :
    ∀ i j : Fin 8, Omul (e i) (e j) = signedBasis (fanoTableF4 i j)
theorem cayleyDickson8_sq_neg_one :                      -- eᵢ² = −1 for i ∈ 1..7
    ∀ i : Fin 8, i.val ≠ 0 → Omul (e i) (e i) = Oneg (e 0)
theorem cayleyDickson8_alternative_on_basis :            -- alternative on all basis triples
    ∀ i j : Fin 8, Omul (Omul (e i) (e i)) (e j) = Omul (e i) (Omul (e i) (e j)) ∧
                   Omul (Omul (e i) (e j)) (e j) = Omul (e i) (Omul (e j) (e j))
theorem fanoTriple_oriented_123 : Omul (e 1) (e 2) = e 3 -- … _145 _167 _246 _257 _347 _356
```

The orientation is therefore **derived from F3**, not posited from a literature table. Indexing: `Fin 8` with index 0 = the real unit e₀ and indices 1..7 = the imaginary units e₁..e₇ (Lean index k = prose eₖ). The 7×7 table above is the `Int × Fin 8` transcription that `fanoTableF4_eq_cayleyDickson` checks against F3.

The previously-cited `archive/QBP_Octonion.lean::octonionMul` table is **broken** (18/42 imaginary entries disagree with F3; non-alternative; `octonionMul_alternative_left` was a `True := by trivial` stub — issue #472) and must not be used as ground truth.

## Sedenion multiplication table

The sedenion multiplication table is determined by applying the Cayley-Dickson doubling formula to this octonion table. The zero divisor structure (42 zero divisors, per PROOF-42zd) and the box-kite / assessor structure (per PROOF-hessian) are computed from this orientation.

See `docs/conventions/sedenion-indexing.md` for the sedenion index convention.

## References

**Authoritative source (orientation):** `docs/conventions/cd-doubling.md` (F3, ratified) + the ℍ-triad e₁=i, e₂=j, e₃=k. The orientation is *forced* by these; kernel-checked in `proofs/QBP/Foundations/FanoOrientationF3.lean`.

**Informal background reading** (not orientation sources; QBP does not claim its F3-forced orientation coincides with these authors' specific sign labelings):

Baez, J.C. (2002). "The Octonions." *Bull. Amer. Math. Soc.* 39(2):145–205. [arXiv:math/0105155](https://arxiv.org/abs/math/0105155) — readable overview of 𝕆, the Fano plane, and the 480 orientations. Background only; **equivalence to Baez (2002) Table 1's specific second-copy labeling is neither claimed nor needed** (this F3-forced orientation differs from Baez Table 1 on the {1,6,7} and {3,5,6} triples).

Furey, C. (2014). "Generations: Three Prints, in Colour." *JHEP* 2014(10):046 — division-algebra Standard Model programme. Background only; QBP is **re-derive-native** (it does not import Furey's literal operators) and matches only G₂-invariant predictions.

Conway, J.H. and Smith, D.A. (2003). *On Quaternions and Octonions*. A.K. Peters/CRC Press. — comprehensive reference on all 480 orientations and their symmetry structure.

## Change history

| Date | Author | Change |
|------|--------|--------|
| 2026-05-29 | qbp-implementor | v1.0 — initial ratification per F4 architect decision |
| 2026-06-04 | qbp (Lean-writer) | Provenance escalation settled: orientation source changed to F3-FORCED, kernel-checked in `proofs/QBP/Foundations/FanoOrientationF3.lean` (`fanoTableF4_eq_cayleyDickson` etc.); Baez 2002 demoted to informal background; no change to the corrected 7×7 table. |
