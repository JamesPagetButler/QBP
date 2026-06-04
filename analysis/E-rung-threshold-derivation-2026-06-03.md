# O1: Decrystallisation Threshold Ladder — E(ℍ→ℂ) Derivation

**Date:** 2026-06-03
**Obligation:** O1 of CONJ-crystallisation-energy-level-equilibrium deliberation
(`docs/foundations/conj-energy-level-crystallisation-deliberation-2026-06-03.md`)
**Status:** COMPLETE — verdict below. Zero free parameters maintained throughout.
**Provenance:** T (analytic derivation from existing QBP machinery; no new axioms)

---

## 1. Method (identical to M_seed, no new parameters)

`SeedMass.lean` defines M_seed by setting Bekenstein–Hawking entropy equal to the
information cost of the 𝕆→ℍ crystallisation selection:

S_BH(M) = 4πGM²/(ℏc) = ln k  ⟹  M(k) = √(ln k · ℏc / 4πG) = √(ln k / 4π) · M_p

For 𝕆→ℍ: k = 7 (Fano lines = quaternionic subalgebras of 𝕆 in the standard frame).

## 2. Derivation decision: discrete frame count, not continuous S² entropy

The Theory Team proposed the continuous selection entropy of choosing a complex
structure from the S² of unit imaginary quaternions. **Rejected:** continuous
Shannon entropy is divergent and any regularisation (coarse-graining scale,
covering number) introduces a free parameter — violating the zero-free-parameter
rule that makes this computation discriminating. The only parameter-free choice is
the one M_seed already made: the **discrete standard-frame count**.

| Transition | Frame | Subalgebras selected among | k | Verified? |
|---|---|---|---|---|
| ℍ→ℂ | {1,i,j,k} | span(1,i), span(1,j), span(1,k) | **3** | ✅ elementary |
| 𝕆→ℍ | octonion frame | 7 Fano lines | **7** | ✅ established in corpus |
| 𝕊→𝕆 | sedenion frame | PG(3,2) planes (candidate 𝕆-subalgebras) | ~~15~~ → **8** | ✅ **KERNEL-CHECKED (O1a, 2026-06-03)**: only 8 of the 15 hyperplane subalgebras are alternative/zero-divisor-free (≅ 𝕆); the other 7 contain explicit zero divisors |

**O1a CORRECTION (lean-prover, kernel-checked, zero-sorry, decide-only):** the
naive pattern k(n) = 2ⁿ−1 is **FALSE at the 𝕊→𝕆 rung**. Of the 15 PG(3,2)
hyperplanes (all XOR-closed, all spanning 8-dim subalgebras), only the 8 with
normal n ≤ 8 are octonion copies; the 7 with normal n ≥ 9 (those mixing the two
doubling halves) contain explicit zero divisors — e.g. (e₂+e₉)(e₄+e₁₅) = 0.
Lean: `proofs/QBP/Foundations/SedenionOctonionCount.lean`, branch
`foundations/o1a-sedenion-octonion-count`, theorems `alternative_hyperplane_count_eq_eight`,
`partition_8_7`, `zero_divisor_normal9..15`; axioms ⊆ {propext, Classical.choice,
Quot.sound}; independent Python cross-check agrees. Caveats: alternativity
checked on basis triples (closed by trilinearity, standard); the
"alternative + 8-dim + positive norm ⟹ 𝕆" classification step is Hurwitz/Zorn,
cited not re-proved.

**Corrected interpretation of k(n):** k counts **genuine division-subalgebra
selections**, NOT frame size. Below 𝕊 every candidate passes automatically
(subalgebras of division algebras are division algebras), so k = frame count by
accident; at 𝕊 — exactly where division is lost — the two notions split:
candidates 15, genuine 8. The selection ladder is **3, 7, 8**.

## 3. Results

| Transition | ln k | M / M_p | GeV | kg |
|---|---|---|---|---|
| E(ℍ→ℂ) | ln 3 = 1.0986 | 0.2957 | 3.610×10¹⁸ | 6.435×10⁻⁹ |
| E(𝕆→ℍ) = M_seed | ln 7 = 1.9459 | 0.3935 | 4.804×10¹⁸ | 8.564×10⁻⁹ |
| E(𝕊→𝕆) | ln 8 = 2.0794 (**O1a-corrected**; was ln 15) | 0.4068 | 4.966×10¹⁸ | 8.854×10⁻⁹ |

Parameter-free ratio predictions: E(ℍ→ℂ)/E(𝕆→ℍ) = √(ln3/ln7) = 0.7514;
E(𝕊→𝕆)/E(𝕆→ℍ) = √(ln8/ln7) = **1.0337** (O1a-corrected; was 1.1797 under the
false k=15 assumption). Monotone ordering **survives** (ln 8 > ln 7) — by one
integer. The top two rungs are now nearly degenerate (3.4% apart).

## 4. Verdict against Wilson's criterion

**Wilson's test:** "derive E(ℍ→ℂ) by the same method with no new free parameter
and check whether it lands on a known scale (e.g. electroweak 246 GeV) to better
than an order of magnitude."

**RESULT: FAILS the landing test.** E(ℍ→ℂ) = 3.6×10¹⁸ GeV is:
- 1.5×10¹⁶ × the electroweak scale (16 orders of magnitude off)
- ~180 × the GUT scale
- within a factor 1.5 of the reduced Planck mass (2.435×10¹⁸ GeV) — noted for
  honesty, but matching to the *nearest* of several Planck-adjacent scales after
  the fact is exactly the post-hoc fishing Wilson warned about; not claimed.

**Structural reason for the failure (stronger than the number):** M ∝ √(ln k) and
ln k grows logarithmically in frame size. The entropy-to-mass bridge **cannot
produce hierarchy** — every conceivable rung lands within a factor of a few of
M_p. The ladder spans a factor 1.57 (band 3.0–5.7×10¹⁸ GeV) while the scales it
would need to reach span 19 orders of magnitude. No choice of k fixes this; it is
the functional form.

## 5. What survives (unexpected structural successes)

1. **Monotone ordering for free.** E(ℍ→ℂ) < E(𝕆→ℍ) < E(𝕊→𝕆): thresholds increase
   with rung, which is exactly the ordering the conjecture's melt-up-the-tower
   requires. Not imposed — it falls out of k = 2ⁿ−1 increasing.
2. **Candidate answer to O2 (the five-rung monotone invariant) — DAMAGED by O1a.**
   The frame/imaginary-unit count 0, 1, 3, 7, 15 = 2ⁿ−1 is still monotone as a
   *property of each level*, but O1a proved it is **no longer the quantity that
   drives the ladder**: the selection count is 3, 7, **8** — the identification
   "ladder cost = frame entropy" breaks exactly at the division-loss rung. The
   invariant and the ladder have decoupled. EITHER the O2 invariant is the
   division-subalgebra selection count (3, 7, 8 — monotone so far, but barely,
   and with no closed form yet) OR 2ⁿ−1 keeps the invariant role and the ladder
   is a different object. This is now a central debate question.
3. **Consistency with the localized-melt reformulation (Finding 3).** All
   thresholds sitting just below M_p means decrystallisation only occurs at
   Planck-density events — black-hole cores and the genesis epoch — exactly where
   QBP-HBH §2.4.2 put the one documented melt. The conjecture is NOT a theory of
   laboratory-accessible transitions, and never was; this computation makes that
   quantitative.

## 6. Interpretation (Oppenheimer)

The computation **kills one reading and sharpens another**:

- **DEAD: the "electroweak = rung transition" reading.** Known accelerator-scale
  symmetry restorations (EW, QCD deconfinement) are NOT Cayley-Dickson rung
  changes. Wilson's categorical objection (gauge symmetry ≠ coefficient-algebra
  structure) is now backed by 16 orders of magnitude. Any future attempt to map
  tower rungs onto collider physics should cite this and stop.
- **SHARPENED: the Planck-band reading.** The tower transitions are a property of
  the Planck regime: ℂ-, ℍ-, 𝕆-physics are separated by thresholds clustered just
  below M_p, ordered correctly, with parameter-free ratios. Everything below
  3×10¹⁸ GeV — all of known physics — lives entirely within the crystallised
  level-ℍ regime. The melt cycle is real in the conjecture's own terms only at
  BH-core/genesis energy densities, consistent with localized epitaxial melts.

**Jaynes's zero-new-content audit, revisited:** the conjecture now owns three
parameter-free numbers (the ratios and the band location) — content it did not
have this morning. But none are observable with foreseeable instruments. The
honest classification stands: NASCENT, now with a quantitative skeleton and a
falsifiable internal structure (the 𝕊→𝕆 count of §2, the O2 candidate), but no
near-term experimental channel.

## 7. New obligations

| # | Obligation | Notes |
|---|---|---|
| O1a | Verify k(𝕊→𝕆) = 15: do all 15 PG(3,2) plane-subspaces of the sedenion frame give 𝕆-isomorphic subalgebras? | Discrete computation — lean-prover candidate (decide-able on the frame) |
| O1b | Confront O2 with the 2ⁿ−1 candidate: does imaginary-unit count carry the "energy-conjugate" role the teams wanted? Counter-Team must attack it | theory teams |
| O1c | Record DEAD ruling: "tower rungs ≠ collider-scale symmetry restorations" — cite this doc | working-ontology v0.1 (O4) |
