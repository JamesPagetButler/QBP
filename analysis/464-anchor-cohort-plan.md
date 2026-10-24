# #464 anchor cohort plan: ANCHOR rows → Tier-3 encoder PRs

**Date:** 2026-10-24 · **Master:** `656d462` · **Ledger:** 6.19.0 · **Source rows:** [`foundations-orphan-resolutions.md`](foundations-orphan-resolutions.md) §3 (5 ANCHOR rows)
**Lane:** qbp-implementor (encoder, confined write via `scripts/cth_ledger_edit.py`, R5 of `docs/conventions/anchor-prefix-policy.md`). **Theory-axis co-sign: @qbp-oppenheimer on every cohort** (each one changes what an existing anchor claims). **Schema axis:** no new anchor id is proposed, so no cth-implementor co-sign is needed. If theory picks the fallback id in Cohort B, that PR gains a schema-axis co-sign (@cth-implementor) under R6.

All three cohorts **extend existing anchors**: they add `theorems[]` entries, add qualified names to `lean_companion_theorems`, add one scope sentence to `description`, and add `prediction_chain` (derived_from) edges. None changes `provenance_kind` (all `proof`), `proof_file`, or `status`. Each new witness needs the C3-FULL bar: a captured `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}`. The three source files already carry `#print axioms` lines for every one of these theorems (ArtinCore l.378, ArtinSpan l.377, ArtinTrace l.129–133), but **the encoder PR must capture the output under `run-bounded`, not cite the source line**. This plan ran no elaboration.

## Cohort A: PROOF-artin-theorem (+2)

| Field | Change |
|---|---|
| anchor | `PROOF-artin-theorem` (existing; `proof_file` `proofs/QBP/Foundations/Artin.lean`, unchanged) |
| `theorems[]` += | `span4_mul_closed` (ArtinSpan.lean:312), `assoc_vanishes_on_span4` (ArtinCore.lean:349) |
| `lean_companion_theorems` += | `QBP.Foundations.CDAlg.span4_mul_closed`, `QBP.Foundations.CDAlg.assoc_vanishes_on_span4` |
| derived_from (own `prediction_chain`, currently `[]`) | `PROOF-ops-alternativity-ladder` (`octonion_alternative`, polarized alternativity), `PROOF-ops-flexibility-ladder` (flexibility, via `assoc_diag_flex`), `PROOF-cd-product-formula` (`cdAlg_sq_eq`, and after Cohort B the swap identity) |
| inbound edges (consumers' `prediction_chain` += `PROOF-artin-theorem`) | PROOF-quaternion-frame-maximal, PROOF-quatdouble-rho-invariant-mul-closed, PROOF-octonion-perp-module-span4-maximal, PROOF-associative-composition-iff, PROOF-gradient-lies-in-host-kernel-algebra |
| scope note (description sentence) | "Also witnesses the two halves the proof assembles, for every pair x, y ∈ 𝕆: span ℝ {1,x,y,x·y} is closed under the product (`span4_mul_closed`) and the associator vanishes on it (`assoc_vanishes_on_span4`). NOT claimed: dim span = 4 (no independence hypothesis), or any statement about 𝕊." |

**Theory question for @qbp-oppenheimer:** should the flexibility edge point at `PROOF-ops-flexibility-ladder` or at `PROOF-octonion-moufang`? `assoc_diag_flex` lives in `OctonionLaws.lean`, which is file-anchored by PROOF-octonion-moufang and PROOF-power-associativity. The ladder anchor names `octonion_flexible`, which is the law itself. The plan defaults to the ladder.

**Ordering:** the derived_from edge to PROOF-cd-product-formula names the swap identity only after Cohort B lands. Land B first, or land A with the `cdAlg_sq_eq` reason alone.

## Cohort B: PROOF-cd-product-formula (+2)

| Field | Change |
|---|---|
| anchor | `PROOF-cd-product-formula` (existing; `proof_file` `proofs/QBP/Foundations/CDAlg.lean`, unchanged; `theorems[]` already holds `cdAlg_sq_eq`) |
| `theorems[]` += | `cdAlg_mul_add_swap` (ArtinTrace.lean:86), `cdAlg_mul_add_swap_pure` (ArtinTrace.lean:120) |
| `lean_companion_theorems` += | `QBP.Foundations.CDAlg.cdAlg_mul_add_swap`, `QBP.Foundations.CDAlg.cdAlg_mul_add_swap_pure` |
| derived_from (own `prediction_chain`, currently `[]`) | `PROOF-norm-form-bilinear` (the proof uses `N_add`/`bil`; Cohort C puts `N_add` there). No cycle: PROOF-norm-form-bilinear's chain is `[]` |
| inbound edges | PROOF-order-three-automorphism-fixes-ell (`mul_swap_eq`), PROOF-rule-field-in-kernel-algebra-leaf-foliation (`mul_swap_self_pure`), PROOF-artin-theorem (Cohort A) |
| scope note | "Also witnesses the polarization of the square law at every level n: x·y + y·x = (2 Re x)·y + (2 Re y)·x − 2⟨x,y⟩·1 (`cdAlg_mul_add_swap`), and for Re x = Re y = 0, x·y + y·x = −2⟨x,y⟩·1 (`cdAlg_mul_add_swap_pure`). Over ℝ only (both lemmas are stated for `CDAlg ℝ n`)." |

**Fallback (theory's choice):** if @qbp-oppenheimer judges the swap identity out of scope for a "product formula" anchor, mint `PROOF-cd-trace-swap-identity` instead. It takes the `PROOF-` prefix and an R4 slug, uses `proof_file` `proofs/QBP/Foundations/ArtinTrace.lean`, and `prediction_chain` = [PROOF-cd-product-formula, PROOF-norm-form-bilinear]. This is the only new-id option in this plan. Choosing it triggers the @cth-implementor schema-axis co-sign. Side effect: the audit's file-level match would then also cover `reCoord_add` and `mul_self_add` (U5). That is the coarse semantics the report already labels as a lower bound, and it would need saying in the PR.

## Cohort C: PROOF-norm-form-bilinear (+1)

| Field | Change |
|---|---|
| anchor | `PROOF-norm-form-bilinear` (existing; `proof_file` `proofs/QBP/Foundations/NormForm.lean`, unchanged) |
| `theorems[]` += | `N_add` (ArtinTrace.lean:57) |
| `lean_companion_theorems` += | `QBP.Foundations.CDAlg.N_add`. **The qualified name is required:** bare `N_add` also names `QBP.Foundations.CrossProduct.N_add` (CrossProduct.lean:79) |
| derived_from | none added (polarization of `N = bil · ·`, already this anchor's content) |
| inbound edges | PROOF-octonion-zd-hypersurface-empty (`octonion_bil_comp`, LeftMulDet.lean:66), PROOF-rule-field-in-kernel-algebra-leaf-foliation (`liftLeaf_gradV_eq`), PROOF-cd-product-formula (Cohort B) |
| scope note | "Also witnesses the additive polarization N(x+y) = N x + N y + 2⟨x,y⟩ over ℝ (`CDAlg.N_add`; a general-`CommRing` copy lives at `CrossProduct.N_add`)." |
| verification needed in the encoder PR | Confirm by elaboration (e.g. `#check @N_add` inside the consumer's namespace context, under `run-bounded`) that LeftMulDet and RuleFlowLeafFoliation bind `CDAlg.N_add`. This plan inferred it from `open` lines only |

## Summary

| Cohort | Anchor (existing) | +theorems | New edges (out / in) | Co-sign |
|---|---|---:|---|---|
| A | PROOF-artin-theorem | 2 | 3 / 5 | @qbp-oppenheimer (theory) |
| B | PROOF-cd-product-formula | 2 | 1 / 3 | @qbp-oppenheimer (theory); +@cth-implementor only if the fallback id is chosen |
| C | PROOF-norm-form-bilinear | 1 | 0 / 3 | @qbp-oppenheimer (theory) |

Suggested landing: one encoder PR with three commits in the order **C → B → A**, so every edge resolves when it is written. Three separate PRs also work; the implementor decides. Expected audit after landing: `orphans=37`, baseline bumped in the same commit, with the 37 UNANCHORED-BY-DESIGN rows handed to #627.
