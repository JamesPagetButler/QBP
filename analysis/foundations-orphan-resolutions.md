# Foundations orphan resolutions (#464 Phase B, AC2/AC3)

**Date:** 2026-10-24 · **Master:** `656d462` · **Ledger:** `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` @ 6.19.0 (346 anchors)
**Scope:** the 42 Lean-side orphans reported by `scripts/anchor_inverse_audit.py` on that master. Docs only: no ledger edit, no Lean edit, no Lean elaboration. Every statement below was read from the `.lean` source at the cited line.
**Plan comment:** issue #464, 2026-10-24. **Cohort plan for the ANCHOR rows:** [`464-anchor-cohort-plan.md`](464-anchor-cohort-plan.md).

## 0. Reproduce

```
python3 scripts/anchor_inverse_audit.py --out-md /tmp/a.md --out-json /tmp/a.json --stamp 2026-10-24
# theorems=1945 orphans=42 phantoms=0 stale=0
python3 scripts/anchor_inverse_audit.py --check --out-md /tmp/a.md --out-json /tmp/a.json --stamp 2026-10-24
# exit 0 (42 = baseline)
```

The JSON from that run is identical to the committed `analysis/foundations-inverse-anchor-audit.json` (`==` compare, same 42 orphans, same stats).

## 1. Result

| Disposition | Count |
|---|---:|
| **ANCHOR** (add to an existing anchor's `theorems[]`) | **5** |
| **UNANCHORED-BY-DESIGN** | **37** |
| Total | 42 |

| Module | Orphans | ANCHOR | UNANCHORED-BY-DESIGN |
|---|---:|---:|---:|
| `proofs/QBP/Foundations/ArtinCore.lean` | 17 | 1 | 16 |
| `proofs/QBP/Foundations/ArtinSpan.lean` | 20 | 1 | 19 |
| `proofs/QBP/Foundations/ArtinTrace.lean` | 5 | 3 | 2 |

All 42 sit in the proof route of Artin's theorem at 𝕆 (`octonion_artin`, `Artin.lean`), which `PROOF-artin-theorem` anchors. No new anchor id is proposed (one fallback id is named in the cohort plan, for theory to accept or decline).

### 1.1 What changed since #619

`docs/cth/619-orphan-disposition-full.md` (PR #628) marked all 42 `aux`, with one reason per file ("Artin-theorem core/span/trace lemma; supports octonion_artin"). This walk reads each statement and checks who consumes it. Five lemmas are now **named proof inputs to anchored theorems in other modules**, so the per-file reason no longer fits them:

Field key: **[t]** = the consumer is named in that anchor's `theorems[]`; **[lt]** = named only in `lean_theorem`/`lean_companion_theorems`; **[f]** = named nowhere, its file is the anchor's `proof_file`. `anchor_inverse_audit.py` reads `theorems[]`, `proof_file` and prose `.lean` paths. It does **not** read `lean_theorem`/`lean_companion_theorems`, so an [lt] consumer is anchored for the tool only through its file.

| Lemma | Consumed by (enclosing theorem → its anchor [field]) |
|---|---|
| `span4_mul_closed` | `quaternion_frame_subalgebra` → PROOF-quaternion-frame-maximal [t]; `mul_mem_quatDouble` → PROOF-quatdouble-rho-invariant-mul-closed [lt]; `perp_span4_left_module`/`_right_module` → PROOF-octonion-perp-module-span4-maximal [lt] (all `HolographicSubalgebra.lean`); `inQuatSpanOct_mul` → PROOF-gradient-lies-in-host-kernel-algebra [lt] (`InFlightAlgebra.lean`) |
| `assoc_vanishes_on_span4` | `quaternion_frame_subalgebra` → PROOF-quaternion-frame-maximal [t]; `lMul_comp_on_quaternion_frame` → PROOF-associative-composition-iff [t] (`HolographicSubalgebra.lean`); `inQuatSpanOct_assoc` → PROOF-gradient-lies-in-host-kernel-algebra [lt] (`InFlightAlgebra.lean`) |
| `cdAlg_mul_add_swap` | `mul_swap_eq` → PROOF-order-three-automorphism-fixes-ell [lt] (`CrystalHosting.lean` l.1171) |
| `cdAlg_mul_add_swap_pure` | `mul_swap_self_pure` → PROOF-rule-field-in-kernel-algebra-leaf-foliation [f] (`Substrate/RuleFlowLeafFoliation.lean` l.266; the anchor's description names this lemma) |
| `N_add` (`CDAlg.N_add`, ArtinTrace l.57) | `octonion_bil_comp` → PROOF-octonion-zd-hypersurface-empty [f] (`LeftMulDet.lean` l.66); `liftLeaf_gradV_eq` → PROOF-rule-field-in-kernel-algebra-leaf-foliation [t] (`RuleFlowLeafFoliation.lean` l.418/421) |

Method: Appendix A (c). This is a reading of the source text. The `N_add` binding is also a source-text inference: both consumer files `open QBP.Foundations.CDAlg` and neither opens `QBP.Foundations.CrossProduct`, where a second `N_add` lives. No elaboration was run to confirm it.

The other 37 stay unanchored, and each now has its own reason instead of the per-file one. That gives #627 AC2 (per-theorem reasons for the allowlist) a source to cite.

## 2. Disposition rule

- **ANCHOR**: the statement is a mathematical fact about the algebra or its norm form (not membership bookkeeping, not an instance field, not a one-line consequence of an anchored law), **and** an anchored theorem in another module uses it as a named proof input. Its claim is then a premise of more than one anchor, so the ledger should name it.
- **UNANCHORED-BY-DESIGN**: everything else, in one of these classes:

| Class | Meaning |
|---|---|
| **U1 route-internal** | A step of the Artin route used only inside `Artin*.lean`. The anchored headline `octonion_artin` (PROOF-artin-theorem) covers its content. |
| **U2 private helper** | A `private theorem` that splits elaboration. It cannot be referenced outside the file, so it cannot be a ledger witness. |
| **U3 generic lift** | A statement about an arbitrary bi-/trilinear map `T`. It says nothing about the CD product. |
| **U4 instance field** | A lemma that exists to fill a typeclass field. |
| **U5 one-step consequence** | Follows in one rewrite from an existing law (unit laws, `add_coord`, distributivity). |
| **U6 membership / unfolding** | A generator lies in its own span (`subset_span`), or a `@[simp] Iff.rfl` unfolding. |
| **U7 cell lemma** | One cell of a case table that a U1/ANCHOR lemma assembles. |

## 3. Per-theorem table

Statements are paraphrased in one line from the source; `assoc a b c := (a*b)*c − a*(b*c)`, `gen4 x y := {1, x, y, x*y}`, `span4 := Submodule.span ℝ (gen4 x y)`, `𝕆 = CDAlg ℝ 3`.

### 3.1 `proofs/QBP/Foundations/ArtinCore.lean` (17)

| # | file:line | theorem | statement | disposition | anchor / class + rationale |
|---|---|---|---|---|---|
| 1 | ArtinCore.lean:54 | `assoc_one_left` | `∀ y z : CDAlg R n, assoc 1 y z = 0` | UNANCHORED | U5: one `simp` from the unit law `cdAlg_one_mul` (CDBridge; named in PROOF-cd-associativity-level2) |
| 2 | ArtinCore.lean:58 | `assoc_one_mid` | `assoc x 1 z = 0` | UNANCHORED | U5: one `simp` from the unit laws `cdAlg_mul_one`, `cdAlg_one_mul` |
| 3 | ArtinCore.lean:62 | `assoc_one_right` | `assoc x y 1 = 0` | UNANCHORED | U5: one `simp` from the unit law `cdAlg_mul_one` |
| 4 | ArtinCore.lean:74 | `assoc_x_xy_y` | on 𝕆: `assoc x (x*y) y = 0` | UNANCHORED | U1: helper for L2 (its docstring says "Helper for L2"); used only in ArtinCore |
| 5 | ArtinCore.lean:100 | `assoc_xy_survivor` | on 𝕆: `assoc x y (x*y) = 0` | UNANCHORED | U1: the strategy's "de-risk gate" L2. The milestone is recorded in `docs/foundations/artin-strategy-2026-06-06.md`. Used only in ArtinCore |
| 6 | ArtinCore.lean:118 | `trilinear_vanish_on_span` | trilinear `T` vanishing on `s×s×s` ⇒ vanishes on `span R s` (each slot) | UNANCHORED | U3: generic span-induction lift, no CD content |
| 7 | ArtinCore.lean:165 | `assoc_span4` | on 𝕆: (assoc vanishes on gen4³) ⇒ assoc vanishes on span4³ | UNANCHORED | U1: hypothesis-parametrized reduction, consumed by #17 as a direct proof helper (`assoc_span4 x y (assoc_gen4_zero x y) hu hv hw`); #17 discharges the hypothesis and is the anchored form |
| 8 | ArtinCore.lean:178 | `assoc_yx_survivor` | on 𝕆: `assoc y x (x*y) = 0` | UNANCHORED | U7: L2-symmetric cell of the 64-triple table |
| 9 | ArtinCore.lean:187 | `assoc_xy_x_y` | on 𝕆: `assoc (x*y) x y = 0` | UNANCHORED | U7: cell |
| 10 | ArtinCore.lean:196 | `assoc_xy_y_x` | on 𝕆: `assoc (x*y) y x = 0` | UNANCHORED | U7: cell |
| 11 | ArtinCore.lean:205 | `assoc_y_xy_x` | on 𝕆: `assoc y (x*y) x = 0` | UNANCHORED | U7: cell |
| 12 | ArtinCore.lean:219 | `assoc_gen4_inner_one` | `private`; `∀ b c ∈ gen4, assoc 1 b c = 0` | UNANCHORED | U2: private 16-leaf split |
| 13 | ArtinCore.lean:226 | `assoc_gen4_inner_x` | `private`; `∀ b c ∈ gen4, assoc x b c = 0` | UNANCHORED | U2 |
| 14 | ArtinCore.lean:255 | `assoc_gen4_inner_y` | `private`; `∀ b c ∈ gen4, assoc y b c = 0` | UNANCHORED | U2 |
| 15 | ArtinCore.lean:282 | `assoc_gen4_inner_xy` | `private`; `∀ b c ∈ gen4, assoc (x*y) b c = 0` | UNANCHORED | U2 |
| 16 | ArtinCore.lean:328 | `assoc_gen4_zero` | on 𝕆: `∀ a b c ∈ gen4 x y, assoc a b c = 0` (all 64) | UNANCHORED | U1: generator table assembled into #17; used only in ArtinCore. The "no trace identity needed" finding in its docstring is a route note, not a separate claim |
| 17 | ArtinCore.lean:349 | `assoc_vanishes_on_span4` | on 𝕆: `∀ u v w ∈ span ℝ {1,x,y,x*y}, assoc u v w = 0` | **ANCHOR** | → **PROOF-artin-theorem** `theorems[]`. Associator-side half of Artin; a named input to PROOF-quaternion-frame-maximal, PROOF-associative-composition-iff, PROOF-gradient-lies-in-host-kernel-algebra (§1.1) |

### 3.2 `proofs/QBP/Foundations/ArtinSpan.lean` (20)

| # | file:line | theorem | statement | disposition | anchor / class + rationale |
|---|---|---|---|---|---|
| 18 | ArtinSpan.lean:80 | `cdAlg_mul_zero` | `x * 0 = 0` on `CDAlg R n` | UNANCHORED | U4: `mul_zero` field of `instNonUnitalNonAssocRing` (l.93) |
| 19 | ArtinSpan.lean:85 | `cdAlg_zero_mul` | `0 * x = 0` | UNANCHORED | U4: `zero_mul` field (l.93) |
| 20 | ArtinSpan.lean:134 | `bilinear_mem_span` | bilinear `T` with `T a b ∈ span s` on `s×s` ⇒ `T x y ∈ span s` on the span | UNANCHORED | U3: generic lift |
| 21 | ArtinSpan.lean:173 | `one_mem_span_gen4` | `1 ∈ span4` | UNANCHORED | U6: `subset_span`. Also used in HolographicSubalgebra/InFlightAlgebra, but it is membership bookkeeping, not a claim |
| 22 | ArtinSpan.lean:177 | `x_mem_span_gen4` | `x ∈ span4` | UNANCHORED | U6 (same cross-module note) |
| 23 | ArtinSpan.lean:181 | `y_mem_span_gen4` | `y ∈ span4` | UNANCHORED | U6 (same) |
| 24 | ArtinSpan.lean:185 | `xy_mem_span_gen4` | `x*y ∈ span4` | UNANCHORED | U6 (same) |
| 25 | ArtinSpan.lean:190 | `xx_mem_span_gen4` | `x*x ∈ span4` (quadraticity) | UNANCHORED | U7: cell of `gen4_mul_mem_span` |
| 26 | ArtinSpan.lean:197 | `yy_mem_span_gen4` | `y*y ∈ span4` | UNANCHORED | U7 |
| 27 | ArtinSpan.lean:207 | `yx_mem_span_gen4` | `y*x ∈ span4` (swap identity) | UNANCHORED | U7 |
| 28 | ArtinSpan.lean:218 | `x_xy_mem_span_gen4` | `x*(x*y) ∈ span4` (left alternativity + quadraticity) | UNANCHORED | U7 |
| 29 | ArtinSpan.lean:229 | `xy_y_mem_span_gen4` | `(x*y)*y ∈ span4` | UNANCHORED | U7 |
| 30 | ArtinSpan.lean:241 | `xy_x_mem_span_gen4` | `(x*y)*x ∈ span4` | UNANCHORED | U7 |
| 31 | ArtinSpan.lean:253 | `y_xy_mem_span_gen4` | `y*(x*y) ∈ span4` | UNANCHORED | U7 |
| 32 | ArtinSpan.lean:264 | `xyxy_mem_span_gen4` | `(x*y)*(x*y) ∈ span4` | UNANCHORED | U7 |
| 33 | ArtinSpan.lean:276 | `gen4_mul_mem_span` | `∀ a b ∈ gen4 x y, a*b ∈ span4` (16 cells) | UNANCHORED | U1: generator table assembled into #34; used only in ArtinSpan |
| 34 | ArtinSpan.lean:312 | `span4_mul_closed` | on 𝕆: `u, v ∈ span ℝ {1,x,y,x*y} ⇒ u*v ∈ span ℝ {1,x,y,x*y}` | **ANCHOR** | → **PROOF-artin-theorem** `theorems[]`. Closure half of Artin (L4); a named input to four anchors (§1.1); already named in prose by PROOF-quatdouble-rho-invariant-mul-closed and PROOF-gradient-lies-in-host-kernel-algebra |
| 35 | ArtinSpan.lean:324 | `mem_span4Subalgebra` | `@[simp]`: `z ∈ span4Subalgebra x y ↔ z ∈ span4` (`Iff.rfl`) | UNANCHORED | U6: definitional unfolding; no consumer |
| 36 | ArtinSpan.lean:340 | `adjoin_pair_le_span4` | `NonUnitalAlgebra.adjoin ℝ {x,y} ≤ span4Subalgebra x y` | UNANCHORED | U1: used only in ArtinSpan (by #37). Its statement is an inclusion and gives no dimension bound, so it is not "2-generated ⇒ dim ≤ 4" |
| 37 | ArtinSpan.lean:353 | `mem_span4_of_mem_adjoin` | `z ∈ adjoin ℝ {x,y} ⇒ z ∈ span4` | UNANCHORED | U1: membership form of #36, consumed only by `octonion_artin` (anchored), so it is covered by its consumer |

### 3.3 `proofs/QBP/Foundations/ArtinTrace.lean` (5)

| # | file:line | theorem | statement | disposition | anchor / class + rationale |
|---|---|---|---|---|---|
| 38 | ArtinTrace.lean:51 | `reCoord_add` | `(x + y).coord 0 = x.coord 0 + y.coord 0` on `CDAlg ℝ n` | UNANCHORED | U5: `rw [add_coord]` |
| 39 | ArtinTrace.lean:57 | `N_add` | `N (x + y) = N x + N y + 2 * bil x y` on `CDAlg ℝ n` | **ANCHOR** | → **PROOF-norm-form-bilinear** `theorems[]` (the polar-form anchor). Named input to LeftMulDet `octonion_bil_comp` and to `liftLeaf_gradV_eq` (§1.1). **Name-collision flag:** `QBP.Foundations.CrossProduct.N_add` (CrossProduct.lean:79, general `CommRing R`) states the same identity and is already file-anchored. The ledger entry must use the qualified name `QBP.Foundations.CDAlg.N_add` (see cohort plan §3). A Lean-side dedupe is a separate, optional follow-up |
| 40 | ArtinTrace.lean:69 | `mul_self_add` | `(x+y)*(x+y) = x*x + (x*y + y*x) + y*y` | UNANCHORED | U5: distributivity + `abel`; used only in ArtinTrace |
| 41 | ArtinTrace.lean:86 | `cdAlg_mul_add_swap` | `∀ x y : CDAlg ℝ n, x*y + y*x = (2 Re x)•y + (2 Re y)•x − (2 bil x y)•1` | **ANCHOR** | → **PROOF-cd-product-formula** `theorems[]`: the polarization of `cdAlg_sq_eq`, which that anchor already holds; it holds at every CD level `n`. Named input to CrystalHosting `mul_swap_eq` (PROOF-order-three-automorphism-fixes-ell) and to ArtinSpan |
| 42 | ArtinTrace.lean:120 | `cdAlg_mul_add_swap_pure` | `Re x = Re y = 0 ⇒ x*y + y*x = −(2 bil x y)•1` | **ANCHOR** | → **PROOF-cd-product-formula** `theorems[]`. Pure-element form ("imaginary elements anticommute up to a scalar"); named input to `mul_swap_self_pure` in RuleFlowLeafFoliation, whose anchor's description cites it |

### 3.4 Class counts (UNANCHORED-BY-DESIGN, 37)

| U1 | U2 | U3 | U4 | U5 | U6 | U7 | Σ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 7 | 4 | 2 | 2 | 5 | 5 | 12 | **37** |

U1 = #4, 5, 7, 16, 33, 36, 37 · U2 = #12–15 · U3 = #6, 20 · U4 = #18, 19 · U5 = #1, 2, 3, 38, 40 · U6 = #21–24, 35 · U7 = #8–11, 25–32.

## 4. What landing the cohorts does to the audit

- The tool matches `theorems[]` entries by **bare name** (`anchor_inverse_audit.py` `anchor_lean_refs`). Adding the 5 names drops the orphan count **42 → 37**. The `N_add` case needs saying explicitly: the Cohort C entry is the qualified `QBP.Foundations.CDAlg.N_add`, but the tool strips the namespace and matches the bare name `N_add`, so the entry lowers the orphan count (ArtinTrace.lean:57 stops being an orphan) even though `CrossProduct.N_add` (CrossProduct.lean:79, already file-anchored) shares that bare name. The qualified name is for the *ledger's* benefit, not the tool's: it records which `N_add` the anchor means. Which one the consumers bind is inferred from their `open` lines only. `LeftMulDet.lean:54` and `RuleFlowLeafFoliation.lean` `open QBP.Foundations.CDAlg` and do not open `QBP.Foundations.CrossProduct`; `SeamSpectrum` calls `CrossProduct.N_add` fully qualified. The elaboration check (`#check @N_add` in the consumer's namespace, under `run-bounded`) is owed to the encoder PR (cohort plan, Cohort C). The baseline is bumped with `--update-baseline` in the same commit (precedent: `scripts/encode_697_leaf_foliation_anchor.py`).
- After that, the 37 UNANCHORED-BY-DESIGN rows are still counted as orphans, because the gate is a count ratchet. Turning them into *declared* residuals (an explicit allowlist with these per-theorem reasons) is **#627** (open; AC2 there cites #619's per-file reasons, and §3 above is the per-theorem source for it). Until #627 lands, #464 AC5 ("~0 orphans") cannot be met with honest dispositions. The 37 are not anchor debt.

## 5. Flags (source-reading, not acted on)

1. **Bare-name matching is ambiguous.** The corpus has 31 bare theorem names that occur more than once (e.g. `N_add`). `theorems[]` entries are `{name, status}` with no file or namespace, so a name entry can match a theorem the anchor does not mean. This is a tool and schema observation for #627 (match on `lean_companion_theorems` qualified names), not a defect in any current anchor.
2. **Under-recorded dependency edges.** `PROOF-artin-theorem.prediction_chain` is `[]`, but its proof depends on PROOF-ops-alternativity-ladder (`octonion_alternative`), the flexibility law (`assoc_diag_flex`, OctonionLaws), and PROOF-cd-product-formula (`cdAlg_sq_eq`). The consumers in §1.1 do not chain to the anchors their inputs belong to. The cohort plan lists these edges.

## 6. AC1 check: is `analysis/foundations-inverse-anchor-audit.md` the "full per-theorem walk"?

AC1 reads: "`analysis/foundations-inverse-anchor-audit.md` authored — full per-theorem walk of the 254 corpus". The corpus is now **1945 theorems** (`stats.theorems_total` in `analysis/foundations-inverse-anchor-audit.json`; 254 was the #458 baseline).

**Verdict: not met as worded.** The tool-generated report is the regenerable audit (AC5's "re-run" is met structurally by #584). It is not a per-theorem walk, for three reasons:

| Gap | Evidence |
|---|---|
| The `.md` lists no theorems. It gives a summary table and a by-directory orphan count, and points to the JSON | `analysis/foundations-inverse-anchor-audit.md` §5 |
| The JSON lists only the 42 orphans, not all 1945 theorems or their anchor | JSON keys `orphans, phantoms, stale, stats` |
| "Anchored" is file-level: a theorem counts as anchored if any anchor cites its file. The report says this itself ("`lean_side_orphans` is a LOWER BOUND") | report §1 note |

The nearest existing per-theorem walk is `docs/cth/619-orphan-disposition-full.md`: 742 parsed rows (the header says 748) with anchor id or reason, generated 2026-09-04. Matching (file basename, theorem name) (Appendix A (b)), **731** of the current 1945 theorems have a row there and **1214** do not. 11 of its rows no longer match a current theorem.

Name-level heuristic, for scale only (Appendix A (a)). **388** of the 1945 are named in some anchor's `theorems[]`. **673** are named in `theorems[]`, `lean_theorem` or `lean_companion_theorems` (bare-name match; 31 bare names are duplicated, so this is approximate). The gap between "file-anchored" (1903) and "named" (673) is the population a real per-theorem walk would have to classify.

**What would satisfy AC1 without writing 1945 rows by hand.** Have the tool emit one row per theorem: `name · file:line · anchored-by ∈ {name, qualified-name, file-only, none} · anchor id(s)`. That is mechanical (the data is already in `anchor_inverse_audit.py`'s `theorems`/`ref_names`/`ref_files`). It belongs with #627, since the allowlist needs the same per-theorem join. The alternative is a scope ruling: qbp-oppenheimer (theory) or the beekeeper (process) re-reads AC1 as "the orphan set is exhaustive at file granularity". This PR does neither. It records the gap.

## 7. Anchored: `OctonionAutBranching.lean` (#755), 2026-10-29

`proofs/QBP/Foundations/OctonionAutBranching.lean` (#755 AC1) adds **55** theorem declarations (41 public, 14 `private`). Before the #755 AC4 anchor landed, the audit on the #755 branch (PR #787, head `43ae30a`) reported `orphans=97` (42 + 55) and failed the per-file ratchet for this file (55 > 0), by design.

| Disposition | Theorems | Status |
|---|---:|---|
| **ANCHOR — #755 AC4, landed at PR #787 commit `8ad0978`** | 55 (whole file) | The AC4 PROOF anchor (`INSIGHT-octonion-quaternion-branching` core, minted by the confined writer, qbp-implementor) cites this file as `proof_file`. That anchors all 55 for the tool. Headline witnesses: `gamma_mul`, `gamma_fixes_hosted`, `gamma_id_iff`, `gamma_bijective` (plus the `gammaAut : CDAut 3` definition). The other 50 declarations are by-design helpers with no standalone claim: `Fin 4`/`Fin 8` index combinatorics, the `oLo`/`oHi` Cayley–Dickson doubling law, the ℍ-conjugation anti-automorphism, unit-quaternion middle-cancellation, and additivity/homogeneity of the halves. They exist only to prove the five witnesses and are anchored through `proof_file`. NOT-claimed clauses: the module docstring and the anchor description. |

**Sequencing honoured, not bypassed.** The baseline was **not** bumped on the Lean-only commits (`50da2e8`, `43ae30a`); the inverse-audit job stayed red there until the AC4 anchor landed (`8ad0978`). `--update-baseline` was then run once, in its own commit (`8bcc073`), recording `OctonionAutBranching.lean: 55` as anchored per-file growth, as the tool's own message requires ("New theorems must ship with a CTH anchor; then run --update-baseline"). The job passes at `8bcc073`. Axiom closures for all 41 public theorems: `proofs/QBP/Foundations/OctonionAutBranching.axioms.txt`.

## Appendix A. Reproduce the derived figures

Run from the repo root with `python3`. It is read-only and imports the audit tool's own enumerator. Output at `656d462`:

```
theorems 1945 | named in theorems[] 388 | named in theorems[]/lean_theorem/companions 673 | duplicated bare names 31
619 rows parsed 742 | current with a row 731 | current without 1214 | 619 rows unmatched 11
```

Then (c) prints one line per orphan that has a consumer outside its own file. Its `N_add` line also lists `CrossProduct.lean:N_add`/`cdAlg_polar_sq`, which are hits on the *other* `N_add` (a regex cannot tell namespaces apart; see §1.1). Its `*_mem_span_gen4` lines are the U6 cross-module uses.

```python
# Run from the repo root: python3 <this file>
import sys, re, json, glob, bisect, collections
sys.path.insert(0, "scripts")
import anchor_inverse_audit as t

th = t.collect_theorems("proofs")                      # (name, path, line)
led = json.load(open(t.DEFAULT_LEDGER, encoding="utf-8"))["anchors"]

# (a) name-level counts
in_thms = {(x["name"] if isinstance(x, dict) else x) for a in led for x in (a.get("theorems") or [])}
in_lt = {q.split(".")[-1] for a in led
         for q in [a.get("lean_theorem")] + (a.get("lean_companion_theorems") or []) if isinstance(q, str)}
dups = sum(1 for v in collections.Counter(n for n, _, _ in th).values() if v > 1)
print("theorems", len(th), "| named in theorems[]", sum(n in in_thms for n, _, _ in th),
      "| named in theorems[]/lean_theorem/companions", sum(n in in_thms | in_lt for n, _, _ in th),
      "| duplicated bare names", dups)

# (b) #619 per-theorem table vs current corpus, key = (file basename, name)
pairs, mod = set(), None
for line in open("docs/cth/619-orphan-disposition-full.md", encoding="utf-8"):
    m = re.match(r"### `(.+?)`", line)
    if m:
        mod = m.group(1)
    m = re.match(r"\| `(.+?)` \|", line)
    if m and mod:
        pairs.add((mod, m.group(1)))
cur = {(p.split("/")[-1], n) for n, p, _ in th}
print("619 rows parsed", len(pairs), "| current with a row", len(cur & pairs),
      "| current without", len(cur - pairs), "| 619 rows unmatched", len(pairs - cur))

# (c) consumers of an orphan outside its own file -> enclosing theorem
by_file = collections.defaultdict(list)
for n, p, l in th:
    by_file[p].append((l, n))
for v in by_file.values():
    v.sort()
orph = json.load(open("analysis/foundations-inverse-anchor-audit.json"))["orphans"]
for o in orph:
    pat = re.compile(r"(?<![A-Za-z0-9_'.`])(?:CDAlg\.)?" + re.escape(o["name"]) + r"(?![A-Za-z0-9_'`])")
    hits = set()
    for f in glob.glob("proofs/**/*.lean", recursive=True):
        if ".lake" in f or f == o["file"]:
            continue
        for i, line in enumerate(open(f, encoding="utf-8").read().split("\n"), 1):
            code = line.split("--")[0]
            if line.strip().startswith(("/-", "#", "*")) or not pat.search(code):
                continue
            v = by_file.get(f, [])
            k = bisect.bisect_right([x[0] for x in v], i) - 1
            if k >= 0:
                hits.add(f"{f.split('/')[-1]}:{v[k][1]}")
    if hits:
        print(o["name"], sorted(hits))
```
