# Batch-A Adjudication Worksheet — v5.13 fold-in (24 anchors)

**For:** @qbp-oppenheimer (QBP #509, v5.13 fold-in)
**Prepared by:** qbp-implementor (preparation only — theory rulings are Oppenheimer's)
**Date:** 2026-06-04
**Source proposals:** `paper/CTH-Inventory-Reconciliation-Cycle2-Proposals.md` §4.2 (vintage ~2026-05-14)
**Canonical inventory:** `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` (150 anchors)
**Anchor source-of-record:** `archive/cth-inventory/confluent-trust-inventory-v5.13.json` (full diffs read)

> **READ FIRST — status of the inputs.**
> 1. The §4.2 proposals doc compared v5.13 against an **old** v5_3 (141 anchors). The **canonical inventory is now v5_3.v0.3 (150 anchors)**. I re-ran the collision check against canonical: **all 24 Batch-A anchors are genuinely absent from canonical v0.3** — none are silent dupes. Several *relate to* (cite in `prediction_chain`, or sharpen/falsify) anchors that ARE canonical; those are flagged in the collision column.
> 2. The proposals doc predates four post-April rulings. The biggest live effect: the §4.2 doc treats `PRED-TOV-limit-sqrt-7-over-3` as a clean prediction, but the v5.13 stream itself now carries anchors (`FLAG-tov-eos-shape-underdetermined`, `INSIGHT-eos-integration-shifts-tov-by-30pct`) that **falsify it as a global M_max claim**. The doc's "include as-is" framing for the TOV cluster is stale — see the contestable list.
> 3. **Recommendations below are recommendations, not rulings.** RECOMMENDATION column is advisory; CONFIDENCE column states why and how firm.

---

## Supersession key (rulings the proposals predate)

| Tag | Ruling | Source | Bites which Batch-A anchors |
|---|---|---|---|
| **EC-DEAD** | Entropy-cone division-algebra inversion FALSIFIED; ℂ→ℍ does not shrink the cone. `PROOF-division-algebra-entropy-cone-mapping` + `INSIGHT-entropy-cone-division-algebra-inversion` now `incoherent`, killed_by HQM-MMI report. | #484 dispositions; `analysis/HQM-MMI-derive-or-die-report.md` | `PRED-hypergraph-cmb-camb-rerun` (chain depends on the killed mapping) |
| **COLLIDER-DEAD** | "tower rungs = collider-scale symmetry restorations" DEAD; entropy→mass bridge cannot produce hierarchy. | `analysis/E-rung-threshold-derivation-2026-06-03.md` §6; debate doc | None of the 24 assert collider-rung mapping directly (clear) |
| **42-COINCIDENCE** | 42⟷Moreno is COINCIDENCE (no equivariant bijection); observability of crystallisation DEAD; L_a non-unitarity promissory. | `docs/foundations/debate-O2-invariant-2026-06-03.md` FINAL JOINT STATEMENT + obligations D2/D4 | None of the 24 assert a 42⟷Moreno bijection (clear) |
| **LADDER-k** | Selection counts are **3, 7, 8, 50** (kernel-checked); naive k=2ⁿ−1=15 is FALSE **at the 𝕊→𝕆 rung only**. The 𝕆→ℍ rung k=7 is UNCHANGED. | `analysis/E-rung-threshold-derivation-2026-06-03.md` §2; debate D1/D3 | **Does NOT touch** the ln7 anchors (`PROOF-seed-mass-from-ln7`, `PROOF-fano-choice-information`) — those are the 𝕆→ℍ rung. Confirm-only. |
| **a₀-EVOL** | a₀(z) saturating form favoured over linear (1+z) (IFU Δχ²=+72.89); but best-fit F_max≈13.4, NOT 7 — internal tension in the v5.13 stream's own notes. | v5.13 anchor notes (Sessions 20–23) | The 6 a₀/BTFR anchors |

---

## Worksheet (one row per anchor)

| # | anchor_id | claim (1 line) | collides-with-canonical? | superseded-by? | RECOMMENDATION | confidence + why |
|---|---|---|---|---|---|---|
| 1 | `FLAG-tov-eos-shape-underdetermined` | TOV w/ QBP EOS gives M_max=3.28 M☉, 49% above √(7/3) pred → bump shape underdetermined or √(7/3) is a normalisation | Relates to canonical `PRED-TOV-limit-sqrt-7-over-3` (marginal), `Q27-TOV-limit-from-Fano` | No — this IS the corrective finding | **include** | HIGH — `resolved` status, honest negative; documents that √(7/3) is not a derived global M_max. Preserves history. |
| 2 | `INSIGHT-cross-platform-per-feature-class` | Γ-test discriminates within feature class (revival 6.5σ) but cross-class mixing only 0.5σ | Chains `PRED-gamma-universality` (canonical, TWO_AXIS) | No | **co-sign-only** (INSIGHT-) | HIGH — methodology insight, not a physics claim; co-sign per META/INSIGHT rule. |
| 3 | `INSIGHT-eos-integration-shifts-tov-by-30pct` | Robust QBP TOV is M_TOV∈[2.6,2.8] M☉ — **mutually exclusive** with √(7/3)=2.20 | Directly contradicts canonical `PRED-TOV-limit-sqrt-7-over-3` claim | No — corrective | **co-sign-only** (INSIGHT-) **but flag** | MED — INSIGHT class → co-sign; BUT it asserts a numeric regime that supersedes the √(7/3) global reading. Oppenheimer should note it forces a status change on the canonical TOV anchor. See contestable #1. |
| 4 | `INSIGHT-gamma-needs-cross-platform` | Single-platform Γ test only 0.6σ; multi-platform pooling needed for multi-σ | Chains `PRED-gamma-universality` | No | **co-sign-only** (INSIGHT-) | HIGH — test-design insight. |
| 5 | `META-physical-mapping-status-field` | Schema: add physical_mapping_status (verified/conjectural/falsified) | Schema field (already used across v5.13 anchors) | No | **co-sign-only** (META-) | HIGH — META schema field; per §4 rule META→Oppenheimer co-sign. (Schema mechanics are cth-implementor's; the enum semantics are the theory-relevant part Oppenheimer co-signs.) |
| 6 | `META-regime-of-validity-field` | Schema: add regime_of_validity field (bump_peak/virial/de_era…) | Schema field | No | **co-sign-only** (META-) | HIGH — same as #5. This field is what makes the TOV-regime distinction expressible; worth co-signing. |
| 7 | `OBS-btfr-z-range-validity` | BTFR (1+z) correction holds 1<z<10; z≥10 overshoot resolved by saturating F_max=7 | Chains `PRED-btfr-mass-correction`, `PRED-a0-redshift-linear` (canonical) | a₀-EVOL (partially — note says saturating resolves it) | **include** | MED — `resolved` status; empirical compilation. Recommend include; the resolution it cites (F_max=7) is itself contestable (see #11/contestable #2). |
| 8 | `OBS-jades-gs-z14-0-vrot-lower-100` | ALMA tentative v_rot>100 km/s — above saturating(88), below linear(118) pred | Chains the a₀ predictions | No (live observation) | **include** | HIGH — `marginal`, observational anchor with explicit caveats; preserves a real literature data point. |
| 9 | `OPEN-Q-parent-bh-retardation-derivation` | Open: derive retardation kernel → F_max=dim(Im 𝕆)=7 rigorously | Chains `PRED-a0-saturating-*` | No (it IS the open task) | **include** | HIGH — `untested`/OPEN by design; documents the gap. Include as open question. |
| 10 | `PRED-a0-redshift-linear` | a₀(z)=a₀(0)(1+z) from M(a)=M₀a | Chains canonical `PROOF-M-proportional-to-a`, `PRED-holographic-boundary-gravity` | a₀-EVOL — now the **late-time asymptote only**; IFU favours saturating | **include** (with regime_of_validity intact) | MED — `marginal`; superseded as a global form but valid in DE-era regime (anchor's own regime_of_validity says so). Include, do not kill — it's the asymptotic limit of the saturating form. |
| 11 | `PRED-a0-saturating-Fmax-7` | a₀(z) saturates with F_max=7=dim(Im 𝕆) | Chains `PRED-a0-redshift-linear`, `PROOF-fano` | a₀-EVOL — **internal tension**: status `coherent` but note records best-fit F_max=**13.4** | **include-with-concern** | LOW — status `coherent` is not supported by its own note (best-fit 13.4 ≠ 7). Recommend Oppenheimer DOWNGRADE to marginal before include, or demand the F_max=7 justification. See contestable #2. |
| 12 | `PRED-a0-saturating-matter-era` | Matter-era a₀(z) saturates (phenomenological reg) | Chains `PRED-a0-redshift-linear`, `PRED-btfr-mass-correction` | a₀-EVOL | **include** | MED — `marginal`, honestly labelled phenomenological. Include as marginal. |
| 13 | `PRED-a0-saturation-factor-fano` | Saturation factor = dim(Im 𝕆)=7 (Fano lines) | Chains `PROOF-fano-choice-information` | a₀-EVOL — same F_max tension as #11 | **include-with-concern** | LOW — duplicates the F_max=7 claim of #11 at `marginal`; the "empirically-best" claim conflicts with #11's best-fit 13.4. Oppenheimer should reconcile #11/#13. |
| 14 | `PRED-btfr-mass-correction` | M_inferred/M_true=(1+z) in deep-MOND | Chains canonical `OBS-rotation-anomaly`; relates `OBS-jwst-early-galaxies` | a₀-EVOL — over-corrects at z>10 (matter-era saturation) | **include** | MED — `coherent`, Lean-backed identity; regime_of_validity already notes the z>10 over-correction. Include. |
| 15 | `PRED-hypergraph-cmb-camb-rerun` | Multi-party hypergraph correlator gives k-flat ν=1+dim(𝕆)·Q=6.333, Ω_m/Ω_b match 0.68% | Chains canonical `COMP-branch-A-cmb-boundary-analysis` (incoherent), `INSIGHT-branch-A-hypergraph-boundary`, **`PROOF-division-algebra-entropy-cone-mapping` (KILLED, EC-DEAD)** | **EC-DEAD** — its chain rests on the killed entropy-cone mapping | **include-as-killed** OR **route-to-Oppenheimer for live-or-dead call** | LOW — `untested`. The hypergraph-boundary rescue inherits the entropy-cone mechanism that #484/HQM-MMI killed. STRONGEST candidate for include-as-killed. See contestable #3 — Oppenheimer must decide if the CAMB-rerun prediction survives independent of the dead cone mapping. |
| 16 | `PRED-jwst-kinematics-z14` | Pre-registered v_rot for GN-z11/JADES/UHZ1: saturating vs linear 25–30% apart | Chains the a₀ predictions | No (pre-registered test) | **include** | HIGH — `untested` pre-registration; clean discriminator. Include. |
| 17 | `PRED-tov-mass-at-bump-peak` | √(7/3) applied to its **actual** regime (ρ_c at peak): M=2.194 M☉ (0.3%) | Sharpens canonical `PRED-TOV-limit-sqrt-7-over-3`; chains `PRED-conformal-sound-speed-1-over-3` | a₀-N/A; this is the TOV-regime REPAIR (regime-specific, not global) | **include** | HIGH — `coherent`, regime_of_validity explicit (NOT global M_max). This is the honest re-scoping of the √(7/3) claim. Include — and it pairs with #1/#3 to resolve the TOV cluster. |
| 18 | `PROOF-alpha-particle-quaternion` | ⁴He mass number = dim ℍ = 4 | New; chains canonical `PROOF-quat-closure` | No | **include** | HIGH — `coherent`, Lean sorry_count 0, type_1_direct algebraic identity. See PROOF-status note below. |
| 19 | `PROOF-fano-choice-information` | log(7 Fano lines) = ln 7 (bridges Fano→M_seed entropy) | New; chains canonical `PROOF-hurwitz`, AXIOM-1 | LADDER-k — **NOT affected** (this is the 𝕆→ℍ k=7 rung, untouched by the k=15→8 𝕊→𝕆 correction) | **include** | HIGH — `coherent`, Lean sorry 0. Explicitly survives the ladder correction. |
| 20 | `PROOF-iron-56-double-octet` | ⁵⁶Fe mass number = 7×8 = dim(Im 𝕆)×dim 𝕆 (=14×4) | New; formalises canonical `INSIGHT-iron-handoff-...`; chains `PROOF-fano` | No | **include** | HIGH — `coherent`, Lean sorry 0, type_1_direct. |
| 21 | `PROOF-iron-to-ns-bridge` | iron-56 & TOV both depend on dim(Im 𝕆)=7; (M_TOV/M_Ch)²=7/3 | New; chains `PROOF-iron-56-double-octet`, **`PRED-TOV-limit-sqrt-7-over-3`** | Indirect TOV — uses the (M_TOV/M_Ch)²=7/3 identity, which #1/#3 show is NOT the physical global M_max | **include-with-concern** | MED — the *algebraic* identity (7/3) is fine (Lean sorry 0); but the physical "how heavy a remnant can be" framing inherits the falsified √(7/3) global reading. Recommend include but flag the physical-mapping caveat (use META-physical-mapping-status = conjectural). |
| 22 | `PROOF-oxygen-16-sedenion` | ¹⁶O mass number = 4² = dim 𝕊 = 16 | New; chains `PROOF-alpha-particle-quaternion` | No | **include** | HIGH — `coherent`, Lean sorry 0, type_1_direct. |
| 23 | `PROOF-seed-mass-from-ln7` | M_seed solves S_BH(M)=ln 7 ≈0.39 M_Pl | New (NOT in canonical despite M_seed usage elsewhere); chains `PROOF-fano-choice-information` | LADDER-k — **NOT affected** (𝕆→ℍ k=7 rung). Consistent with E-rung doc's M_seed row. | **include** | HIGH — `coherent`, Lean sorry 0. Confirmed against E-rung-threshold derivation (same M_seed = √(ln7/4π)·M_p). |
| 24 | `PROOF-silicon-28-fano-ladder` | ²⁸Si mass number = 7×4 = dim(Im 𝕆)×dim ℍ (alpha-ladder exhausts 7 Fano lines) | New; chains `PROOF-alpha-particle-quaternion`, `PROOF-fano` | No | **include** | HIGH — `coherent`, Lean sorry 0, type_1_direct. |

---

## PROOF-status anchors — evidence vs the 5 anchor-rule termination types

The proposals doc routes PROOF-* anchors to Oppenheimer (not INST→cth). Eight Batch-A anchors carry PROOF- prefix (#18–24 plus #15). For the nuclear/algebra ones (#18,19,20,22,23,24) the cited evidence is a **kernel-checked Lean theorem, sorry_count 0, type_1_direct** — these are pure algebraic-identity terminations (mass number = algebra dimension), the strongest termination class; they are not empirical predictions and do not need observational closure. **#21 (`PROOF-iron-to-ns-bridge`)** and **#15 (`PRED-hypergraph-cmb-camb-rerun`)** are the exceptions: #21 mixes a valid algebraic identity with a falsified physical reading (TOV global M_max); #15 is `untested` and rests on a killed chain. Neither #21 nor #15 meets a clean termination type on the *physical* side — the Lean theorem terminates the algebra only.

---

## Counts by recommended disposition

| Disposition | Count | Anchors |
|---|---|---|
| **include** | 12 | #1, #7, #8, #9, #10, #12, #14, #16, #17, #18, #19, #20, #22, #23, #24 — *(15 listed; see note)* |
| **include-with-concern** | 3 | #11, #13, #21 |
| **include-as-killed** (or route for live-or-dead) | 1 | #15 |
| **co-sign-only** (META-/INSIGHT-) | 5 | #2, #3, #4, #5, #6 |
| **drop-superseded** | 0 | — (we preserve history; nothing is silently dropped) |
| **route-to-cth** (INST-*) | 0 | — (no INST- anchors in Batch-A) |

> **Count reconciliation:** plain **include = 12** (#1,7,8,9,10,12,14,16,18,19,20,22,23,24 minus the 2 promoted to "with-concern"/"killed" already excluded) — precisely: include {1,7,8,9,10,12,14,16,17,18,19,20,22,23,24} = **15**, include-with-concern {11,13,21} = **3**, include-as-killed {15} = **1**, co-sign-only {2,3,4,5,6} = **5**. Total = 15+3+1+5 = **24**. ✓
> (Disregard the first include-row's parenthetical; authoritative split is the reconciliation line: **15 include / 3 include-with-concern / 1 include-as-killed / 5 co-sign-only / 0 drop / 0 route-to-cth = 24**.)

---

## The 3–5 genuinely contestable rulings (Oppenheimer's closest attention)

1. **The TOV cluster — #1 / #3 / #17 / #21 vs canonical `PRED-TOV-limit-sqrt-7-over-3`.**
   The proposals doc treats these as routine includes. They are not routine: together they **demote √(7/3) from a global M_max prediction to a regime-specific (bump-peak) result**, and assert a *competing* robust prediction M_TOV∈[2.6,2.8] M☉. Canonical `PRED-TOV-limit-sqrt-7-over-3` is currently `marginal`; folding in #1/#3 should arguably trigger a status/physical_mapping_status change on the canonical anchor (→ falsified-as-global, conjectural-as-regime). This is a theory ruling, not a fold-in mechanic. **Highest-stakes contest.**

2. **`PRED-a0-saturating-Fmax-7` (#11) status `coherent` vs its own best-fit F_max=13.4.**
   The anchor claims algebraic F_max=7 and status `coherent`, but its embedded Session-22 note records IFU best-fit F_max=**13.378**. 13.4 is roughly 2×7 — it is NOT dim(Im 𝕆)=7. Either the algebraic identification is wrong, or the data disfavours it. `coherent` looks unjustified. #13 duplicates the claim at `marginal` and calls 7 "empirically-best," directly contradicting #11's note. Oppenheimer should reconcile #11↔#13 and likely downgrade #11.

3. **`PRED-hypergraph-cmb-camb-rerun` (#15) vs EC-DEAD.**
   Its `prediction_chain` includes `PROOF-division-algebra-entropy-cone-mapping`, which #484 + the HQM-MMI report killed (`incoherent`). The CAMB-rerun prediction (ν=6.333, Ω_m/Ω_b match 0.68%) may or may not survive **independently** of the dead cone-inversion mechanism. If it depends on it → **include-as-killed** with killed_by=HQM-MMI report. If the multi-party hypergraph correlator can be motivated without the entropy-cone inversion → it stays a live `untested` prediction. **This is a derive-or-die-shaped call only Oppenheimer can make.** Recommend: include-as-killed unless a chain-independent derivation is exhibited.

4. **`INSIGHT-eos-integration-shifts-tov-by-30pct` (#3) — INSIGHT co-sign vs substantive supersession.**
   Routing rules say INSIGHT→co-sign-only. But this anchor's *content* is the supersession of the TOV global prediction (it explicitly says the two predictions are "mutually exclusive"). Treating it as a mere co-sign understates its effect on canonical #1's TOV anchor. Oppenheimer should co-sign AND act on its implication for the canonical TOV status (ties to contestable #1).

5. **`PROOF-iron-to-ns-bridge` (#21) — algebra-true / physics-falsified split.**
   The (M_TOV/M_Ch)²=7/3 identity is Lean-clean, but the physical claim ("how heavy a collapsed remnant can be") rides on the same √(7/3) global reading that #1/#3 falsify. Recommend include with physical_mapping_status=conjectural (or falsified-as-physics), keeping the algebraic theorem. Contestable because the proposals doc presents it as a plain coherent PROOF.

---

## Where the proposals doc's OWN recommendation is now wrong (post-April rulings)

- **The entire TOV sub-cluster (#1, #3, #17, #21).** §4.2 lists each as a flat "→ @qbp-oppenheimer decides on inclusion (scientific content)" with no signal that the √(7/3) global prediction has since been falsified by the v5.13 stream's own integration results. The doc (2026-05-14) predates the regime-split resolution baked into the anchors' Session-19+ notes. The doc's implicit "these are coherent QBP predictions" framing for `PROOF-iron-to-ns-bridge` and the canonical √(7/3) anchor is stale: the **physical** mapping is falsified-as-global; only the regime-specific (#17) and algebraic-identity readings survive.

- **`PRED-hypergraph-cmb-camb-rerun` (#15).** §4.2 lists it as a neutral scientific-content inclusion. It predates EC-DEAD (#484 / HQM-MMI ratified). Its chain depends on a now-`incoherent`, killed anchor. The doc's neutral framing is wrong; this needs an include-as-killed or a chain-independent rescue, not a plain include.

- **`PRED-a0-saturating-Fmax-7` (#11) status.** Not a doc error per se (the doc only carries the summary `coherent`), but the `coherent` status is contradicted by the anchor's own best-fit-13.4 note — anyone reading only §4.2's summary table would fold it in as coherent, which the data does not support.

**No anchor needs drop-superseded:** per the kill-history rule, falsified claims (#1/#3 TOV, #15 cone-dependent) are preserved with killed_by/killed_note or physical_mapping_status=falsified, never silently removed.
