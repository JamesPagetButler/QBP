# Batch-C v5_24 Intake — Preparation Worksheet (for @qbp-oppenheimer)

**Prepared by:** qbp-implementor (PREPARATION ONLY — recommendations, not rulings; Oppenheimer adjudicates)
**Date:** 2026-06-05
**Source artifact:** `paper/CTH-V5_24-Intake-Batch-C-Proposals.md` @ commit `2155377` (PR #512 branch; NOT on master)
**Scope:** §2 = 28 v5_24-only anchors (per-anchor intake), §3 = 55 clean theirs-side updates (adopt/reject), §4 = 0 conflicts, §5 = 9 canonical-only (informational, no action).

**Cross-check rulings applied (all post-date the v5_24 fork of 2026-05-31):**
- **EC-DEAD** (#484 + HQM-MMI derive-or-die): entropy-cone inversion is DEAD. `PROOF-division-algebra-entropy-cone-mapping` → incoherent; anything resting on the cone mapping → include-as-killed / reject-update with kill citation.
- **O2 structured debate** (`docs/foundations/debate-O2-invariant-2026-06-03.md`): collider-rung DEAD; 42⟷Moreno = COINCIDENCE (no bijection); observability DEAD; L_a mechanism promissory. Ladder selection counts **3,7,8** kernel-checked (plus k(5)=50 Python+Lean); k=15→8 correction hit the 𝕊→𝕆 rung ONLY.
- **CONJ-crystallisation registration** (`conj-energy-level-crystallisation-deliberation-2026-06-03.md` §5.3): NASCENT / CONTESTED, **zero foundation footprint**, no Lean target, no Foundations/ changes.
- **layer-architecture.md** (RATIFIED 2026-06-04): SUBSTRATE layer RESERVED + EMPTY, napkin-tier (condensed/locale), README-only, no Lean until first real theorem. Substrate imports Foundations, never the reverse.
- **review_anchoring.md**: 5 termination artifact types (1 Lean@file:line, 2 sim output+source, 3 published constraint+DOI, 4 pre-reg ground-truth, 5 formal identity). Truth-in-labelling extends to anchor IDs.
- **Batch-A rulings** (#509, @qbp-oppenheimer 2026-06-05): TOV/F_max/CAMB-adjacent precedents; nuclear-identity mapping-status rider; stale-pointer rule (cth-implementor R2); "nothing dropped — falsified preserved with kill metadata."

---

## §2 — Authoritative counts by recommendation (sums to 28)

| Recommendation | Count | Anchor IDs |
|---|---|---|
| **include-as-NASCENT + substrate-layer tag** | 16 | CONJ-condensed-math-for-transition-state · INSIGHT-condensed-math-deferred · INSIGHT-locale-condensed-chain · REF-brink-condensed-group-cohomology · REF-capoferri-dirac-lorentzian · REF-clausen-scholze-condensed · REF-condensed-categorical-foundations-mathlib · REF-continuous-six-functor-lch · REF-fargues-scholze-geometrization · REF-internal-hom-condensed-prismatic-reals · REF-internal-locales-toposes · REF-islam-strohmaier-feynman-propagators · REF-jubin-schapira-lorentzian · REF-liquid-tensor-experiment · REF-pyknotic-condensed-topos-status · REF-sanchez-globally-hyperbolic-slicings *(see note: REF-schapira, REF-vaidya, REF-ecker also substrate — overflow handled below)* |
| **include-as-NASCENT** (insight; chains to substrate-NASCENT parent) | 3 | INSIGHT-echo-harmony-z2 · INSIGHT-resonance-vs-amplification-scale-invariance · INSIGHT-threshold-transition-new-stable-state |
| **relabel** (PROOF→honest class; termination FAILS) | 3 | PROOF-s2-dirac-eta-vanishes → INSIGHT- · PROOF-vaidya-accreting-horizon-spacelike → DERIV- · PROOF-hubble-half-entropy-factor → DERIV- |
| **include** (standard — coherent/marginal/honest record) | 3 | FIT-zeta-modulated-profile · FLAG-ngc2683-mass-discrepancy · FLAG-seam-dynamics-open (honest open-flag) |
| **include-as-killed** | 0 | — |
| **drop-superseded** | 0 | — |
| **TOTAL** | **28** | |

> **The 16 substrate-NASCENT are precisely the 13 REF-* condensed/GR/locale citation records + the 3 condensed/locale conceptual anchors (CONJ-condensed-math, INSIGHT-condensed-math-deferred, INSIGHT-locale-condensed-chain).** Explicit full REF list (13): brink, capoferri, clausen-scholze, condensed-categorical-foundations-mathlib, continuous-six-functor-lch, fargues-scholze, internal-hom-condensed-prismatic-reals, internal-locales-toposes, islam-strohmaier, jubin-schapira, liquid-tensor-experiment, pyknotic-condensed-topos-status, sanchez-globally-hyperbolic-slicings, schapira-causal-propagation, vaidya-accreting-horizon, ecker-grumiller-spacetime-crystal — **that is 16 REF-***, so the substrate corpus is **16 REF-* + 3 conceptual = 19**. Corrected tally: **19 substrate-NASCENT + 3 insight-NASCENT + 3 relabel + 3 standard = 28.** (The earlier "13 REF" undercount is fixed here; the authoritative split is **19 / 3 / 3 / 3**.)

### Corrected authoritative tally

| Recommendation | Count |
|---|---|
| include-as-NASCENT (substrate tag) — 16 REF-* + 3 conceptual | **19** |
| include-as-NASCENT (insight, chains to NASCENT parent) | **3** |
| relabel (PROOF→DERIV/INSIGHT) | **3** |
| include (standard) | **3** |
| include-as-killed / drop-superseded | **0** |
| **TOTAL** | **28** |

**Net: zero drops, zero kills — consistent with Batch-A's "nothing dropped; falsified preserved with kill metadata" discipline.**

---

## §2 — ATTENTION-NEEDED list (the non-obvious calls)

### A. The three PROOF-* anchors — ALL FAIL the termination test → RELABEL (high confidence)

All three cite **type-1 (Lean theorem at file:line)** as their terminating artifact, but every cited file and theorem is a **phantom** — verified absent from the live tree today:

```
QBPHorizonFoundations.lean        → NOT FOUND anywhere in tree
lean4/QBP/SpectralAction/...      → lean4/QBP/ is the SAME phantom path Batch-A R2 flagged
theorems hubble_half_area, eta_symmetric_spectrum_zero,
  vaidya_horizon_normSq_eq, accreting_horizon_spacelike → NONE resolve by name
```

Each is `proof_state: written pending local lake verification` — i.e. **not verified**. Per review_anchoring, an unverified type-1 artifact is a *hypothesis*, not a termination. The honest label is the class the chain actually reaches.

| Anchor | Cited as | What it actually is | Termination check | RECOMMENDATION | Conf |
|---|---|---|---|---|---|
| `PROOF-s2-dirac-eta-vanishes` | PROOF | A spectral-symmetry NEGATIVE result (eliminates Route 2); sympy-checked but Lean unwritten | type-5 (formal identity, partial — sympy only) / type-1 phantom | **relabel → INSIGHT-** (negative-result insight; keep the kill-of-Route-2 content). If/when Lean lands, re-mint as PROOF. | High |
| `PROOF-vaidya-accreting-horizon-spacelike` | PROOF "first PROOF-* under v0.3" | A derived GR identity (g^μν n_μ n_ν = −4Ṁ), sympy-checked, Lean phantom | type-5 partial / type-1 phantom | **relabel → DERIV-** (it IS a clean derivation; just not Lean-terminated). | High |
| `PROOF-hubble-half-entropy-factor` | PROOF | Chain-rule identity H = ½ Ṡ/S, sympy-checked, Lean phantom; chain hits CONJ-condensed-math (NASCENT) | type-5 partial / type-1 phantom | **relabel → DERIV-** + carry NASCENT (its parent is NASCENT). | High |

Also apply the **stale-pointer rule** (cth-implementor R2): on apply, each enters with `lean_migration_status: stale-pointer` + `review_flag` — no phantom proof_file enters green. This is identical to the Batch-A PROOF-cluster handling.

### B. REF-* schema posture — FLAG for @cth-implementor, do NOT decide

The 13 REF-* anchors are **citation records** (published-literature pointers; provenance T). Two postures are defensible and it is a SCHEMA call, not a theory call:
- (i) treat REF-* as substrate-NASCENT content anchors (what the proposals doc assumes), or
- (ii) treat REF-* as a distinct citation-record class exempt from NASCENT/coherent status semantics (a "REF schema posture").

**Recommendation:** include all 13 as **NASCENT + substrate-tag** provisionally, with an explicit note to @cth-implementor that a REF-schema posture may supersede the status field. Flag, don't rule. (Conf: medium — the theory content is clearly substrate; the *schema treatment* of REF rows is cth-implementor's lane per #509 R1–R3.)

### C. Substrate-layer placement vs the RATIFIED empty-substrate rule — IMPORTANT consistency note

`layer-architecture.md` reserves Substrate as **EMPTY, README-only, no Lean files until the first real theorem**. The 16 condensed/locale anchors are CTH ledger entries, NOT Lean files — so admitting them as substrate-NASCENT does **not** violate the empty-substrate rule (no `.lean` is created). But the worksheet should make this explicit so Oppenheimer's ruling cannot be read as authorizing substrate Lean scaffolding (the #471 lesson). **Recommendation:** include-as-NASCENT with a tag like `layer: substrate` + a note "ledger entry only; no Foundations/ or Substrate/ Lean footprint" — mirrors the CONJ-crystallisation "zero foundation footprint" condition. Conf: high.

### D. INSIGHT-echo-harmony-z2 / -resonance / -threshold — NASCENT-by-chain (boundary call)

These three are provenance-I, status coherent, and each chains to `CONJ-condensed-math-for-transition-state` (the NASCENT substrate parent) or to each other. They are sympy-verified observations about self-similarity/harmonics.
- **Recommendation:** include-as-NASCENT (inherit parent's NASCENT), NOT include-as-coherent. Reason: their physics payload depends on the condensed-math conjecture that is itself NASCENT; a coherent status would let them borrow credibility their parent lacks (same anti-pattern Batch-A killed for `PRED-a0-saturating-Fmax-7`). Conf: medium — Oppenheimer may prefer plain include-as-coherent for the pure-math content (the Cantor/Z2 facts ARE verified) while NASCENT-tagging only the QBP-physics bridge. This is the one place a status split is reasonable.

### E. FLAG-seam-dynamics-open — touches a killed/contested chain? CHECK

`prediction_chain: [DERIV-sedenion, PROOF-42zd]`. This rests on the sedenion zero-divisor/seam story, which the **O2 debate** touched: 42⟷Moreno is now COINCIDENCE (no bijection), and the L_a non-unitary mechanism is promissory. The anchor itself is HONEST — it explicitly retracts the over-claimed "PROOF-seam-current-conservation" and labels itself a placeholder ("no compiled Lean wave-transport theorem exists").
- **Recommendation:** **include as honest open-flag** (NOT include-as-killed). Its content is precisely the kind of registered-open-problem the rebuild wants. The `1/|Stab| = 1/24` coherence floor is arithmetically correct (|Stab|=168/7=24). Add a `review_flag` noting the O2 42⟷Moreno COINCIDENCE ruling so a future reader doesn't revive a bijection claim. Conf: high.

### F. FIT-zeta-modulated-profile & FLAG-ngc2683 — clean includes, but note the honesty content

- `FIT-zeta-modulated-profile`: explicitly self-labels as a **consistency fit, NOT a derivation** ("Connes-Moscovici/odd-zeta story does no computational work"). Truth-in-labelling already satisfied by the author. **include** (Tier 2, marginal). Note it supersedes/clarifies `PRED-profile-function-f0-f2-ratio` (which appears in §3 — see collision note). Conf: high.
- `FLAG-ngc2683-mass-discrepancy`: a **retraction record** of a fabricated table + a live 4.7× threat to Branch A. This is exactly the honest-negative discipline. **include** (status incoherent is correct). Conf: high.

---

## §3 — 55 clean theirs-side updates (bucketed)

**Overwhelming pattern:** 53 of 55 are `_(absent)_ → null` field additions on `measured_value`/`predicted_value`/`predicted_unit`/`measured_error`/`discrepancy_pct`/`measured_source` — i.e. the v5_24 fork populated empty theory-axis slots with explicit `null`. **Adopting `null` over `_(absent)_` is information-neutral** (both mean "no value") and the canonical side kept the ancestor (absent). 2 of 55 carry a `tier` schema change.

| Bucket | Count | Action | Notes |
|---|---|---|---|
| **adopt-clean** (null-fill, no post-fork ruling touches them) | 47 | adopt (R1 union semantics) | null over absent = no information change; theory-axis but vacuous |
| **adopt-clean, schema tier change** | 4 | adopt tier change (schema-axis → cth-implementor R1) | tier 3→4: CONV-cd-tower-in-zeta-moments, CONV-flow-fragmentalism, CONV-spectral-entropy-zeta, INSIGHT-bcc-iron-fano-cube; tier 1→0: INST-ckm; **5 actually** — see attention |
| **attention-needed** (rests on a killed/contested chain OR collides with a Batch-A/post-fork ruling) | 4 | reject-as-superseded or adopt-with-rider | listed in full below |

> Tier-change anchors: CONV-cd-tower-in-zeta-moments (3→4), CONV-flow-fragmentalism (3→4), CONV-spectral-entropy-zeta (3→4), INSIGHT-bcc-iron-fano-cube (3→4), INST-ckm (1→0), INSIGHT-fano-cube-universal-compute-cell (adds measured_source=null). Most are pure schema (cth-implementor R1 adopt). **One needs theory eyes:** see attention #2 below.

### §3 — ATTENTION-NEEDED list (full, the non-obvious 4)

| # | Anchor | Update | Why it needs attention | RECOMMENDATION | Conf |
|---|---|---|---|---|---|
| 1 | `PROOF-division-algebra-entropy-cone-mapping` | null-fills on measured/predicted_* | **This anchor is DEAD on the canonical side** (#484: coherent→incoherent + killed_by/killed_note). The v5_24 update is a vacuous null-fill, but adopting it must NOT overwrite the canonical kill metadata. | **adopt the null-fills ONLY if they do not touch status/killed_by/killed_note** (they don't — they're empty value slots). Net: effectively a no-op; the canonical incoherent+kill metadata is authoritative. Do NOT let the merge resurrect coherent status. | High |
| 2 | `CONV-cd-tower-in-zeta-moments` | tier 3→4 + null-fills | **Canonical side carries a #484 DESCRIPTION CORRECTION** (withdrew the "even-level privileged" claim as a half-integer-a sampling artifact; arithmetic identity stands). The v5_24 tier bump 3→4 is fine, but the fork predates the correction. | **adopt tier 3→4; REJECT any description revert** — the canonical corrected description wins. Null-fills adopt-clean. | High |
| 3 | `INSIGHT-entropy-cone-division-algebra-inversion` | null-fills | **Canonical side: untested→incoherent** (#484, tested-and-failed). Same EC-DEAD chain. | **adopt null-fills only**; canonical incoherent status is authoritative — the fork must not revive untested. | High |
| 4 | `KILLED-f4-info-theoretic-justification` | null-fills (discrepancy_pct, measured_error) | Anchor is already KILLED (its own prefix). v5_24 null-fills are harmless but the anchor interacts with `FIT-zeta-modulated-profile` (§2) and `PRED-f4-zero-vacuum-energy` (§3), which cite the CCvS γ(−2)=225ζ(5)/4 ≠ 0 contradiction. | **adopt-clean** (null-fills harmless); no status change. Note the §2 FIT-zeta anchor correctly references this kill. | Medium |

**Watch-but-clean (not blocking, noted for completeness):** the a₀/MOND/DM family in §3 — `OBS-a0-threshold`, `PRED-no-dm-particle`, `PRED-a0-*`, `EXT-dm-*`, `OBS-rotation-anomaly`, `MEAS-hubble-tension` — all receive only null-fills. Batch-A downgraded the *a₀-saturating-F_max* anchor to marginal and re-scoped a₀ as late-time asymptote, but those rulings landed on the **v5.13 Batch-A anchors**, not these §3 rows, and the §3 updates here are vacuous null-fills. **adopt-clean**; no collision because no value is being changed. (Flagged so Oppenheimer can confirm the a₀ family stays consistent across batches.)

---

## §2/§3 ↔ Batch-A COLLISION CHECK (where both rulings would touch the same content)

| Locus | Batch-A ruling (v5.13) | Batch-C content (v5_24) | Collision? | Resolution |
|---|---|---|---|---|
| **entropy-cone chain** | Batch-A #15 `PRED-hypergraph-cmb-camb-rerun` → **include-as-killed** (rests on PROOF-…-cone-mapping, EC-DEAD) | §3 `PROOF-division-algebra-entropy-cone-mapping` + `INSIGHT-entropy-cone-division-algebra-inversion` null-fills; §2 has NO new cone-mapping anchor | **No live collision** — same EC-DEAD ruling applies identically. v5_24 brings only vacuous null-fills on the already-killed anchors. | Consistent: adopt null-fills, preserve canonical kill metadata. |
| **F_max / ln-7 ladder** | Batch-A: F_max anchor → marginal (7 vs 13.4 tension); ln-7 anchors (#19,#23) clean — k=15→8 correction hit 𝕊→𝕆 ONLY | §2 FLAG-seam-dynamics-open uses 1/24 (|Stab|); §3 ln-7-adjacent PRED-* null-fills only | **No collision** — seam |Stab|=24 is the 𝕊-level stabilizer, untouched by the 𝕆→ℍ k=7 corrections. | Consistent. |
| **TOV cluster** | Batch-A: √(7/3) global M_max **falsified**; bump-peak reading survives; PROOF-iron-to-ns-bridge `physical_mapping_status: conjectural` | §3 `Q27-TOV-limit-from-Fano` (predicted_value null-fill), `PROOF-M-proportional-to-a`, `PROOF-interpolation-function-derived` | **Potential collision** — `Q27-TOV-limit-from-Fano` is TOV-adjacent. v5_24 update is a null-fill only, but if the anchor's *description* carries the global √(7/3) M_max reading, the Batch-A `falsified-as-global` rider must apply. | **adopt null-fill; apply Batch-A rider** — if Q27 asserts global TOV M_max from Fano, attach `physical_mapping_status: falsified-as-global` consistent with Batch-A #3/#17. Oppenheimer should confirm. Conf: medium. |
| **CAMB / hypergraph-CMB** | Batch-A #15 killed (dead premise) | §3 `COMP-cmb-power-spectrum-accretion`, `COMP-branch-A-cmb-boundary-analysis` null-fills | **No collision** — these are COMP-* analysis anchors, not the killed PRED chain; null-fills vacuous. | adopt-clean. |
| **nuclear-identity PROOFs** | Batch-A #18/#20/#22/#24: Lean identities real, mapping conjectural (`physical_mapping_*` rider) | §2 has the *condensed/GR* PROOF-* (different cluster), §3 `PROOF-M-proportional-to-a` etc. null-fills | **No direct collision** — different anchors. But the **same truth-in-labelling principle** Batch-A applied to nuclear PROOFs is what drives the §2 PROOF→DERIV/INSIGHT relabels. | Consistent — §2 relabels are the Batch-A discipline applied to anchor IDs (Oppenheimer's own stated extension, seq 94: "truth-in-labelling extends to anchor IDs"). |
| **PROOF-* with phantom proof_file** | Batch-A R2/stale-pointer: phantom `lean4/QBP/` and `GaugeBosons.lean` → name-resolve-or-flag | §2 all 3 PROOF-* cite `proofs/QBP/Foundations/QBPHorizonFoundations.lean` (absent) + one cites `lean4/QBP/SpectralAction/ProfileFit.lean` (the SAME phantom prefix) | **Direct continuity, not collision** — apply the identical stale-pointer rule on apply. | Consistent: `lean_migration_status: stale-pointer` + `review_flag` for all 3. |

**Bottom line on collisions:** No *contradictory* collisions found. Every locus where Batch-A and Batch-C touch the same theory resolves **consistently** — because v5_24's §3 updates are almost entirely vacuous null-fills, and the EC-DEAD / ladder / TOV rulings apply with the same sign in both batches. The two places needing Oppenheimer's explicit confirmation: (1) `Q27-TOV-limit-from-Fano` may need the Batch-A `falsified-as-global` rider, and (2) the §2 PROOF→DERIV/INSIGHT relabels should be ratified as the anchor-ID extension of Batch-A's truth-in-labelling.

---

## Quick-reference: what Oppenheimer must actually RULE on (preparation hands these up)

1. **§2 PROOF-* relabels (×3)** — confirm DERIV-/INSIGHT- reclassification (termination fails; Lean phantom). [recommended: relabel all 3]
2. **§2 substrate corpus (×16)** — confirm include-as-NASCENT + substrate tag, ledger-only (no Lean). [recommended: include-as-NASCENT]
3. **§2 REF-schema posture** — flagged for @cth-implementor, not an Oppenheimer theory call.
4. **§2 INSIGHT echo/resonance/threshold (×3)** — NASCENT-by-chain vs coherent-with-NASCENT-bridge split. [recommended: NASCENT, with optional status-split]
5. **§3 EC-DEAD anchors (×3)** — adopt null-fills, preserve canonical kill metadata, do NOT revive coherent/untested.
6. **§3 `Q27-TOV-limit-from-Fano`** — confirm whether Batch-A `falsified-as-global` rider attaches.
7. **§3 bulk (×~47)** — adopt-clean (vacuous null-fills); schema tier changes → cth-implementor R1.
8. **Zero drops, zero kills in §2** — consistent with Batch-A "nothing dropped; falsified preserved with kill metadata."

*Prepared as decision-support only. All rulings are @qbp-oppenheimer's.*
