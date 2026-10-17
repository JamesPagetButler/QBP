# CTH Anchor ID Prefix Policy

**Status:** DRAFT — authored for QBP #462 (Sprint-4 housekeeping, tracking #714); ratification by qbp-architecture pending (#462 AC7)
**Resolves:** #462 (which cites "discovery response §7.F6 action item #5" — source document not in this repo; the on-disk source is the 22-row table in `docs/cth/qbp-local-extensions.md` §Anchor ID prefixes)
**Author:** qbp-implementor (housekeeping seat)
**Ledger surveyed:** `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` @ ledger 6.18.0 (schema 0.3.x)
**Upstream:** the vendored schema (`docs/cth/inventory.schema.v0.3.json`, `$id` …v0.3.5) has `Anchor.id` at `minLength: 1`, "workspace-convention prefix … not pattern-enforced"; only `derived_principles[].id` is pattern-pinned (`^DERIV-`). The upstream proposal to register the five new prefixes in the confluent-trust schema is a separate schema-axis issue, **QBP #722** (co-sign @cth-implementor) — **not** this document. #494 (PROOF-prefix vs `provenance_kind: theory` naming) is a different, open question — see R2.

---

## 1. What a prefix is for

An anchor id is `<PREFIX>-<slug>`. The prefix is the **reader's first classifier**: it says what *kind of claim* the record is before `provenance_kind`, `status` and `tier` are read. It is convention, not schema — so the convention has to be written down, or the ledger drifts (it already has: §5).

Rules that hold for every prefix:

| Rule | Statement |
|---|---|
| **R1 — one prefix, one meaning** | A prefix names a claim kind, never a topic, a sprint, or an author. `Q27-`/`Q28-` (topic-numbered) are grandfathered legacy, not a pattern to extend. |
| **R2 — prefix ≠ provenance_kind** (*provisional*) | The prefix classifies the *claim*; `provenance_kind` classifies the *evidence*. They correlate (§2 "pairs with") but need not coincide: a `PROOF-` anchor whose evidence is a literature citation is `provenance_kind: theory-external` (`PROOF-hurwitz`), and a `PRED-` anchor can be `proof`, `theory`, `derivation` or `internal-compute`. **This is the "loose" reading that #494 AC1 leaves open** (strict = a `PROOF-` id requires `provenance_kind ∈ {proof, derivation}`; 16 `PROOF-`/`theory` anchors would then need re-keying). R2 *proposes* loose; it is settled only when #494 AC1 is ruled, and ratification of this document (§6) is that ruling's natural vehicle. |
| **R3 — status lives in `status`, not the id** | Never encode lifecycle in the prefix. `KILLED-` is the one legacy exception and is **closed to new mints** — a killed anchor keeps its prefix and sets `status: killed`/`refuted`/`falsified`. |
| **R4 — slug conventions** | Lower-case, hyphen-separated; algebra glyphs in Unicode (`DEFN-op-norm-𝕆`, not `-O`) per `docs/conventions/algebra-naming.md`. Short, stable, never renamed — ids are cited from chains, `discharge` fields, `evidence_ref`s and review threads. |
| **R5 — ids are minted by encoders, not by hand** | Every anchor enters the ledger through a confined writer (`scripts/encode_*.py`, `scripts/encode_pa_from_evidence.py`) in a PR with Tier-2+ review; the root lists (§3) additionally need the architecture ratification that gates them. No prefix grants a seat write authority it does not otherwise hold. |
| **R6 — no new prefix without a row here** | Mirror of the extensions doc's forward rule for fields: a prefix not in §2–§4 is a review BLOCKING finding until this document gains the row (and, for a schema-enforced prefix, an upstream issue). |

---

## 2. The established family (anchors, `anchors[]` list)

Counts and `provenance_kind` pairings are from the ledger census at 6.18.0 (`anchors[]` only unless stated). "Pairs with" = the kinds observed; the **bold** kind is the expected default.

| Prefix | Meaning | Pairs with (`provenance_kind`) | Minted by | Count | Ledger examples |
|---|---|---|---|---|---|
| `PROOF-` | A theorem with a formal-proof reference (`proof_file` / `lean_theorem`), or a named external theorem the programme stands on | **proof** (95); derivation (11); theory (16 — the #494 reconcile set); theory-external (6); internal-compute (1) | encoder on a Lean/Agda/Coq landing PR; PA grade computed, never declared (`pa_local`/`pa_effective`) | 129 | `PROOF-42zd` (proof), `PROOF-hurwitz` (theory-external), `PROOF-hessian` (internal-compute) |
| `MEAS-` | A measured quantity the programme compares against | **theory** (12 — the programme's own number), experiment (6), theory-external (2) | encoder; experiment source cited | 20 | `MEAS-alpha`, `MEAS-sin2tw`, `MEAS-alphas` |
| `PRED-` | A prediction awaiting (or scored against) observation | **theory** (30); internal-compute (5); theory-external (3); derivation (2); proof (1) | encoder; scored via `compute.ScorePrediction` when the observation lands | 41 | `PRED-gw-em`, `PRED-3episode`, `PRED-willow-j` |
| `OBS-` | An observation: a numerical coincidence or empirical fact noted, not yet a prediction | **experiment** (13); theory (6); theory-external (4) | encoder | 23 | `OBS-f0-2alpha`, `OBS-cbt-koide`, `OBS-cmb-314` |
| `REF-` | An external reference the programme cites (paper, dataset) | **theory-external** (31); experiment (10); internal-compute (1) | encoder | 42 | `REF-wagner-profiles`, `REF-clifton-hyatt-intrinsic` |
| `EXT-` | An external *anchor*: a number owned by another programme/experiment that QBP is constrained by | experiment (2); internal-compute (2) | encoder | 4 | `EXT-omega-dm`, `EXT-dm-null-detection` |
| `COMP-` | A computation performed inside the programme (pipeline, simulation) | **internal-compute** (3) | encoder; reproduce-path cited | 3 | `COMP-cmb-power-spectrum-accretion`, `COMP-sm-non-unification-at-1loop` |
| `FLAG-` | A programme flag: an open problem or unresolved quantity tracked as a node | **theory** (14); internal-compute (1); experiment (1) | encoder; may be a `kill_condition.discharge` tracker (LIVE `FLAG-`/`CONJ-`) | 16 | `FLAG-J`, `FLAG-Tc`, `FLAG-xi` |
| `INSIGHT-` | A synthesised insight: an interpretive claim that connects nodes but is not itself a theorem or prediction | **theory** (15); internal-compute (7); theory-external (1); derivation (1) | encoder | 24 | `INSIGHT-info-paradox-resolution`, `INSIGHT-urca-threshold-dim-O` |
| `CONV-` | A convergence: an independent external framework reaching the same structure | **theory-external** (2); philosophy (1) | encoder | 3 | `CONV-spectral-entropy-zeta`, `CONV-flow-fragmentalism` |
| `CONSTRAINT-` | A constraint the theory must satisfy (bound, exclusion) | theory (1); experiment (1) | encoder | 2 | `CONSTRAINT-ynu`, `CONSTRAINT-gdot` |
| `WISDOM-` | A Wisdom-Ledger claim (scope-deliberation §6): a programme-level lesson or principle, not a physical claim | **theory** (3) | encoder; beekeeper/architecture-sourced text | 3 | `WISDOM-schema-vs-instance`, `WISDOM-003-there-is-only-f-u` |
| `INST-` | An instance: a single empirical fit / irreducible input. Lives mostly in `inputs[]` (status `irreducible`/`measurable`); one legacy `anchors[]` record | internal-compute (1 in `anchors`); `inputs[]` carry no `provenance_kind` | encoder | 1 + 5 (`inputs`) | `INST-ckm` (anchor), `INST-f0`, `INST-theta` (inputs) |
| `PARTIAL-` | A partially-resolved claim: a proven structural half with an unproven dynamical half, stated as such | theory (1) | encoder | 1 | `PARTIAL-qgp` |
| `Q27-`, `Q28-` | Open-question anchors numbered by the legacy question register. **Legacy; closed to new mints** — new open questions are `CONJ-` or `FLAG-` (R1) | theory (2) | — | 2 | `Q27-TOV-limit-from-Fano`, `Q28-alpha-GUT-from-stabiliser` |
| `KILLED-` | Killed hypothesis recorded as a node. **Legacy; closed to new mints** (R3) | theory (1); internal-compute (1) | — | 2 | `KILLED-f4-info-theoretic-justification`, `KILLED-locale-forcing-route` |
| `META-` (anchor form) | A schema-level / programme-level note encoded as an anchor (distinct from the `META-n` meta-principle roots, §3). **Closed to new mints:** #657 (#654 D1) rules these two "smuggled roots" and renames them out of the root prefix space | theory (2) | — (rename pending, #657) | 2 | `META-physical-mapping-status-field`, `META-regime-of-validity-field` |
| `DERIV-` (anchor form) | A kernel-verified derived result whose full claim is a derivation/interpretation, not a foundational proof (schema `ProvenanceKind` note, 0.3.3). Also the **schema-enforced** id of every `derived_principles[]` record (`^DERIV-`), §3 | **derivation** (14) | encoder on a Lean landing PR; `derived_principles[]` rows need architecture ratification | 14 + 12 (`derived_principles`) + 1 (`retired_principles`) | `DERIV-observation`, `DERIV-arrow`, `DERIV-3plus1` (principles) |

---

## 3. Root-list prefixes (not in `anchors[]`)

Root records are the ledger's Layer-0 objects. Their prefixes are fixed by the list they live in; minting one is a **constitutional-layer** change — proposal doc + conversation per `~/Documents/inter/conversation-modus-operandi.md`, qbp-architecture ratification, cth-implementor co-sign on the introducing PR (precedent: `decision_state`/`kill_condition`, `docs/cth/qbp-local-extensions.md` §Root decision fields).

| Prefix | List | Meaning | Count | Examples |
|---|---|---|---|---|
| `META-n` | `meta_axiom` (singular), `meta_principles[]` | The meta-axiom and meta-principles the axioms sit under | 1 + 1 | `META-1` (meta_axiom), `META-2` "Level saturation" |
| `AXIOM-n` | `axioms[]`, `retired_axioms[]` | A foundational axiom (`derivable: false`), numbered. Carries `decision_state` + `kill_condition` when open. Formal documentation of the prefix: §4 | 1 + 1 retired | `AXIOM-1` "Information is preserved"; `AXIOM-2` (retired 2026-09-09, demotion record in `docs/foundations/axiom2-demotion-*.md`) |
| `POST-` | `axioms[]` | A postulate: an axiom-list record that is a hosting/existence posit rather than a numbered axiom (introduced on the AXIOM-2 demotion) | 4 | `POST-boundary-encoding`, `POST-hosting`, `POST-observer-associativity`, `POST-observation` |
| `DERIV-` | `derived_principles[]`, `retired_principles[]` | Derived principle (schema-enforced `^DERIV-`) | 12 + 1 | `DERIV-observation`, `DERIV-arrow` |
| `INTERP-` | `interpretations[]` | An interpretation (`provenance_kind: philosophy`) — a root with `decision_state` + `kill_condition`, no new kind (cth live-test 1297) | 1 | `INTERP-holographic-boundary` |
| `CONFL-` | `confluence_points[]` | A confluence point: where independent chains meet on one number | 8 | `CONFL-rebco-stability`, `CONFL-coupling-ratios`, `CONFL-f0-three-couplings` |
| `CHAIN-` | `chains[]` | A derivation chain, §4 | 22 | `CHAIN-axioms-to-gauge`, `CHAIN-alpha-to-udd` |

---

## 4. The five additions (DEFN- / AXIOM- / CONJ- / CHAIN- / FORK-)

These were listed as "pending" in the extensions doc's table. This section is their formal documentation (#462 AC3/AC4). Three are already live in the ledger; `FORK-` is reserved.

### 4.1 `DEFN-` — Definition (foundations rebuild §3)

| | |
|---|---|
| **Meaning** | A *definition* in the operations-complete property matrix (`docs/foundations/scope-deliberation-2026-05-31.md` §3 — the "foundations rebuild §3.1 + §4" #462 cites; that doc has no `DEFN-` strings itself, the prefix is this document's formalisation of its rows): a structural object or operation on the tower (ℝ, ℂ, ℍ, 𝕆, 𝕊 — addition, multiplication, conjugation, norm, Cayley-Dickson doubling, bilinear form, exp/log, cross product). A `DEFN-` anchor asserts *what the object is* as formalised in `proofs/QBP/Foundations/`, not that any law holds of it — laws are `PROOF-`. |
| **Pairs with** | `provenance_kind: theory` (observed 7/7). Status `untested` until the Lean definition it names compiles under the foundations gate, then `coherent`. Never `proof` — a definition is not a theorem; the theorem about it is the `PROOF-` anchor that cites it. |
| **Minted by** | the foundations encoder on the PR that lands the Lean `def`; `proof_file` points at the defining module. |
| **Ledger** | 7 — `DEFN-cayley-dickson-doubling`, `DEFN-real-structural-trivial`, `DEFN-complex-structural-i`, … |
| **Slug** | `DEFN-<object>[-<algebra glyph>]` — `DEFN-ℍ-hamilton-product`, `DEFN-op-norm-𝕆` (`docs/conventions/algebra-naming.md`). |

### 4.2 `AXIOM-` — Axiom (foundations rebuild §4; root list)

| | |
|---|---|
| **Meaning** | A foundational axiom of the programme — a Layer-0 record in `axioms[]` with `derivable: false`. Numbered (`AXIOM-1`, `AXIOM-2`), never slugged: an axiom's identity is positional in the foundations, and retiring one keeps its number in `retired_axioms[]` (AXIOM-2) so citations stay resolvable. |
| **Pairs with** | no `provenance_kind` (root records do not carry one). Carries `decision_state` ∈ {open, settled} + `kill_condition[]` (KillConditionEntry) per `qbp-local-extensions.md` §Root decision fields; `open` REQUIRES a non-empty kill list. |
| **Minted by** | constitutional path (§3 preamble). An axiom is never minted by an encoder script alone. |
| **Distinct from** | `POST-` (a posit in the same list that is not a numbered axiom) and `META-n` (above the axioms). |
| **Ledger** | `AXIOM-1` "Information is preserved" (open, two-entry kill list, #647); `AXIOM-2` retired. |

### 4.3 `CONJ-` — Conjecture

| | |
|---|---|
| **Meaning** | An open conjecture: a stated, falsifiable claim the programme has *not* proven and does not assume. The foundations rebuild's FRONTIER signposts (scope-deliberation §4 🟡 — triality, Hopf fibrations, Dixon algebra, h₃(𝕆)) are the intended cohort; a `CONJ-` is the live tracker a `kill_condition.discharge` may point at while the route is OPEN. |
| **Pairs with** | `provenance_kind: hypothesis` is the schema's designed pairing (extensions doc: "foundations rebuild + `provenance_kind: hypothesis`"). **Observed:** both ledger `CONJ-` anchors are `theory` (`CONJ-condensed-math-for-transition-state` marginal, `CONJ-vconstants-keystone` untested). Policy going forward: new `CONJ-` mints use `hypothesis`; the two existing records are re-keyed on their next touch (a data-quality fix, logged in the extensions doc change history, not a re-mint). |
| **Status** | `untested` while open; on resolution the record is **not** renamed — it moves to `coherent` (proven: a `PROOF-` anchor is minted and the `CONJ-` cites it) or `refuted`/`falsified` (R3). |
| **Minted by** | encoder; requires a stated falsifier in the record (same discipline as a kill condition — nothing parks open without a kill). |

### 4.4 `CHAIN-` — Derivation chain (`chains[]`)

| | |
|---|---|
| **Meaning** | A derivation chain: an ordered path `source_ids → … → target_id` through anchors, with `steps` and a chain `status` ∈ the coherence enum. Chains are the objects `confluence_points` and the criticality metric (`CTH edge types`) are computed over. |
| **Pairs with** | no `provenance_kind`; `status` observed: coherent 14, untested 4, incoherent 2, marginal 2. |
| **Minted by** | encoder on the PR that lands the last link; every `source_ids`/`target_id` must resolve to an existing anchor (a dangling link is a lint failure — `scripts/check_anchor_manifest.py`). |
| **Ledger** | 22 — `CHAIN-axioms-to-gauge`, `CHAIN-axioms-to-alpha`, `CHAIN-alpha-to-udd`. |
| **Note** | The extensions table said "used in `chains`, not yet in `anchors`" — correct, and by design: a `CHAIN-` id never appears in `anchors[]`. |

### 4.5 `FORK-` — Fork branch (reserved)

| | |
|---|---|
| **Meaning** | One branch of a programme fork: a point where two incompatible continuations are both kept live until a discriminating result lands (the routing rubric's "forks: branch labels differ (schema) AND branch membership differs (theory)" — `docs/workflows/pr7_conflict_routing_rubric.md`). |
| **Schema** | **Supported upstream, unused in QBP.** The confluent-trust schema v0.3.5 (vendored at `docs/cth/inventory.schema.v0.3.json` l.45, `$defs/ForkPoint` l.445; upstream `confluent-trust/schema/inventory.schema.json` @ 13de2f7) has a top-level **`fork_points[]`** of `ForkPoint {id, branch_node_id, question, shared_prefix[], branches[] (≥2 `Branch`), branch_observations[]}` — Theory v0.2 §2.9 fork extension. The pre-v0.3 raw QBP inventory carried a `forks` list (rubric §verification); the QBP ledger at 6.18.0 carries **no `fork_points` key** — a QBP population gap, not a schema gap. |
| **Status in the ledger** | **Reserved, zero records.** The two live forks of record (Forks 1 & 2 under #559, `docs/foundations/substrate-foundational-concerns-resolution-2026-06-13.md`) are tracked in issues, not the ledger. |
| **Policy** | A `FORK-` id is the `id` of a `fork_points[]` record and is **not mintable in `anchors[]`**. Minting one = populating `fork_points[]` through an encoder with `branch_node_id` resolving to an existing anchor and ≥ 2 branches — **no upstream schema issue is needed** (the list and record type already exist); the id-prefix registration rides with the other four on #722. Until the first record lands, a fork is recorded as two `CONJ-` anchors sharing a `kill_condition` that discriminates them, and the policy row here is un-reserved by the PR that encodes it. |

---

## 5. Census vs. table — what this document corrects

The extensions table (22 rows) and the ledger disagree in both directions. This document is the reconciled list; the extensions table is reduced to a pointer.

| Finding | Disposition |
|---|---|
| In ledger, not in the 22-row table: `CONFL-` (8), `POST-` (4), `INTERP-` (1), `META-` (1 root + 2 anchors), `FIT-` (1), `OPEN-` (1), `QBP-POS-` (2) | `CONFL-`/`POST-`/`INTERP-`/`META-` documented in §3 (root-list prefixes were out of the table's scope). **`FIT-`** (`FIT-zeta-modulated-profile`, a constraint-solve fit, `proof`/marginal), **`OPEN-`** (`OPEN-Q-parent-bh-retardation-derivation`) and **`QBP-POS-`** (`QBP-POS-emergent-time`, `QBP-POS-organization-not-generator` — programme position statements) are **undocumented one-offs**: closed to new mints; recommended re-key on next touch to `COMP-`/`PARTIAL-`, `CONJ-`, and `WISDOM-` respectively (a Tier-2 data-quality PR — not done here). |
| In table, zero in ledger: `FORK-` | Reserved (§4.5); schema-supported upstream via `fork_points[]`, so no schema work gates it. |
| Table says `CONV-` = "Convention"; the three ledger records are convergences (`CONV-spectral-entropy-zeta` "External mathematical result…", `CONV-cd-tower-in-zeta-moments` "surviving piece of the candidate CCvS convergence", `CONV-flow-fragmentalism` "structural analogy…") | Meaning disagreement, not an omission: `CONV-` = **Convergence** (§2); the table row is corrected in the same PR. |
| Table says 22 prefixes | The table's 22 rows = 21 distinct prefixes once `Q27-`/`Q28-` share a row (+1 for the pair = 22 names). This document covers them as: 18 in §2 (anchor family, incl. `META-`/`DERIV-` anchor forms) + 7 in §3 (root lists) − 2 overlapping (`META-`, `DERIV-`) + 2 in §4 only (`DEFN-`, `CONJ-`; `AXIOM-`/`CHAIN-`/`FORK-` are §3 rows) = **25 documented**, i.e. the table's 22 plus `CONFL-`, `POST-`, `INTERP-` from the census (the `FIT-`/`OPEN-`/`QBP-POS-` one-offs above are listed, not adopted). |
| `CONJ-` designed pairing `hypothesis`, observed `theory` | §4.3 — re-key on next touch. |

---

## 6. Ratification and upstream

- **#462 AC7 (qbp-architecture ratification):** pending. This document carries `Status: DRAFT` until the ratification seq is recorded here, mirroring `sedenion-indexing.md`.
- **#462 AC6 (confluent-trust upstream proposal, schema-axis routing per `pr7_conflict_routing_rubric.md` v0.2):** carried by **QBP #722** (filed 2026-10-17; co-sign @cth-implementor), not by this document. When it lands, the upstream schema registers the prefix semantics (description-level, not pattern enforcement) and this document's §2–§4 become the QBP-side mirror of the canonical list, synced per `docs/cth/schema-change-propagation-checklist.md`.
- **#494 (PROOF- naming vs `provenance_kind: theory`):** open; R2 proposes the loose reading and is marked provisional until #494 AC1 is ruled.

## Change history

| Date | Author | Change |
|---|---|---|
| 2026-10-17 | qbp-implementor (housekeeping seat) | v0.1 — authored for #462 from the ledger census at 6.18.0; §4 formalises DEFN/AXIOM/CONJ/CHAIN, reserves FORK; §5 reconciles the extensions table against the ledger |
| 2026-10-17 | qbp-implementor (housekeeping seat) | v0.2 — PR #719 Red Team (Grothendieck G1–G7): §4.5 FORK- rewritten against upstream `fork_points[]`/`ForkPoint` (schema-supported, unused in QBP; no upstream issue needed); AC6 re-routed from #494 to #722; R2 marked provisional pending #494 AC1; census PROOF-/proof 95, REF-/theory-external 31; §5 arithmetic redone, `CONV-` Convergence row added; META- anchor form closed per #657; unverifiable source pointers marked |
