# CTH Inventory — Canonical Ledger + Tracked Baselines

**Status:** Active source-of-truth for the QBP programme's Confluent Trust Hypergraph (CTH) inventory anchors at the Crawl/Toddle phase.

## ⭐ THE CANONICAL FILE

> **`confluent-trust-inventory-v5_3.v0.3.json`** — 150 anchors, schema v0.3.
>
> This is the **single theory-state authority** for the QBP programme. All live updates land here: theory PRs append anchors alongside prose (the "(a)-cadence"), kill dispositions carry `killed_by` provenance (e.g. #484, commit `a7e85db`), and the foundations rebuild's `DEFN-*`/`PROOF-*` anchors accrue here.

**Authority chain:**
- Beekeeper decision 2026-05-14 (`pr407-conflict-resolution` seq=40, option b of a+b+c) — baselines land in git as tracked source-of-truth (PR #422)
- v0.3 schema migration 2026-05-29 (`cth migrate v0.3-impl-2`; see `migrations/`) — produced the canonical file from the v5_3 baseline
- Federation canonicity settled 2026-06-01 (`cth-qbp-live-testing` seq=19–23, read-back-verified by @cth-implementor): **QBP `archive/cth-inventory/` = theory-state authority; the `confluent-trust` repo = schema authority only**

---

## Files in this directory

| File | Role | Anchors | Schema | Status |
|---|---|---|---|---|
| `confluent-trust-inventory-v5_3.v0.3.json` | **CANONICAL — live ledger** | 150 | v0.3 | Receives all updates. 141 migrated from v5_3 + 9 foundations appends (6 `DEFN-*`, 2 `PROOF-*` breakdown, 1 `WISDOM-*`) |
| `confluent-trust-inventory-v5_3.json` | Historical baseline | 141 | 5.3 | **Frozen.** QBP-web Session-13 closeout 2026-05-11. Migration input — do not update |
| `confluent-trust-inventory-v5.13.json` | Historical baseline | 150 | 5.13 | **Frozen.** qbp-architecture federation-tenancy stream 2026-04-30. 24 stream-only anchors await adjudication (#509) |
| `confluent-trust-inventory-v5_24.json` | Historical baseline — **pending intake** | 169 | v0.2 | **Frozen.** QBP-web continued lineage (received 2026-05-31). 28 anchors not in canonical (condensed-math programme, `REF-*` citations, Dirac/Vaidya proofs); missing the 9 foundations appends. Adjudication scope of #509 |
| `migrations/` | Migration provenance | — | — | `decisions-v5_3-to-v0_3.json` (33 applied) + `migration-report-v5_3-to-v0_3.md` (74 provenance decisions still pending — #509) |

**Rule: one live file.** Only the canonical file is ever updated. Baselines are frozen migration/reconciliation inputs. If you have received a newer inventory export from any stream, add it as a new frozen baseline and file a reconciliation issue — never update a baseline in place, never start a second live file.

---

## How to use

### Query the canonical ledger

```python
import json
inv = json.load(open("archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"))
anchors_by_id = {a["id"]: a for a in inv["anchors"]}
```

### Append anchors (theory PRs — the "(a)-cadence")

The theory PR commits the anchor JSON in the same PR as the prose. Reviewers check both prose accuracy AND inventory consistency. Kill dispositions set `killed_by` (+ `killed_note`, `review_flag` per confluent-trust #93) rather than deleting — see #484 for the working precedent.

### Proven-theorem anchors (foundations stream)

Per the two-stream model (`pr407-conflict-resolution` seq=82–92): proven Lean theorems flow to CTH per the protocol in confluent-trust#96 (per-batch sign-off at #474 matrix-row milestones; Lean-identity join key = module path + theorem name + `#print axioms` attestation).

### For BMA re-audit (Capability #6) and ρ_net trajectory (federation tenancy §5.4)

Read the canonical file only. Baselines exist for historical-trajectory computation, not current state.

---

## Open reconciliation work — QBP #509

| Gap | Scope |
|---|---|
| v5.13 fold-in | 24 stream-only anchors → adjudication per `paper/CTH-Inventory-Reconciliation-Cycle2-Proposals.md` (PR #423; named adjudicator per anchor) |
| v5_24 intake | 28 stream-only anchors + shared-anchor diffs → same routing rubric (third stream, discovered 2026-06-04) |
| Provenance backfill | 74 anchors awaiting `theory` vs `theory-external` classification → `cth migrate --decisions` |

Routing authority: Beekeeper D4 (2026-05-13) — theory-axis → @qbp-oppenheimer; schema-axis → @cth-implementor; rubric at `docs/workflows/pr7_conflict_routing_rubric.md`.

---

## Provenance

| Step | Date | Actor |
|---|---|---|
| Session-13 closeout produces v5_3 (141 anchors) | 2026-05-11 | QBP-web Red Team (Opus 4.7) |
| Federation-tenancy v5.13 (150 anchors) staged | 2026-04-30 | qbp-architecture |
| Tracked baselines land in git (option b) | 2026-05-14 | qbp-implementor (PR #422) |
| v0.3 schema migration → canonical file | 2026-05-29 | cth migrate v0.3-impl-2 (#458/#459 infra) |
| QBP-web v5_24 export received | 2026-05-31 | beekeeper (archive transfer) |
| Entropy-cone DEAD dispositions (kill-provenance precedent) | 2026-06-01 | qbp-oppenheimer (#484, `a7e85db`) |
| Federation canonicity read-back-verified | 2026-06-01 | cth-implementor (`cth-qbp-live-testing` seq=19–23) |
| Foundations zero-sorry rebuild begins appending | 2026-06-01+ | qbp-oppenheimer (480-B posture) |
| README canonical pointer fixed + v5_24 baseline tracked | 2026-06-04 | qbp-implementor (#509) |

---

*See also:*
- `docs/workflows/pr7_conflict_routing_rubric.md` — reconciliation routing rules
- `paper/CTH-Inventory-Reconciliation-Cycle2-Proposals.md` — per-anchor merge proposals (PR #423)
- `migrations/migration-report-v5_3-to-v0_3.md` — v0.3 migration provenance + pending decisions
- confluent-trust#96 — proven-theorem → CTH anchoring protocol (§I4 surface)
- inter#57 — foundation↔physics dependency map (Lean-identity join key shared with anchor verification field)
- `~/Documents/CTH/cth/` — canonical CTH Go library / schema authority (sibling repo)
