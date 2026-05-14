# CTH Inventory — Tracked Baselines

**Status:** Active source-of-truth for the QBP programme's Confluent Trust Hypergraph (CTH) inventory anchors at the Crawl/Toddle phase.

**Authority:** Beekeeper decision 2026-05-14 (`pr407-conflict-resolution` seq=40 → option b accepted as part of a+b+c bundle). Lands the v5_3 and v5.13 inventory snapshots into git as the tracked baseline for BMA re-audit reads + ρ_net trajectory computation + bookkeeper-role first operations.

---

## Files in this directory

| File | Source | Anchors | Status |
|---|---|---|---|
| `confluent-trust-inventory-v5_3.json` | QBP-web Session-13 closeout 2026-05-11 | 141 | **Canonical baseline for Session-13 theory state.** Includes KILLED-f4-info-theoretic-justification + CONV-cd-tower-in-zeta-moments + CONV-spectral-entropy-zeta. |
| `confluent-trust-inventory-v5.13.json` | qbp-architecture federation-tenancy stream 2026-04-30 | 150 | **Reference snapshot for federation-tenancy stream.** Contains 24 anchors unique to this stream (mostly META + INSIGHT class). |

Both files are byte-identical copies of the corresponding files in `archive/` (kept there as the historical archive transfer location). The duplication is intentional: `archive/cth-inventory/` is the **git-tracked source-of-truth**; `archive/confluent-trust-inventory-v*.json` files are the **historical archive transfer** (will land in git via #81 Theory Refinement integration in a future PR).

---

## How to use

### For BMA re-audit (Capability #6)

Query the tracked inventory programmatically:
```python
import json
inv = json.load(open("archive/cth-inventory/confluent-trust-inventory-v5_3.json"))
anchors_by_id = {a["id"]: a for a in inv["anchors"]}
# anchor "KILLED-f4-info-theoretic-justification" is queryable here
```

### For ρ_net trajectory computation (federation tenancy §5.4)

Use the CTH `compute.NetCompressionDetail` on either tracked file. Output is the ρ_net value at that inventory snapshot's timestamp.

### For the bookkeeper-role first operations (Capability #7)

- `bma cth status <anchor-id>` (Toddle Phase 0): reads any field from the tracked inventory.
- `bma cth propose-update <anchor-id> --reason <text>` (Toddle Phase 1): generates a PR-shaped diff against the tracked baseline; beekeeper approves; commit happens via PR.

---

## What's NOT in this directory (deferred)

1. **CONJ-fu-from-hawking-time-reverse** — the 4th Session-13 closeout finding. Per `archive/INDEX.md` it exists only as text in `SESSION-13-WORKING-NOTES.md`; not yet formalised as a CTH anchor. Will land via Oppenheimer's PR4 (Spectral Action + CCvS + W-003 revision) per option (a) of the 2026-05-14 a+b+c decision.

2. **WISDOM-003-revised** — W-003 revision per PR #407 prose ("the spectral triple is the invariant; test functions select observables"). Per option (a), Oppenheimer's PR4 / PR6 commits this anchor entry alongside the wisdom paper integration.

3. **Live updates** — neither file is updated by automated processes. Future updates land via:
   - Option (a): theory PRs bundle inventory diffs (Oppenheimer-side)
   - Option (b) follow-on: PR7 cycle 2/3 produces unified vNext inventory from the two streams
   - Option (c): cth-implementor sync-script (CTH-side; multi-cycle)

4. **CTH library v0.2 schema lock** — the JSON files here are the schema-by-example for now. cth-implementor's `~/Documents/CTH/cth/` is the canonical Go implementation; schema formalization is CTH-side.

5. **All anchor-level diff reconciliation** — PR7 cycle 1 (`paper/CTH-Inventory-Reconciliation-Delta-v0.1.md`) classified the 126 in-both + 39 stream-only anchors per the routing rubric. PR7 cycle 2 (forthcoming) produces per-anchor merge proposals using these tracked baselines.

---

## Provenance

| Step | Date | Actor |
|---|---|---|
| Session-13 closeout produces v5_3 (141 anchors) | 2026-05-11 | QBP-web Red Team (Opus 4.7) |
| Federation-tenancy v5.13 (150 anchors) staged | 2026-04-30 | qbp-architecture |
| Both files arrive locally via archive transfer | 2026-05-08 | (untracked in `archive/` until this commit) |
| Discovery of CTH-inventory-not-tracked gap | 2026-05-14 | Beekeeper (qbp-implementor verification on `pr407-conflict-resolution` seq=40) |
| Decision: proceed with options a + b + c | 2026-05-14 | Beekeeper |
| This commit (option b): tracked baseline lands in git | 2026-05-14 | qbp-implementor (Integration role) |

---

*See also:*
- `docs/workflows/pr7_conflict_routing_rubric.md` — routing rules for v5.13 ↔ v5_3 reconciliation work
- `paper/CTH-Inventory-Reconciliation-Delta-v0.1.md` — PR7 cycle 1 anchor-classified delta report
- `docs/qbp-federation-tenancy.md` §5.4 — ρ_net trajectory tracking consumer
- `~/Documents/CTH/cth/` — canonical CTH Go library (sibling repo)
