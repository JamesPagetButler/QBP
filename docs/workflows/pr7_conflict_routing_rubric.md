# PR7 Conflict-Routing Rubric — v5.13 ↔ v5_3

**Purpose:** classify a content conflict between the two inventory streams without round-tripping every time.
**Source:** Beekeeper D4 decision 2026-05-13 (`pr407-conflict-resolution` bridge channel; split: theory-axis → qbp-oppenheimer; schema-axis → cth-implementor).
**Status:** v0.1 — drafted by qbp-oppenheimer (bridge seq=11, 2026-05-14); committed to docs/workflows/ by qbp-implementor (Integration role).
**Anchor verifications:** schema verified from `archive/confluent-trust-inventory-v5_3.json` (top-level fields = `programme, version, timestamp, meta_axiom, axioms, derived_principles, anchors, inputs, chains, confluence_points, missed_opportunities, forks, changelog`; anchor fields = 23). Anchor-count verification (Python `json.load + len`): v5.13 = 150, v5_3 = 141, v5.1 = 140, v5_1-original = 138.

---

## Single-axis classification (most cases)

### → qbp-oppenheimer (theory-axis)

Differing field ∈ {`status`, `description` (substantive), `notes` (scientific update), `predicted_value`, `predicted_unit`, `measured_value`, `measured_error`, `discrepancy_pct`, `prediction_chain` (content), `interference_hypothesis`, `interference_type`, `converges_with`, `last_tested_at` (if status flip implied)}

**Example (KILLED-f4-info-theoretic-justification):** v5_3 has it as `status: incoherent` citing CCvS 2018; v5.13 has no such anchor. Theory-axis: programme claim about reality changed.

### → cth-implementor (schema-axis)

Differing field ∈ {`id` (rename only), `tier`, `provenance`, `proof_system`, `proof_file`, `sorry_count`, `chain_id` (placeholder vs real), `prediction_chain` (reference format only), `last_tested_at` (alone)}

**Example:** v5_1-original `id: DerivedPrinciple-koide-3-2-1` vs v5_3 `id: DERIV-koide-3-2-1`, otherwise identical. Schema-axis: renaming for v0.2 migration.

## Two-axis (joint, sequential: schema first to lock ID, then theory for content)

- ID renamed AND status changed
- new axiom added (schema) AND downstream chains changed (theory)
- forks branch labels differ (schema) AND branch membership differs (theory)

## Not-actually-conflicts (skip routing, handle in-stream)

- One stream adds anchor X via its own changelog → not conflict, intentional
- `last_tested_at` differs but theory content identical → mechanical, cth-implementor in migration
- `converges_with` superset evolution → not conflict

## Fast lookup

```
diff_field ∈ theory-set → qbp-oppenheimer
diff_field ∈ schema-set → cth-implementor
both hit → both, schema first
```

## Escalation back to bridge

Unclassifiable conflict → post to `pr407-conflict-resolution` (or successor channel) with anchor ID, differing fields, 1-line "why I can't classify." Rubric extends with each new case.

---

## Provenance + change history

| Date | Author | Change |
|---|---|---|
| 2026-05-14 | qbp-oppenheimer | v0.1 drafted on bridge seq=11 |
| 2026-05-14 | qbp-implementor | committed to docs/workflows/ as Integration deliverable |

*v0.1; will calibrate against first 5-10 actual conflicts surfaced during PR7 reconciliation.*
