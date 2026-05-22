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

---

## Schema-axis enum-value extensions (v0.2 addition — drift prevention)

A separate sub-case of schema-axis routing surfaced during foundations rebuild Phase 0 (2026-05-22) when `archive/cth-inventory/confluent-trust-inventory-v5_3.json` was found to contain 5 distinct provenance values (`T`, `E`, `D`, `I`, `P`), 3 of which (`D`/`I`/`P`) are not in the upstream CTH v0.3 schema enum. The mismatch had accumulated silently because no CI step validated QBP's inventory against the canonical schema, and was discovered only when `cth migrate --check` ran during Phase 0 prep.

**Rule:** Any PR that adds a value to a CTH-tracked enum (`anchor.provenance`, `anchor.status`, `derived_principles[].layer` discrete values, anchor ID prefixes, etc.) in `archive/cth-inventory/*.json` MUST:

1. **Be routed to cth-implementor** as a required co-signer (this is a schema-axis change, not a theory-axis one — even if the underlying claim is a theory-axis matter)
2. **Have an upstream proposal issue** open on `confluent-trust` BEFORE the QBP-side PR lands. The proposal extends the canonical schema enum to accept the new value
3. **Update `docs/cth/qbp-local-extensions.md`** in the same PR — add a row to the relevant section with the upstream issue link, the mapping to canonical v0.3 values, and rationale
4. **Pass `.github/workflows/cth-schema-lint.yml`** — validates the inventory against the vendored CTH v0.3 schema (`docs/cth/inventory.schema.v0.3.json`). Will reject the PR if the new value isn't yet in the schema enum

**Why a separate rule:** the §"→ cth-implementor (schema-axis)" sub-case above already lists `provenance` as a schema-axis field, but doesn't distinguish between (a) routing a rename/restructure (the original case) and (b) routing an enum-value extension (the new case). Both go to cth-implementor, but (b) additionally requires the canonical mapping doc update AND the upstream extension proposal — without which the value can never round-trip cleanly through `cth migrate`.

**Trigger for invocation:** any of:
- `git diff` on `archive/cth-inventory/*.json` shows a new value in an enum field that isn't already in `docs/cth/inventory.schema.v0.3.json`
- CI workflow `cth-schema-lint` fails with "value must be one of [list]" — the failure message names exactly the field + offending value

**Drift prevention triad (already in place; this rule is the gate):**
| Layer | Mechanism |
|---|---|
| **a** | CI schema-lint (`.github/workflows/cth-schema-lint.yml`) catches drift at PR time |
| **b** | This routing rule forces conversation with cth-implementor when extension IS warranted |
| **c** | `docs/cth/qbp-local-extensions.md` is the canonical mapping table; institutional memory |

---

## Provenance + change history

| Date | Author | Change |
|---|---|---|
| 2026-05-14 | qbp-oppenheimer | v0.1 drafted on bridge seq=11 |
| 2026-05-14 | qbp-implementor | committed to docs/workflows/ as Integration deliverable |
| 2026-05-22 | qbp-implementor | v0.2 — added schema-axis enum-value-extension sub-rule + drift-prevention triad references (foundations rebuild Phase 0 discovery) |

*v0.2; will continue calibrating against actual conflicts as they surface.*
