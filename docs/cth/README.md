# `docs/cth/` — CTH schema discipline for the QBP tenant

This directory holds the vendored canonical CTH schema and the QBP-local extension mapping. It exists to **prevent schema drift between QBP's local inventory and upstream CTH** from being discovered at migration time — which is what happened with `confluent-trust-inventory-v5_3.json` (5 distinct legacy provenance values not in upstream enum; surfaced during foundations rebuild Phase 0 → confluent-trust #88).

## Contents

| File | Purpose | Update cadence |
|---|---|---|
| `inventory.schema.v0.3.json` | Vendored copy of `confluent-trust/schema/inventory.schema.json` at the v0.3 release. Used by `.github/workflows/cth-schema-lint.yml` to validate any change to `archive/cth-inventory/*.json` at PR time. | When upstream CTH schema bumps (rare; v0.3 is the stable canonical) |
| `qbp-local-extensions.md` | Canonical mapping of QBP-local provenance/status/etc. values to their CTH v0.3 equivalents, with rationale + upstream-extension issue links | When QBP introduces new local extensions; each new extension requires an upstream proposal |

## Why vendor the schema instead of fetching it from upstream

- **No PAT needed** — upstream `confluent-trust` is private; vendoring avoids CI credential setup
- **Reproducible builds** — pinned schema means CI fails consistently on real drift, not on upstream churn
- **Auditable drift** — diff between vendored and upstream schema is a single grep; refresh PR is small and reviewable

## Refresh procedure

When upstream CTH ratifies a new schema version:

1. `cp <upstream>/cth/schema/inventory.schema.json docs/cth/inventory.schema.v0.3.json` (or rename for new version)
2. Update `qbp-local-extensions.md` if new extensions land upstream
3. Run `.github/workflows/cth-schema-lint.yml` locally against `archive/cth-inventory/*.json` to verify QBP still passes
4. Open a Tier-2 PR with `@cth-implementor` as required reviewer (per `docs/workflows/pr7_conflict_routing_rubric.md` schema-axis routing)

## Why this exists (drift-prevention triad)

Three layered preventions catch schema drift at PR time rather than migration time:

| Layer | Mechanism | Catches |
|---|---|---|
| **a** | CI schema-lint (`.github/workflows/cth-schema-lint.yml`) | Any anchor with off-schema enum value, missing required fields, or shape drift in `archive/cth-inventory/*.json` |
| **b** | Routing-rubric extension (`docs/workflows/pr7_conflict_routing_rubric.md` schema-axis) | New provenance/status values requiring `@cth-implementor` co-sign |
| **c** | This canonical mapping doc (`qbp-local-extensions.md`) | Institutional memory; single source of truth for QBP-local extensions |

(a) is load-bearing — makes drift impossible to merge silently. (b) is the process gate when extensions ARE warranted. (c) is documentation.

## Anti-pattern to avoid

Do **NOT** add a new local provenance / status / kind value to `archive/cth-inventory/*.json` without:

1. Opening an upstream issue on `confluent-trust` to propose the addition to the canonical schema enum
2. Updating `qbp-local-extensions.md` with the proposed mapping + upstream issue link
3. Refreshing `inventory.schema.v0.3.json` once upstream lands the extension
4. Tagging `@cth-implementor` on the QBP-side PR per the routing rubric

If you skip (1), CI will reject the inventory change. That's the point.

— qbp-implementor, foundations rebuild Phase 0
