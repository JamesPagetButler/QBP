# `docs/cth/` — CTH schema discipline for the QBP tenant

This directory holds the vendored canonical CTH schema and the QBP-local extension mapping. It exists to **prevent schema drift between QBP's local inventory and upstream CTH** from being discovered at migration time — which is what happened with `confluent-trust-inventory-v5_3.json` (5 distinct legacy provenance values not in upstream enum; surfaced during foundations rebuild Phase 0 → confluent-trust #88).

## Contents

| File | Purpose | Update cadence |
|---|---|---|
| `inventory.schema.v0.3.json` | Vendored copy of `confluent-trust/schema/inventory.schema.json` at the v0.3 release. The CI workflow reads it indirectly via the `inventory.schema.current.json` symlink. | When upstream CTH schema bumps (rare; v0.3 is the stable canonical) |
| `inventory.schema.v0.3.meta.json` | Provenance metadata for the vendored schema: upstream commit SHA, vendoring date, sha256 of schema file, QBP PR that vendored it. Re-checked on each refresh. | Bumped at refresh time |
| `inventory.schema.current.json` (symlink → `.v0.3.json`) | Stable pointer the CI workflow targets. Future v0.4 refresh = retarget the symlink, no CI edit needed. | Retargeted when schema version bumps |
| `qbp-local-extensions.md` | Canonical mapping of QBP-local provenance/status/etc. values to their CTH v0.3 equivalents, with rationale + upstream-extension issue links | When QBP introduces new local extensions; each new extension requires an upstream proposal |

## Why vendor the schema instead of fetching it from upstream

- **No PAT needed** — upstream `confluent-trust` is private; vendoring avoids CI credential setup
- **Reproducible builds** — pinned schema means CI fails consistently on real drift, not on upstream churn
- **Auditable drift** — diff between vendored and upstream schema is a single grep; refresh PR is small and reviewable

## Refresh procedure

When upstream CTH ratifies a new schema version (e.g., v0.4):

1. `cp <upstream>/cth/schema/inventory.schema.json docs/cth/inventory.schema.v0.4.json` (new versioned filename)
2. Retarget symlink: `ln -sf inventory.schema.v0.4.json docs/cth/inventory.schema.current.json`
3. Write `docs/cth/inventory.schema.v0.4.meta.json` (provenance metadata; copy v0.3.meta.json shape, update fields)
4. Update `qbp-local-extensions.md` if new extensions land upstream
5. Run `.github/workflows/cth-schema-lint.yml` locally against `archive/cth-inventory/*.json` to verify QBP still passes
6. Open a Tier-2 PR with `@cth-implementor` as required reviewer (per `docs/workflows/pr7_conflict_routing_rubric.md` schema-axis routing)

The CI workflow targets `inventory.schema.current.json` (not `.v0.3.json`) so step 2 is the only file the workflow cares about. Old versioned schemas (`.v0.3.json`, etc.) remain in-repo for audit.

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
