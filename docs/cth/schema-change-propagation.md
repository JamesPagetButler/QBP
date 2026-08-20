# CTH Schema-Change Propagation — QBP-side Operational Companion

**Scope:** the QBP integration lane's operational steps for keeping the vendored CTH schema mirror in sync with canonical upstream (`confluent-trust`). This is the **operational** half. The **federation-canonical governing rules** (the phase model, the minor/major contract, the merge-ordering rule) are owned upstream by the schema authority (`@cth-implementor`).

> **Cross-link status:** the canonical governing doc is referenced by the v0.3.1 schema description as `confluent-trust:doc/design/schema-change-propagation.md` but is **not yet authored** (404 at `7a226c70`). Until it lands, treat the phase/contract summary below as a working transcription of the `cth-qbp-live-testing` seq 27–33 design, to be replaced by a cross-link once upstream publishes. Tracked under **#488**.

Companion to [`qbp-local-extensions.md`](./qbp-local-extensions.md) (the QBP-local extension front-half) and [`README.md` §Refresh procedure](./README.md) (the mechanical refresh steps). This doc is the *why + when*; the README is the *how*.

---

## 1. The mirror surface (what can drift)

The canonical CTH schema lives upstream at `confluent-trust:schema/inventory.schema.json`. QBP **vendors** a pinned copy so CI (`cth-schema-lint.yml`) validates with zero upstream credentials. The vendored surface:

| File | Role |
|---|---|
| `docs/cth/inventory.schema.v0.3.json` | the vendored schema copy CI validates against |
| `docs/cth/inventory.schema.v0.3.meta.json` | provenance sidecar: upstream commit SHA, vendoring date, sha256, `schema_document_semver`, vendoring PR |
| `docs/cth/inventory.schema.current.json` | symlink → `.v0.3.json` (stable CI target) |
| `archive/cth-inventory/*.json` | the inventory data validated against the above |

**Drift = the vendored copy lags canonical.** That is the failure mode this process exists to prevent (precedents: the v5.24 fork, the stale-#483 base, and the #97 lag this doc's first run fixed).

## 2. Three version concepts (do not conflate)

1. **Inventory content version** — e.g. `5.4.0`; changes when *anchors* change. Not what propagation keys on.
2. **Schema generation** — `cth_schema_version: v0.3`; coarse schema family.
3. **Schema-document semver** — `x-schema-semver` in the schema `$id`, mirrored as `schema_document_semver` in the sidecar (e.g. `0.3.1`). **This is the load-bearing primitive** the Toddle drift-check and Walk pin-by-reference key on. The sidecar value and the schema `$id` must match; the drift-check asserts equality.

## 3. Minor / major contract

- **Minor** (additive/optional, `migrate` no-op — e.g. v0.3.1's `killed_by`/`foundation_batch`/`class_floors`): old validators still pass (`additionalProperties: true`), so the **mirror may lag safely**. Sync promptly, but it is not a write-blocker.
- **Major** (new required field / new `Validate` constraint / enum removal): the **mirror must update before QBP writes** inventory under the new schema.

## 4. Three flow directions

| Direction | Example | Governed by |
|---|---|---|
| **Upstream-first** — canonical → mirror | #97 (v0.3.1), #92 (`peer_review_status`) | this doc (§5) |
| **QBP-local awaiting upstream** — local extension used via catch-all, proposal filed up | D/I/P provenance values | [`qbp-local-extensions.md`](./qbp-local-extensions.md) |
| **Catch-all → formalize upstream → back to mirror** (round-trip) | `killed_by`/`review_flag` (lived in QBP data via `additionalProperties`, then formalized in #93/#97, now flow back down) | both: extensions doc for the front-half, this doc for the back-half |

## 5. QBP-side refresh procedure (upstream-first)

When `confluent-trust` merges a schema change:
1. Vendor the merged `schema/inventory.schema.json` **byte-identical** at the merge commit (`gh api …/contents/…?ref=<merge-sha>`), overwriting `inventory.schema.v0.3.json`.
2. Update the sidecar (README §Refresh steps 2–4, 6): recompute sha256, bump date, **populate `vendored_upstream_commit_sha`** with the merge SHA, set `schema_document_semver` to match the schema's `x-schema-semver`, record the vendoring PR.
3. **Verify (refresh step 5):** every `archive/cth-inventory/*.json` still validates against the new schema (`jsonschema` + `check_cth_invariants.py`). For a minor bump this should pass unchanged; if it does not, the change was mis-classified as minor.
4. Open a QBP PR, **tag `@cth-implementor`** to co-sign that the vendored content matches the upstream merge commit. Refs the propagation issue (#488), does not close it.
5. Land **before** any dependent upstream PR that rebases onto the change (e.g. #97 before #98's 0.3.2 link), so the rebase chain stays current.

## 6. Phase graduation (Crawl → Toddle → Walk)

- **Crawl (now):** manual vendor + `@cth-implementor` co-sign + this checklist. Drift prevented by *discipline*.
- **Toddle:** a `schema-sync-check` CI job pins the **published** upstream schema semver and fails the build if the vendored mirror drifts. Drift caught by *detection*. **Trigger:** confluent-trust publishes schema releases as versioned artifacts (a published-artifact pin needs no PAT — it dissolves the private-repo-read dependency). **Owed — not yet built.**
- **Walk:** the schema stops being vendored — published once by confluent-trust on the Wyrd/NATS substrate and consumed by pinned reference. Drift becomes *impossible by construction* (no second copy). The `schema_document_semver` introduced at Crawl is what consumers pin to.

## 7. Worked example — the first real run (and a sequencing-inversion lesson)

The first run exercised the **out-of-order-merge** case, which is exactly why §5 step 5 pins to "current canonical," not a planned intermediate:

- confluent-trust **#97** merged → canonical **0.3.1** (`killed_by`/`foundation_batch`/`class_floors`). QBP **#549** opened, vendoring 0.3.1 from `7a226c70`, finally pinning the upstream SHA (a `TODO` placeholder since the #459 vendoring).
- Before #549 landed, confluent-trust **#98** merged → canonical advanced to **0.3.2** (`axis_trust`/`locale_domain`/`cluster_state` — sheaf trust). The planned order (`#549@0.3.1 → later 0.3.2 refresh`) inverted.
- **Lesson applied:** merging #549 at 0.3.1 would have landed the mirror *already one version stale* — re-creating the drift it exists to close. So #549 was **re-pointed straight to 0.3.2** (`confluent-trust@18c91db`, sha256 `56ebd180…`), skipping the now-pointless 0.3.1 intermediate. One mirror PR, not two.

**Rule this hardens:** a mirror PR always vendors **current canonical at merge time**, never the version it was opened against. If upstream advances while the mirror PR is open, re-point before merge (cheap — byte-copy + sidecar bump + re-co-sign), don't merge-then-refresh. Both are minor/additive (mirror-may-lag class), so the re-point is a clean swap, not a migration.

## 8. Open items

- **Upstream canonical governing doc** (`confluent-trust:doc/design/schema-change-propagation.md`) — referenced by the schema but not authored; `@cth-implementor` deliverable. When it lands, §2–3 + §6 here collapse to a cross-link.
- **Toddle `schema-sync-check` CI** — owed (this lane); gated on upstream schema-release publishing.
- Both tracked under **#488**.
