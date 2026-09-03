# CTH Schema-Change Propagation — QBP Operational Checklist

**Companion to** the canonical governing doc `confluent-trust:doc/design/schema-change-propagation.md` (R16). That doc is the *why* + the phased strategy; this is the *how*, QBP-side, for the mirror owner (`qbp-implementor`). Front-half local-extension governance: `docs/cth/qbp-local-extensions.md`.

**Phase:** Crawl (manual vendor + co-sign). This checklist is the Crawl enforcement mechanism.

---

## When this fires

Any change to the CTH schema — a new anchor field, a new enum value, a relaxed/added constraint. Before touching the QBP mirror, classify two things (governing doc §2, §4):

- **Flow direction:** upstream-first (default) · QBP-local-awaiting-upstream · landed-via-catch-all→formalize-upstream.
- **Semver class:** **minor** (additive/optional field, no new `Validate` constraint, `cth migrate` no-op → mirror may lag safely; may ride the consuming PR) or **major** (new required field, new constraint, enum removal → breaking; the mirror PR MUST merge before any QBP inventory writes the field).

---

## Per-change checklist (QBP mirror side)

For every schema change, in order:

- [ ] **1. Vendored schema** — apply the canonical delta to `docs/cth/inventory.schema.v0.3.json`. For a schema authored upstream, cth-implementor hands you the exact content; **you are the single writer on the file** (one hand per file — avoids the concurrent-write hazard). Bump `x-schema-semver` and the mirrored `$id` (e.g. `0.3.2 → 0.3.3`).
- [ ] **2. Sidecar** — update `docs/cth/inventory.schema.v0.3.meta.json`:
  - `schema_document_semver` → new semver.
  - `vendored_sha256_of_schema_file` → recompute: `sha256sum docs/cth/inventory.schema.v0.3.json`.
  - `vendored_on_date_utc` → today.
  - `synced_from_upstream_pr` → the canonical confluent-trust PR (or "pending canonical PR #N — vendored-first per R16 minor same-day sync" when the mirror rides ahead).
  - `vendored_upstream_commit_sha` → the canonical commit once it merges.
  - `vendored_by_pr` → the QBP PR carrying this mirror change.
  - Append the change to `_comment_semver`'s cumulative list.
- [ ] **3. Cross-field lint** — if the field participates in a cross-field invariant, update `scripts/check_cth_invariants.py` (and `scripts/check_anchor_manifest.py` if it touches the proof-evidence bar — e.g. the `derivation` delta extended C3-FULL's G1).
- [ ] **4. Validate locally, both sides:**
  - schema is valid JSON Schema + backward-compatible with the current ledger:
    `python3 -c "import json; from jsonschema import Draft202012Validator as V; s=json.load(open('docs/cth/inventory.schema.v0.3.json')); V.check_schema(s); inv=json.load(open('archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json')); e=list(V(s).iter_errors(inv)); print('errors:', len(e))"`
  - the proof gate is green: `python3 scripts/check_anchor_manifest.py`.
- [ ] **5. Sequencing (major only)** — the mirror PR merges before any QBP inventory record writes the new field. (Minor: the mirror may ride the same PR as the records that use it.)
- [ ] **6. Co-sign upstream** — co-sign the canonical confluent-trust PR (`model/*.go` + `schema/*.json` + semver bump). Upstream is source of truth; the vendored copy must end byte-identical.
- [ ] **7. Downstream fixtures** — sync `qbp-systema/pkg/bookkeeper/testdata/*.json` from canonical, or document the divergence.
- [ ] **8. CI green** — `cth-schema-lint` passes on the QBP PR (validates `archive/cth-inventory/*.json` against the bumped vendored schema).

---

## Worked example — 0.3.3 `derivation` (FAULT-S4-007 / #621)

The first change run through this checklist. Flow: **upstream-first**. Class: **minor** (additive enum value + *relaxed* constraint — no new required field).

1. Vendored schema: added `"derivation"` to `$defs/ProvenanceKind.enum`; relaxed the C1 conditional `{"not":{"const":"proof"}}` → `{"not":{"enum":["proof","derivation"]}}` (verification-fields now allowed on `{proof, derivation}`); `x-schema-semver`/`$id` `0.3.2 → 0.3.3`. cth authored the content; qbp-implementor committed it (one hand).
2. Sidecar bumped: semver 0.3.3, sha256 recomputed, `synced_from_upstream_pr` → the canonical derivation-delta PR, `vendored_by_pr` → QBP #621, cumulative-list appended.
3. Cross-field: `check_anchor_manifest.py` gained the **G1** clause — the clean-evidence bar extends to a `derivation` that shows verification (a dirty proof can't be laundered as a derivation).
4. Validated: schema valid + ledger backward-compatible + gate green.
5. Minor → the vendored schema + the 17 records that use `derivation` rode the same PR (#621); canonical PR followed same-day, byte-identical.
6–8. Co-signed upstream; fixtures N/A (no bookkeeper field); `cth-schema-lint` green.

---

## Notes

- The **semver is the spine** — Toddle's drift-check and Walk's consume-by-reference both key on `schema_document_semver`, so keep it accurate in *both* the schema `$id`/`x-schema-semver` and the `.meta.json` sidecar; a mismatch between them is itself a drift incident.
- **Ownership:** the mirror + sidecar + this checklist + the Toddle drift-check CI are qbp-implementor's; the canonical schema + Go model + governing doc are cth-implementor's; theory-axis content is oppenheimer/qbp-architecture; merges are the beekeeper's (governing doc §6).
- Refresh procedure detail: `docs/cth/README.md §Refresh procedure`.
