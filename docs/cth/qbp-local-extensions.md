# QBP-local extensions to the CTH schema

**Purpose:** single source of truth for every QBP-local extension to the canonical CTH inventory schema. Each row documents WHAT the local value means, WHY it exists, and WHEN/HOW it will round-trip to canonical CTH v0.3 values.

**Status:** v0.1 — first canonicalised record post-foundations-rebuild Phase 0 discovery (2026-05-22). Authored by qbp-implementor.

**Governing rule** (per `docs/cth/README.md` and `docs/workflows/pr7_conflict_routing_rubric.md`):

> Every QBP-local extension to a CTH inventory enum value MUST be either:
> 1. **Already canonical** in upstream `confluent-trust` (in which case it's not really a local extension), OR
> 2. **Tracked here with an upstream extension issue link**, AND co-signed by `@cth-implementor` on the QBP PR that introduces it.

If a value lands in `archive/cth-inventory/*.json` that isn't (1) or (2), the CI schema-lint rejects the PR.

---

## Provenance values (`anchor.provenance`)

### CTH v0.3 canonical (always allowed)

| Value | Meaning |
|---|---|
| `T` | Theoretical (prose-stage; gets refined to `theory` or `theory-external` via `cth migrate --decisions`) |
| `E` | Experimental |
| `H` | Hypothesis |

### QBP-local extensions (require upstream issue + co-sign)

| Value | Count in v5_3 | Intended CTH v0.3 ProvenanceKind | Upstream extension issue |
|---|---|---|---|
| `D` | 15 | `theory` (programme-derived from CTH chain) | confluent-trust #88 (proposed; extends `MigrationDecision` to accept) |
| `I` | 8 | `internal-compute` (calculation-derived inferred claim) | confluent-trust #88 |
| `P` | 10 | `theory` + `proof_state: partial` (partial verification) | confluent-trust #88 (extends decisions file with optional `proof_state`) |

**Migration plan (post confluent-trust #88 landing):** run `cth migrate v0.2 → v0.3 --decisions <d.json>` with per-anchor mappings; D/I/P legacy values translate to canonical v0.3 ProvenanceKind values; no further QBP-local provenance extensions needed.

**Forward rule:** after the migration, no new D/I/P values should land in inventory writes. New anchors should use canonical CTH v0.3 ProvenanceKind values directly. The CI schema-lint will reject D/I/P additions once the v0.3 schema removes them from the enum (upstream change pending confluent-trust #88 closure).

---

## Status values (`anchor.status`)

### CTH v0.3 canonical (per architect's "propagate-upstream ruling" at confluent-trust #71)

| Value | Meaning |
|---|---|
| `coherent` | Anchor is consistent with programme |
| `incoherent` | Anchor conflicts with programme |
| `marginal` | Anchor sits at the boundary; weak evidence either way |
| `untested` | Anchor not yet validated |
| `killed` | Anchor invalidated by experimental/derivational evidence |
| `converged` | Multiple chains converge on this anchor; load-bearing |
| `falsified` | Specific prediction failed empirical test |

### QBP-local extensions

None at v5_3 baseline. Discovery response §6 noted possible future need for `pending-verification` or similar — would require upstream proposal first.

---

## Tier values (`anchor.tier`)

CTH schema requires `tier >= 1`. v5_3 had one anchor (`INST-ckm`) with `tier: 0` — caught by `cth migrate --check` at the schema validation step. **This is not an extension** — it's a data quality issue and will be fixed inline (`tier: 0` → `tier: 1`) during migration. Documented here only so future reviewers know what to look for.

---

## Layer values (`derived_principles[].layer`)

Same story as tier: CTH schema requires `layer >= 1`. v5_3 had one entry (`DERIV-crystallisation-asymptotic`) with `layer: 0`. Fix inline during migration.

---

## Anchor ID prefixes

Per discovery response action item §5 and QBP #433 (pending architect ratification), 22 known prefixes are in use:

| Prefix | Meaning |
|---|---|
| `PRED-*` | Prediction |
| `PROOF-*` | Theorem with formal proof reference |
| `OBS-*` | Observation |
| `MEAS-*` | Measurement |
| `FLAG-*` | Programme flag |
| `INSIGHT-*` | Synthesised insight |
| `REF-*` | External reference |
| `EXT-*` | External anchor |
| `CONV-*` | Convention |
| `COMP-*` | Computation |
| `CONSTRAINT-*` | Constraint |
| `WISDOM-*` | Wisdom-layer claim |
| `INST-*` | Instance (single empirical fit) |
| `PARTIAL-*` | Partially-resolved claim |
| `Q27-*`, `Q28-*` | Open question anchors |
| `KILLED-*` | Killed-hypothesis (status equivalent; legacy) |
| `DEFN-*` | Definition (foundations rebuild proposal; pending) |
| `AXIOM-*` | Axiom (foundations rebuild proposal; pending) |
| `DERIV-*` | Derived (used in `derived_principles`, not yet in `anchors`) |
| `CONJ-*` | Conjecture / open conjecture (foundations rebuild + `provenance_kind: hypothesis`) |
| `CHAIN-*` | Chain (used in `chains`, not yet in `anchors`) |
| `FORK-*` | Fork branch |

The DEFN/AXIOM/CONJ/CHAIN/FORK extensions land formally with the foundations rebuild Phase 1 anchor cohort PR. Not yet upstream-registered; will require a confluent-trust schema extension to add to the JSON Schema enum (parallel to confluent-trust #88).

---

## Change history

| Date | Author | Change |
|---|---|---|
| 2026-05-22 | qbp-implementor | v0.1 — initial canonicalisation post-Phase-0 discovery (D/I/P documented; confluent-trust #88 referenced) |

— qbp-implementor, foundations rebuild Phase 0

---

## Axiom decision fields (`axioms[].decision_state`, `axioms[].kill_condition`)

**Status:** QBP-local since PR #659 (ledger 5.7.1, 2026-09-14); required by #654 D3 (the root gate's four-bucket exit, `scripts/root_audit.py`, PR #658). Validate today under `$defs/Axiom.additionalProperties: true` in the vendored schema (`docs/cth/inventory.schema.v0.3.json`, synced from confluent-trust #98; canonical-PR status per the sidecar `inventory.schema.v0.3.meta.json`). **Upstream extension issue:** confluent-trust #102 (canonical delta owned by @cth-implementor; drafted after the AXIOM-2 encode lands, with AXIOM-1's record as the test vector). **Co-sign on the introducing PR:** @cth-implementor, #659 issuecomment-5658368053 (pinned to head 762b7b4; field surface unchanged since).

| Field | Type | Meaning | Gate reading (`root_audit.py`) |
|---|---|---|---|
| `decision_state` | enum `open` \| `ruled` | decision lifecycle, distinct from the coherence `status` enum. `open` = the root is an Impasse Record with a stated falsifier; `ruled` = a scope/process ruling exists and is cited by a `JamesPagetButler/*` GitHub URL in `ruling` (structural check; the semantic half is the Red Team confirmer's) | `open` + `kill_condition` ⇒ bucket-3 OPEN; `ruled` + cite ⇒ bucket-2 FORCED |
| `kill_condition` | non-placeholder string | the falsifier: the ledger-observable event that fires the kill, and (where stated) the discharge arm. Named `kill_condition`, not `kill`, to avoid collision with the anchor field `killed_by`. Invariant (cth-implementor): `decision_state: open` ⇒ `kill_condition` present — nothing parks open without a kill | required for bucket-3 |

**Current usage:** `AXIOM-1` — `decision_state: "open"`, `kill_condition` = two armed questions (process; scope of the selection clause), each with kill and discharge, trigger #647. No other root carries the fields yet (META-1, AXIOM-2 are in the open-roots register, #655 / #473).

**Forward rule:** no other QBP-local field on `Axiom` records without a row here and an upstream issue. When confluent-trust #102 lands, this row is marked canonical and the vendored schema is synced per `schema-change-propagation-checklist.md`.
