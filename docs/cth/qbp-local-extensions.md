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

## Root decision fields (`decision_state`, `kill_condition` on any record in a root list)

**Status:** QBP-local since PR #659 (ledger 5.7.1, 2026-09-14); required by #654 D3 (the root gate's four-bucket exit, `scripts/root_audit.py`, PR #658). Validate today under `$defs/Axiom.additionalProperties: true` in the vendored schema (`docs/cth/inventory.schema.v0.3.json`, synced from confluent-trust #98; canonical-PR status per the sidecar `inventory.schema.v0.3.meta.json`). **Upstream extension issue:** confluent-trust #102 (canonical delta owned by @cth-implementor; drafted after the AXIOM-2 encode lands, with AXIOM-1's record as the test vector). **Co-sign on the introducing PR:** @cth-implementor, #659 issuecomment-5658610585 (re-pinned to head d6ac91b after the string→array re-cut; earlier pins issuecomment-5658354408 / -5658368053).

| Field | Type | Meaning | Gate reading (`root_audit.py`) |
|---|---|---|---|
| `decision_state` | enum `open` \| `settled` (renamed from `ruled` in canonical 0.3.4: the settled state is reached by proof or force, never by fiat) | decision lifecycle, distinct from the coherence `status` enum. `open` = the root is an Impasse Record with a stated falsifier; `settled` = a scope/process ruling exists and is cited by a `JamesPagetButler/*` GitHub URL in `ruling` (structural check; the semantic half is the Red Team confirmer's) | `open` + `kill_condition` ⇒ bucket-3 OPEN; `settled` + cite ⇒ bucket-2 FORCED |
| `kill_condition` | array<object> `KillConditionEntry` — `{kill (required, non-placeholder), closure ∈ {derivation, measurement, ruling-rescope} (required), discharge}` (canonical 0.3.4, confluent-trust#104; migrated from array<string> on QBP #665) | one entry per open question; `discharge` names the resolving anchor if the route exists, else a LIVE `FLAG-`/`CONJ-` tracker (route OPEN); absent only for `ruling-rescope`. root_audit's `kill_present` checks every entry semantically (placeholder-token, discharge resolves to a live anchor of the matching kind) and the D6 report tags each entry route EXISTS / route OPEN / constitutional. |

**Current usage (after #662, ledger 6.2.0 (root fields since 6.0.0; KillConditionEntry objects since 6.2.0)):** `AXIOM-1` (two-entry list, #647); `META-2`, `POST-boundary-encoding`, `POST-hosting`, `POST-observer-associativity`, `POST-observation`, `INTERP-holographic-boundary` — all `decision_state: open` with one-or-more-entry kill lists (four of them cannot fire today and say so). META-1 is in the open-roots register (#655); AXIOM-2 is retired.

**Forward rule:** no other QBP-local field on `Axiom` records without a row here and an upstream issue. When confluent-trust #102 lands, this row is marked canonical and the vendored schema is synced per `schema-change-propagation-checklist.md`.


---

## QBP-local top-level lists (`meta_principles`, `interpretations`, `retired_axioms`, `retired_principles`)

**Status:** QBP-local since PR #662 (ledger 6.2.0 (root fields since 6.0.0; KillConditionEntry objects since 6.2.0), 2026-09-18); validate under the schema's top-level `additionalProperties: true`. **Upstream tracking issue:** https://github.com/JamesPagetButler/confluent-trust/issues/103 (promotion to canonical `$defs` when the shape freezes; @cth-implementor owns the delta together with #102). **Co-sign on the introducing PR:** @cth-implementor, #662.

| List | Records | Why a separate list | Gate reading (`root_audit.py`) |
|---|---|---|---|
| `meta_principles` | epistemic roots (`META-*`; today META-2 level saturation) | the canonical `meta_axiom` is a single object; a second epistemic root needs a list | a root list: every record must sort (open + kill list) or be registered |
| `interpretations` | `INTERP-*` records — `provenance_kind: philosophy` + `decision_state` + `kill_condition` (cth-implementor, live-test 1297: no new kind) | the schema pins `derived_principles` ids to `^DERIV-` | a root list (the gate's `INTERP-` prefix) |
| `retired_axioms` / `retired_principles` | records retired as roots/principles, kept verbatim with a dated `notes` string saying where their content went (AXIOM-2 → POST-boundary-encoding + META-2 + DERIV-encoding-level; DERIV-holographic → the flag-3 split) | the record is the audit trail; nothing is deleted | reported (bucket-4), not gated |

**No further record-level fields.** Records in these lists carry only the schema's fields, the two D3 fields, and — for INTERP — `provenance_kind`. Evidence-anchor lists and supersession pointers are prose in the pre-existing `notes` field, not new fields (PR #662 Red Team R1: a `kind` taxonomy was ruled out at #654 D3(b)).
