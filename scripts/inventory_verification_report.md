# Inventory Verification Report

**Generated:** 2026-05-22 (foundations rebuild Phase 0)
**Author:** qbp-implementor
**Scope:** map the 254 zero-`sorry` Lean theorems in `proofs/` against the 141 CTH anchors in `archive/cth-inventory/confluent-trust-inventory-v5_3.json`; surface orphans, phantoms, and stale-path drift.
**Source-of-truth inputs:**
- `proofs/` (Lean corpus; toolchain `leanprover/lean4:v4.30.0-rc2`)
- `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (141 anchors, schema v0.2)

This report is the **inverse** of `cth migrate`: that tool walks CTH anchors and translates them forward to v0.3; this report walks Lean theorems and asks "is each one anchored, and does its anchor cite a real file?" It surfaces work needed in three categories: anchor-side gaps, Lean-side phantoms, and citation-style drift.

---

## 1. Summary statistics

| Metric | Count |
|---|---|
| `.lean` files in `proofs/` (excluding `.lake/`) | 23 |
| Total theorems + lemmas (zero-`sorry` per `lake build`) | **254** |
| QBP/ proper | 185 |
| Sprint12-Inherited/ | 69 |
| CTH anchors in v5_3.json | 141 |
| PROOF-* anchors total | 28 |
| PROOF-* with `proof_file` field set | 10 |
| PROOF-* with `proof_file == null` | 18 |
| Anchors referencing existing on-disk Lean files | 4 |
| Anchors referencing **phantom** files (don't exist) | 6 |
| Anchors with citation-style `proof_file` (e.g., "Hurwitz 1898") | 2 |
| Anchors referencing Python artefacts | 1 |

The headline gap: **18 of 28 PROOF-* anchors have no `proof_file` reference** (orphan on the anchor side), and **6 of the 10 PROOF-* anchors that DO cite a file cite a non-existent path** (phantom on the Lean side). Less than 15% of PROOF-* anchors round-trip cleanly today.

---

## 2. Lean theorem corpus inventory

Per-file theorem counts (matches `grep -cE "^(theorem|lemma) [a-zA-Z]"` against `proofs/` excluding `.lake/`):

### QBP/ proper (185 theorems across 16 files)

| File | Theorems |
|---|---|
| `proofs/QBP.lean` | 0 (root module; imports only) |
| `proofs/QBP/Basic.lean` | 6 |
| `proofs/QBP/Cosmo/AlgebraicIdentities.lean` | 13 |
| `proofs/QBP/Cosmo/Cl6.lean` | 18 |
| `proofs/QBP/Cosmo/DenseMatter.lean` | 15 |
| `proofs/QBP/Cosmo/FanoChoiceInformation.lean` | 2 |
| `proofs/QBP/Cosmo/Nucleosynthesis.lean` | 16 |
| `proofs/QBP/Cosmo/RedshiftEvolution.lean` | 4 |
| `proofs/QBP/Cosmo/SeedMass.lean` | 4 |
| `proofs/QBP/Experiments/AngleDependent.lean` | 12 |
| `proofs/QBP/Experiments/DoubleSlit.lean` | 32 |
| `proofs/QBP/Experiments/General3D.lean` | 12 |
| `proofs/QBP/Experiments/SternGerlach.lean` | 6 |
| `proofs/QBP/Foundations/LieAlgebraIso.lean` | 17 |
| `proofs/QBP/Optics/Fraunhofer.lean` | 5 |
| `proofs/QBP/Units/Constants.lean` | 9 |
| `proofs/QBP/Units/ScaleFactors.lean` | 14 |

`proofs/QBP/Oracle/*.lean` and `proofs/QBP/Units/{GenTestVectors,Oracle}.lean` are executable / test-vector generation rather than theorem-bearing modules.

### Sprint12-Inherited/ (69 theorems across 7 files)

| File | Theorems |
|---|---|
| `proofs/Sprint12-Inherited/Bi2Se3.lean` | 6 |
| `proofs/Sprint12-Inherited/Crystallisation.lean` | 6 |
| `proofs/Sprint12-Inherited/Elements.lean` | 12 |
| `proofs/Sprint12-Inherited/Graphene.lean` | 11 |
| `proofs/Sprint12-Inherited/Kitaev.lean` | 13 |
| `proofs/Sprint12-Inherited/Quaternion.lean` | 11 |
| `proofs/Sprint12-Inherited/Sedenion.lean` | 10 |

Total: **254 theorems** (matches discovery response §1.1).

---

## 3. CTH anchor → Lean file coverage

### 3.1 Anchors that cleanly resolve to existing Lean files (4 of 10 with proof_file)

These need only path-prefix normalisation (`lean4/QBP/` → actual current location) but the file content exists:

| Anchor | Cited path | Actual file | Status |
|---|---|---|---|
| PROOF-shells | `lean4/QBP/Elements.lean` | `proofs/Sprint12-Inherited/Elements.lean` | ✓ resolvable (stale prefix) |
| PROOF-42zd | `lean4/QBP/Sedenion.lean` | `proofs/Sprint12-Inherited/Sedenion.lean` | ✓ resolvable (stale prefix) |
| PROOF-fano | `lean4/QBP/Sedenion.lean` | `proofs/Sprint12-Inherited/Sedenion.lean` | ✓ resolvable (stale prefix) |
| PROOF-hessian | `lean4/QBP/Sedenion.lean` | `proofs/Sprint12-Inherited/Sedenion.lean` | ✓ resolvable (stale prefix) |

**Action:** anchor `proof_file` field updates to current paths (housekeeping; can run during Phase 0.5 or Phase 1).

### 3.2 Phantom file references (3 anchors → non-existent `GaugeBosons.lean`)

| Anchor | Cited path | Likely actual content |
|---|---|---|
| PROOF-cl6 | `lean4/QBP/GaugeBosons.lean` | `proofs/QBP/Cosmo/Cl6.lean` (18 theorems; name match) |
| PROOF-eigenratios | `lean4/QBP/GaugeBosons.lean` | unclear — needs investigation |
| PROOF-3gen | `lean4/QBP/GaugeBosons.lean` | unclear — needs investigation |

`GaugeBosons.lean` does not exist anywhere in `proofs/` or `archive/`. `Cl6.lean` was likely a refactor/rename of `GaugeBosons.lean` at the Sprint 12 → current architecture transition. PROOF-cl6 obviously maps to `Cl6.lean`; the other two need theorem-level audit to determine where their proofs migrated to (or whether the proofs were lost).

**Action:** open the GaugeBosons.lean tracking issue (per v1.0 prompt Phase 0 deliverable #5) and assign anchor-level forensics work.

### 3.3 Citation-style references (theory-external candidates)

| Anchor | `proof_file` value | Re-grade target |
|---|---|---|
| PROOF-hurwitz | "Hurwitz 1898" | `provenance_kind: theory-external` + `theory_citation: "Hurwitz 1898"` |
| PROOF-born | "Hurwitz corollary" | `provenance_kind: theory-external` + `theory_citation: "Hurwitz 1898, corollary"` (or self-citation) |

These are not migration bugs — they're correctly identifying that the proof is an external published theorem. The v0.3 `theory-external` provenance kind is the canonical home. They become decisions-file entries when CTH `cth migrate --decisions` runs (post confluent-trust #88 landing).

### 3.4 Python artefact (internal-compute candidate)

| Anchor | `proof_file` value | Re-grade target |
|---|---|---|
| PROOF-g2 | `QBP-boundary-cell-model.py` | `provenance_kind: internal-compute` (per confluent-trust #88 extension) |

The script lives in `archive/`. Either re-grade to `internal-compute` or formalise in Lean (Phase 2+ work).

### 3.5 PROOF-* anchors without any `proof_file` (18 orphans)

These claim PROOF-* status but cite no file. Per discovery response §6: foundation-side orphans — proofs likely exist somewhere in `proofs/` but the anchor doesn't say where.

| Anchor | Provenance | Likely host file (hypothesis) |
|---|---|---|
| PROOF-quat-closure | T | `proofs/Sprint12-Inherited/Quaternion.lean` |
| PROOF-su2-lie | T | `proofs/QBP/Foundations/LieAlgebraIso.lean` |
| PROOF-kramers | T | likely Sprint12-Inherited or QBP/Cosmo |
| PROOF-hurwitz-quat | T | `proofs/Sprint12-Inherited/Quaternion.lean` |
| PROOF-z2-cover | T | `proofs/Sprint12-Inherited/Kitaev.lean` |
| PROOF-z3-cyclic | T | `proofs/Sprint12-Inherited/Quaternion.lean` (cyclic group structure) |
| PROOF-c2zt-square | T | `proofs/Sprint12-Inherited/Kitaev.lean` |
| PROOF-helicity-obstruction | T | unclear |
| PROOF-plaquette-z2 | T | `proofs/Sprint12-Inherited/Kitaev.lean` |
| PROOF-clifford-majorana | T | `proofs/QBP/Cosmo/Cl6.lean` |
| PROOF-nonabelian-braid | T | `proofs/Sprint12-Inherited/Kitaev.lean` |
| PROOF-majorana-charge | T | `proofs/QBP/Cosmo/Cl6.lean` |
| PROOF-bond-complete | T | `proofs/Sprint12-Inherited/Crystallisation.lean` |
| PROOF-stelle-no-linear | P | `proofs/QBP/Cosmo/` (partial — proof_state: partial) |
| PROOF-interpolation-function-derived | T | unclear |
| PROOF-M-proportional-to-a | T | `proofs/QBP/Cosmo/` |
| PROOF-division-algebra-entropy-cone-mapping | T | `proofs/QBP/Cosmo/AlgebraicIdentities.lean`? |
| PROOF-beta-function-3-times-7 | T | unclear |

**Action:** Phase 1 work — for each orphan, locate the actual theorem(s) in the Lean corpus and back-fill `proof_file` + `lean_theorem` + (post-#88) `theorems[]` per the v0.3 schema. Mint `DEFN-*` companions where the anchor is a definitional claim rather than a derivable theorem.

---

## 4. Inverse audit — theorems lacking anchors

A full Lean-theorem-by-theorem inverse audit (254 theorems × anchor lookup) is Phase 6 scope per the foundations-rebuild instantiation prompt §5. This Phase 0 report establishes the population (254) and surfaces the structural shape; per-theorem orphan resolution is deferred.

Spot-check, however: only 4 anchors currently cite a Lean file that exists, so **at minimum 250 of 254 theorems are anchor-orphaned today**. Phase 6 will systematically:

- Either back-fill an anchor (for theorems that warrant first-class CTH presence), OR
- Explicitly mark the theorem as unanchored-by-design in `analysis/foundations-orphan-resolutions.md` with reason (e.g., "implementation detail", "auxiliary lemma", "convention-bound notation").

Many theorems will be the latter — every multi-step proof has supporting lemmas that don't need CTH anchors. The triage is the work.

---

## 5. Drift findings — sources of future drift to prevent

### 5.1 Stale path prefix `lean4/QBP/`

7 anchors cite `lean4/QBP/<file>.lean`. The actual repo structure at this date is `proofs/QBP/` (current QBP work) and `proofs/Sprint12-Inherited/` (inherited corpus folded via QBP PR #422). The `lean4/` prefix is an artefact of the pre-lake project structure.

**Action:** mechanical anchor-side update from `lean4/QBP/` → actual paths. Bundle into the Phase 1 anchor cohort PR.

### 5.2 Phantom GaugeBosons.lean

3 anchors cite `GaugeBosons.lean` which has no on-disk equivalent. PROOF-cl6 obviously maps to `Cl6.lean`; PROOF-eigenratios and PROOF-3gen need theorem-level forensics.

**Action:** dedicated tracking issue (filed as part of this PR).

### 5.3 Mixed proof-file formats

CTH `proof_file` is conventionally a path string, but in v5_3.json it carries 3 distinct shapes:
- Actual file path (with current or stale prefix)
- Citation-style ("Hurwitz 1898", "Hurwitz corollary") — these are inherently theory-external, not files
- Python artefact path

**Action:** post confluent-trust #88 landing, citation-style refs migrate to `theory_citation` field; Python refs migrate to `internal-compute` provenance_kind.

### 5.4 No Mathlib pin (until this PR)

`proofs/lakefile.lean` previously had `require mathlib from git "..." ` with no `@ <ref>` pin. `lake update` resolved a SHA into `lake-manifest.json` but it could drift on the next `lake update`. **This PR pins to the resolved SHA** so subsequent `lake update` is reproducible.

---

## 6. Phase 0 recommendations + follow-up housekeeping

1. **Mathlib pin (this PR, done):** `proofs/lakefile.lean` now pins to the resolved SHA from lake-manifest. Reproducible across machines.
2. **GaugeBosons.lean tracking issue (this PR, filed separately):** assigns the theorem-level forensics work for PROOF-eigenratios + PROOF-3gen migration.
3. **Run `cth migrate v0.2 → v0.3 --decisions <d.json>`** — blocked on confluent-trust #88 (extends `MigrationDecision` to support QBP-local I/P/D provenance values + ProofState override).
4. **Stale-prefix anchor updates** — mechanical; bundle into Phase 1 cohort PR.
5. **Re-grade citation-style + Python proof_file values** — bundle into Phase 1 cohort PR; depends on #88 for theory-external citation field round-trip.
6. **Phase 1 anchor back-fill** — for the 18 orphan PROOF-* anchors, locate actual Lean theorems and populate `proof_file` + `lean_theorem` + `theorems[]`.
7. **Phase 6 inverse audit** — per-theorem orphan resolution against the 254 corpus; produce `analysis/foundations-orphan-resolutions.md`.

---

## 7. Closing note on report shape

This report is **descriptive, not prescriptive**. It catalogues the current state of the Lean ↔ CTH boundary so Phase 1 prose authoring can proceed with full knowledge of:
- which proofs exist where (Section 2),
- which anchors are wired up correctly (Section 3.1),
- which need surgery (Sections 3.2-3.5),
- and which work is gated on what (Section 6).

The numbers (254 theorems / 28 PROOF-* / 4 cleanly-wired / 6 phantoms / 18 orphans / 131 anchors-without-proof_file) are reproducible by re-running the queries embedded in Sections 2-3 against the same `v5_3.json` baseline. Future runs against migrated `v5_3.v0.3.json` will produce a different shape — that's the point of the migration.

— qbp-implementor, foundations rebuild Phase 0
