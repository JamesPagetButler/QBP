# #619 — Orphan-Proof Disposition Record

**Owner:** @qbp-oppenheimer (theory-state) · **Process:** [`proof-anchor-best-practices.md`](proof-anchor-best-practices.md) · **Beekeeper-directed**

The under-claim mirror of the over-claim burn-down (#617/#615/#613). The inverse-anchor audit found **576 orphan theorems** — proven in `proofs/**/*.lean`, cited by **no** CTH anchor, every one `sorry`-free and `native_decide`-free (real kernel-verified proof). This is the honest per-theorem disposition of all 576, and the ledger encode that recovers the anchor-worthy work.

**No silent skips.** Every theorem is either anchored (with a `provenance_kind` and witnessed evidence) or marked auxiliary with a stated reason. This file gives the cluster-level disposition; the **exhaustive per-theorem table** (every one of the 748 in-scope declarations → anchor id or reason) is in [`619-orphan-disposition-full.md`](619-orphan-disposition-full.md).

**Review-driven revisions (#628, Furey/Feynman):** `PROOF-fraunhofer-optics` was reclassified **proof → `DERIV-fraunhofer-optics`** — the intensity function encodes the far-field diffraction model, so its properties are true *given that model*, matching how the QBP spin-prediction anchors are treated. `PROOF-octonion-sedenion-exp-log` had its description sharpened (the group law is the **single-axis one-parameter** law, valid in 𝕊 via power-associativity; the full `exp(x+y)=exp(x)exp(y)` is neither claimed nor true in 𝕊). `PROOF-bpm-si-round-trip` confirmed **proof** (the scale factor is a free parameter → pure invertibility, no constant baked in).

## Result summary

| | Count |
|---|---:|
| Orphans dispositioned | **576 / 576** (15 clusters, 30 files) |
| → new **proof** anchors' witnesses | 23 deliverables |
| → new **derivation** anchors' witnesses (model/ansatz/constant-gated) | 12 deliverables |
| → existing anchors extended | PROOF-su2-lie (theory→proof, +Casimir), PROOF-42zd (+42-plane construction) |
| → **auxiliary** (stated reason, no anchor) | ~378 theorems |
| Ledger anchors | 235 → **270** |
| Anchor-worthy manifest entries | 10 → **46** |
| Inverse-audit orphans | 580 → **49** (residual = all dispositioned-auxiliary) |

**Evidence bar (C3-FULL):** every proof anchor carries a captured `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}`. Zero `native_decide`, zero `sorry`. Gates green: `check_anchor_manifest.py` exit 0; `anchor_inverse_audit.py --check` exit 0.

## Disposition by cluster

Each row: the anchor-worthy witnesses (→ their deliverable anchor) and the count of auxiliary theorems (plumbing / coordinate lemmas / bundled members / restatements).

### Foundations — proof deliverables

| Cluster (file) | Orphans | Anchor deliverable(s) | Aux |
|---|---:|---|---:|
| `Breakdown.lean` | 26 | operations-ladder ✗-cells → `PROOF-ops-order/commutativity/associativity/alternativity/norm-composition/division-ladder`; the 42 → `PROOF-42zd` (extended) | 12 |
| `TowerLaws.lean` | 49 | operations-ladder ✓-cells ℝ/ℂ/ℍ → the 7 `PROOF-ops-*-ladder` anchors; CD level-2 iso (dedup: existing `quaternion_is_cayley_dickson_level2`) | 31 |
| `OctonionLaws.lean` | 55 | `PROOF-octonion-moufang`, `PROOF-power-associativity`, `PROOF-ops-flexibility-ladder` (𝕆/𝕊), `PROOF-ops-norm-composition-ladder` (𝕆) | 45 |
| `CrossProduct.lean` | 37 | `PROOF-octonion-cross-product` (10 witnesses; 𝕊-obstruction cross-ref Breakdown) | 27 |
| `CDLifting.lean` | 27 | `PROOF-ops-alternativity-ladder` (octonion_alternative), `PROOF-cd-associator-formula` | 25 |
| `CDAlg.lean` + `CDBridge.lean` | 66 | `PROOF-cd-product-formula`, `PROOF-cd-structure-constant-tables`, `PROOF-cd-associativity-level2` | 57 |
| `Exp.lean` + `Artin*.lean` | 110 | `PROOF-artin-theorem` (Artin's theorem), `PROOF-octonion-sedenion-exp-log` (Euler + group law + inverses + 𝕆·𝕊 cells) | 88 |
| `NormForm` + `FanoOrientationF3` + `SedenionOctonionCount` + `Octonion32Count` | 41 | `PROOF-norm-form-bilinear`, `PROOF-cd-structure-constant-tables` (Fano), `PROOF-sedenion-zero-divisor-witnesses` (7 cells), `PROOF-sedenion-alternative-hyperplane-count` (8/15), `PROOF-octonion-32dim-alternative-count` (k(5)=50, 42=35+7) | 12 |
| `LieAlgebraIso.lean` | 17 | `PROOF-su2-lie` (updated: +`imH_structure_constants` +`imH_casimir`) | 16 |
| `ScaleFactors.lean` | 14 | `PROOF-bpm-si-round-trip` | 12 |

### Physics — proof (optics/quaternion facts) + derivation (model-gated)

| Cluster (file) | Orphans | Anchor deliverable(s) | Aux |
|---|---:|---|---:|
| `DoubleSlit` (pure quaternion algebra + bounds) | (in 72) | **proof:** `PROOF-doubleslit-quaternion-algebra`, `PROOF-doubleslit-visibility-bounds` (bounds on the defined ratio, no ansatz) | |
| `SternGerlach`/`AngleDependent`/`General3D`/`DoubleSlit`(visibility model)/`Fraunhofer` | (in 72) | **derivation:** `DERIV-sterngerlach-qbp`, `DERIV-angle-dependent-qbp`, `DERIV-general3d-qbp`, `DERIV-doubleslit-visibility-model` (Model A), `DERIV-fraunhofer-optics` (far-field model — reclassified proof→derivation in the #628 review) | 25 |
| `Basic.lean` + `Units/Constants.lean` | 15 | **derivation:** `DERIV-measurement-ansatz-basic`, `DERIV-code-si-constants`. **0 proof** (all ansatz/constant-gated) | 4 |
| Sprint-12 materials (`Kitaev`/`Graphene`/`Quaternion`/`Bi2Se3`/`Crystallisation`) | 47 | **derivation:** `DERIV-kitaev-model`, `DERIV-graphene-model`, `DERIV-bi2se3-ti`, `DERIV-crystallisation-spectral-moments`, `DERIV-quaternion-physics-kramers`. **0 new proof** (4 pure-math items Q2/Q3/Q8/Q9 are see-also dedups to Foundations anchors) | 15 |

## Proof-vs-derivation discipline

The whole point of this pass (post-FAULT-S4-005). A result that bakes in a physical ansatz, a chosen Hamiltonian/lattice, or numeric constants is **`derivation`** — true *given that model*, never a model-independent proof. Physics files therefore yield **zero** pure-math `proof` anchors except genuine optics/quaternion identities (Fraunhofer, double-slit algebra).

## House-clean flags surfaced (none ledger-cited; no live over-claim)

The sweep reads every orphan, so it also reports source-level traps it found. Full-ledger name-grep confirmed none were cited as `proof`.

1. **`mott_from_hessian` (Graphene) — was vacuous** (`true && true`, verified nothing; FAULT-S4-005 shape). **Fixed in this PR:** now checks the real Hessian spectrum {0,4,8,12}·{16,4,8,4} tied to Tr(H²)=1152. Remains auxiliary (model-parallel).
2. **`flux_squared_identity` (Kitaev) — docstring over-claim** (checked e₀² only, not (e₁e₂e₃)²). **Fixed in this PR:** now genuinely squares e₁e₂e₃. Auxiliary.
3. **`PROOF-su2-lie` Casimir over-claim** — description asserted "Casimir verified" with no witness. **Fixed in this PR:** `imH_casimir` authored; anchor promoted theory→proof.
4. **Numerology-as-proof class** (author-chosen constants satisfy author-designed relations) — derivation at most, never proof; kept auxiliary or bundled as derivation with premise named.

## The 49 residual orphans (all dispositioned-auxiliary)

Named in `analysis/foundations-inverse-anchor-audit.json`. They are: the Artin proof-machinery (`ArtinCore`/`ArtinSpan`/`ArtinTrace` — `assoc_*`, `*_mem_span_gen4`, `span4_*`; self-labeled "core lemmas only, does NOT prove Artin"), CDAlg coordinate plumbing (`N_add`, `cdAlg_mul_zero`, `reCoord_add`, …), and the 7 bundled `fanoTriple_oriented_{123,145,167,246,257,347,356}` members (their bundle `fanoTriples_oriented` **is** anchored). None are anchor-worthy.

## Follow-ups (tracked, not folded into this PR)

- **Absolute orphan gate (PATTERN-02):** the audit currently uses a count-baseline (49). Converting it to read an explicit auxiliary allowlist — so residuals are *declared*, not *tolerated by count* — is the "orphan audit → absolute gate" tooling task noted in the best-practices doc. Filed separately (cth/qbp-implementor lane).
- **CI build-invisibility gap:** `check_layer_imports.py` Rule-3 covers only `Foundations/`, not the physics dirs — how `General3D.lean` was build-invisible. Filed separately.
- **Sedenion-table single source:** the 16×16 table is re-embedded in 6 Sprint-12 files. Filed separately.

---
*Disposition adjudicated by qbp-oppenheimer; encoded via `scripts/encode_619_anchors.py`; gate-validated. Pending cth §I4 (schema authority) review.*
