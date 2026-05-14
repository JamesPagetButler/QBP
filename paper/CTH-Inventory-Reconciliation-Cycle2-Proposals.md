# CTH Inventory Reconciliation — Cycle 2 Per-Anchor Proposals

**Generated:** by `scripts/cth_inventory_proposals.py` (qbp-implementor, 2026-05-14)  
**Inputs:** `archive/cth-inventory/confluent-trust-inventory-v5.13.json` (150) + `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (141)  
**Routing rubric:** `docs/workflows/pr7_conflict_routing_rubric.md` (v0.1, PR #416)  
**Routing authority:** Beekeeper D4 (2026-05-13) — theory-axis → @qbp-oppenheimer; schema-axis → @cth-implementor

---

## 1. Summary

Cycle 1 classified 165 anchor-level differences (126 in-both with diffs + 24 v5.13-only + 15 v5_3-only).
Cycle 2 turns the classification into per-anchor merge proposals to drive Cycle 3 unified-vNext production.

| Bucket | v0.1 count | v0.2 count (with proposed extension) | Routing |
|---|---|---|---|
| NOT_CONFLICT | 77 | 77 | _(auto-fold; no adjudication)_ |
| SCHEMA_AXIS | 23 | 30 | → @cth-implementor |
| THEORY_AXIS | 0 | 0 | → @qbp-oppenheimer |
| TWO_AXIS | 19 | 19 | → both, schema first |
| UNCLASSIFIABLE | 7 | 0 | → bridge escalation (v0.1) or @cth-implementor (v0.2 if extension accepted) |

Plus **24 v5.13-only** and **15 v5_3-only** anchors with per-stream inclusion proposals.

---

## 2. Rubric v0.2 Extension Proposal

Cycle 2 surfaced 19 anchor-fields appearing in the in-both diff that the v0.1 rubric does not classify. Their semantics fall cleanly into two groups:

**SCHEMA_AXIS extensions (proof-system + mapping-classification metadata; →@cth-implementor):**

| Field | Appearances | Why schema-axis |
|---|---|---|
| `physical_mapping_type` | 46 | categorical: how anchor maps to a physical observable |
| `lean_theorem` | 36 | pointer to a Lean theorem ID — proof-system metadata |
| `lean_companion_theorems` | 21 | list of supporting Lean theorems |
| `integration_test_status` | 15 | CI/test-run pass/fail/skip — not theory content |
| `lean_scope` | 8 | Lean namespace/module scope for proof |
| `lean_migration_status` | 5 | migration state of Lean proof (`planned`/`done`/…) |
| `proof_results` | 4 | file pointer to raw test results |
| `proof_note` | 4 | free-text annotation about the proof procedure |
| `physical_mapping_status` | 2 | status of the mapping declaration |
| `physical_mapping_diagnosis` | 1 | diagnostic note about the mapping |
| `lean_migration_scope` | 1 | scope of a Lean migration |
| `lean_migration_remaining` | 1 | what remains to migrate |
| `lean_migration_target_file` | 1 | destination Lean file |
| `analysis_pipeline` | 1 | which analysis pipeline produced the result |
| `python_caveats` | 1 | caveats on a Python proof |
| `supporting_python_proof` | 1 | file pointer to a Python proof |

**THEORY_AXIS extensions (scientific content; →@qbp-oppenheimer):**

| Field | Appearances | Why theory-axis |
|---|---|---|
| `regime_of_validity` | 2 | explicit statement of the domain where a prediction holds — theory content |
| `qbp_threshold_R` | 1 | numeric theory prediction (QBP-side R threshold) |
| `null_threshold_R` | 1 | numeric theory prediction (null-hypothesis R threshold) |

**Effect:** moves the 49 anchors with unclassified fields under v0.1 to (7 additional → SCHEMA_AXIS, 0 additional → THEORY_AXIS, 0 additional → TWO_AXIS) — taking UNCLASSIFIABLE to 0.

**Authority:** Beekeeper sign-off in this PR; @cth-implementor co-sign on the schema additions; @qbp-oppenheimer co-sign on the theory additions.

```diff
 SCHEMA_AXIS_FIELDS = {
   "id", "tier", "provenance", "proof_system", "proof_file",
   "sorry_count", "chain_id", "last_tested_at",
+  "analysis_pipeline",
+  "integration_test_status",
+  "lean_companion_theorems",
+  "lean_migration_remaining",
+  "lean_migration_scope",
+  "lean_migration_status",
+  "lean_migration_target_file",
+  "lean_scope",
+  "lean_theorem",
+  "physical_mapping_diagnosis",
+  "physical_mapping_status",
+  "physical_mapping_type",
+  "proof_note",
+  "proof_results",
+  "python_caveats",
+  "supporting_python_proof",
 }

 THEORY_AXIS_FIELDS = {
   "status", "description", "notes",
   "predicted_value", "predicted_unit",
   "measured_value", "measured_error", "discrepancy_pct",
   "prediction_chain", "interference_hypothesis",
   "interference_type", "converges_with",
+  "null_threshold_R",
+  "qbp_threshold_R",
+  "regime_of_validity",
 }
```

---

## 3. Per-anchor merge proposals (in-both, with diffs)

Each anchor shows: routing recommendation; proposed deterministic resolution where possible; full field diffs (untruncated).

### 3.1 TWO_AXIS — needs both adjudicators (schema first, then theory) — 19 anchor(s)

#### `INSIGHT-iron-handoff-nuclear-to-magnetic` — Iron as the energy handoff point: nuclear harmonics → gravitational collapse → magnetic storage

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["iron_56_g2_alpha_ladder","iron_56_is_fourteen_alphas","iron_decomposition_consistency"] | _(field absent)_ |
| `lean_theorem` | **?** | 'iron_56_double_octet' | _(field absent)_ |
| `notes` | theory | …y have algebraic significance.\n[Session 13, Nucleosynthesis.lean] Algebraic identity 56 = 7×8 now Lean-formalised as `iron_56_double_octet`. Companion theorems show the consistency with 14×4 (G₂ alph… | …y have algebraic significance." |
| `proof_file` | schema | 'QBP/Cosmo/Nucleosynthesis.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `INSIGHT-urca-threshold-dim-O` — Direct URCA threshold x_p = 1/(1+dim(𝕆)) = 1/9: kinematic origin

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_theorem` | **?** | 'urca_threshold_decomposition' | _(field absent)_ |
| `notes` | theory | …ns through spatial kinematics.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `urca_threshold_decomposition`. Build verified under Mathlib v4.30-rc2 with so… | …ns through spatial kinematics.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-TOV-limit-sqrt-7-over-3` — TOV limit = M_Ch × √(7/3) = 2.20 M☉ from Fano plane dimensions

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'lean_companion_theorems', 'lean_scope', 'lean_theorem', 'physical_mapping_diagnosis', 'physical_mapping_status', 'physical_mapping_type', 'regime_of_validity']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'verified-as-regime-specific' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_companion_theorems` | **?** | ["tov_ratio_squared","tov_ratio_pos","predicted_tov_mass_pos"] | _(field absent)_ |
| `lean_scope` | **?** | 'algebraic-identity (squared form) + Real.sqrt extension; M_Ch and M_TOV measured values are inputs not Lean theorems' | _(field absent)_ |
| `lean_theorem` | **?** | 'tov_ratio_squared_decomposition' | _(field absent)_ |
| `notes` | theory | 'Shared prefix. ORIENTATION TRIAD EXTENDED: The same algebraic dimensions that give the CKM CP phase (sin² = 7/8), the η′ mass shift (1/24 = (1/8)(1/3)), and the Koide phase (2/9) also give the stella… | "Shared prefix. ORIENTATION TRIAD EXTENDED: The same algebraic dimensions that give the CKM CP phase (sin² = 7/8), the η′ mass shift (1/24 = (1/8)(1/3)), and the Koide phase (2/9) also give the stella… |
| `physical_mapping_diagnosis` | **?** | 'Sensitivity sweep over the four EOS knobs shows: with asymptotic c_s² LOCKED at 1/3 (the QBP-required value), no combination of bump width × P(ρ₀) × peak position produces M_max ∈ [2.15, 2.25] M_☉. R… | _(field absent)_ |
| `physical_mapping_status` | **?** | 'falsified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/DenseMatter.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `regime_of_validity` | **?** | {"configuration":"bump_peak","asymptotic_or_exact":"exact_in_regime","description":"Mass of NS whose central density sits at the algebraic peak (\u03c1_c \u2248 \u03c1_peak = 2 \u03c1\u2080 where c_s\… | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-chiral-restoration-3rho0` — Full chiral restoration at dim(Im ℍ)·ρ₀ = 3ρ₀: crystallisation onion model

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_companion_theorems` | **?** | ["chiral_at_rho0_is_koide"] | _(field absent)_ |
| `lean_scope` | **?** | 'density-coefficient identity; full ⟨q̄q⟩(ρ) functional form is a linear-extrapolation model not a theorem' | _(field absent)_ |
| `lean_theorem` | **?** | 'chiral_restoration_dim_im_quaternion' | _(field absent)_ |
| `notes` | theory | …ICER measurements of NS radii.\n[Session 14, DenseMatter.lean] Lean theorem `chiral_restoration_dim_im_quaternion` formalises the algebraic-identity content. Build verified under Mathlib v4.30-rc2, so… | …ICER measurements of NS radii.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/DenseMatter.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-ckm-cp-phase-arctan-sqrt7` — CKM CP phase δ_CP = arctan(√7) ≈ 69.3° from octonion dimensionality

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-14T00:00:00Z' |
| `lean_scope` | **?** | 'algebraic-identity only; physical mechanism remains conjectural' | _(field absent)_ |
| `lean_theorem` | **?** | 'cp_phase_sin_squared' | _(field absent)_ |
| `notes` | theory | …an(√7) = 69.295° definitively.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `cp_phase_sin_squared`. Build verified under Mathlib v4.30-rc2 with sorry_coun… | …an(√7) = 69.295° definitively.' |
| `physical_mapping_type` | **?** | 'type_3_statistical' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-conformal-sound-speed-1-over-3` — Conformal sound speed c_s² = 1/dim(Im ℍ) = 1/3 at full chiral restoration

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_status', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_theorem` | **?** | 'conformal_sound_speed_decomposition' | _(field absent)_ |
| `notes` | theory | …ediction. Value is c_s² = 1/3.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `conformal_sound_speed_decomposition`. Build verified under Mathlib v4.30-rc2 … | …ediction. Value is c_s² = 1/3.' |
| `physical_mapping_status` | **?** | 'verified-as-EOS-property' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-eta-prime-mass-shift-1-over-24` — η′ mass shift = m_η′/|Stab| = 957.8/24 = 39.9 MeV at ρ₀

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_scope` | **?** | 'algebraic-identity only; physical mechanism remains conjectural' | _(field absent)_ |
| `lean_theorem` | **?** | 'eta_prime_decomposition' | _(field absent)_ |
| `notes` | theory | …< 25 MeV or Δm > 60 MeV at ρ₀.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `eta_prime_decomposition`. Build verified under Mathlib v4.30-rc2 with sorry_c… | …< 25 MeV or Δm > 60 MeV at ρ₀.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-gamma-universality` — Gamma-reparameterisation reduces decoherence variance

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['analysis_pipeline', 'integration_test_status', 'null_threshold_R', 'physical_mapping_type', 'qbp_threshold_R']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `analysis_pipeline` | **?** | 'reviews/nanorotor_gamma_test_synthetic.py' | _(field absent)_ |
| `integration_test_status` | **?** | 'partial' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | None |
| `notes` | theory | '\n[Session 16] Synthetic six-rotor analysis (1000 trials each hypothesis) gives discrimination thresholds R < 0.526 (QBP-favoured, 5th percentile of null distribution) vs R > 8.46 (QBP-falsified, 95t… | _(field absent)_ |
| `null_threshold_R` | **?** | 8.46 | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `qbp_threshold_R` | **?** | 0.526 | _(field absent)_ |

#### `PRED-holographic-boundary-gravity` — Holographic boundary gravity: a₀ = κ_BH (parent BH surface gravity), MOND as holographic effect

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-13T00:00:00Z' |
| `lean_theorem` | **?** | 'a0_redshift_evolution' | _(field absent)_ |
| `notes` | theory | …or 1-3 gap at cluster scales).\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/RedshiftEvolution.lean as theorem `a0_redshift_evolution`. Build verified under Mathlib v4.30-rc2 with sorry_count… | …or 1-3 gap at cluster scales)." |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/RedshiftEvolution.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-koide-phase-2-over-9` — Koide phase δ_fund = Q/dim(Im ℍ) = 2/9: lepton mass ratios from algebra

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-14T00:00:00Z' |
| `lean_scope` | **?** | 'algebraic-identity only; physical mechanism remains conjectural' | _(field absent)_ |
| `lean_theorem` | **?** | 'koide_phase_decomposition' | _(field absent)_ |
| `notes` | theory | …atios → CKM angles → CP phase.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `koide_phase_decomposition`. Build verified under Mathlib v4.30-rc2 with sorry… | …atios → CKM angles → CP phase.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-lambda-as-cross-term` — Effective Λ as cross-term 2AB between early and late accretion modes

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_scope` | **?** | 'algebraic-identity only; physical mechanism remains conjectural' | _(field absent)_ |
| `lean_theorem` | **?** | 'lambda_cross_term' | _(field absent)_ |
| `notes` | theory | …cretion physics in Universe 1.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `lambda_cross_term`. Build verified under Mathlib v4.30-rc2 with sorry_count =… | …cretion physics in Universe 1." |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-magnetar-energy-fraction-1-over-3` — Magnetar energy fraction E_B/E_grav = 1/dim(Im ℍ) = 1/3

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'lean_companion_theorems', 'lean_theorem', 'physical_mapping_type', 'regime_of_validity']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'verified-as-upper-bound' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_companion_theorems` | **?** | ["magnetar_equals_conformal_cs"] | _(field absent)_ |
| `lean_theorem` | **?** | 'magnetar_fraction_decomposition' | _(field absent)_ |
| `notes` | theory | …ipation, or may need revision.\n[Session 14, DenseMatter.lean] Lean theorem `magnetar_fraction_decomposition` formalises the algebraic-identity content. Build verified under Mathlib v4.30-rc2, sorry_c… | …ipation, or may need revision.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/DenseMatter.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `regime_of_validity` | **?** | {"configuration":"virial_saturation","asymptotic_or_exact":"upper_bound","description":"Theoretical upper bound from pressure-saturated B\u00b2/(2\u03bc\u2080) \u2264 P_local pointwise. Pressure-satur… | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |
| `status` | theory | 'coherent' | 'untested' |

#### `PRED-peak-sound-speed-Q` — Peak sound speed c_s²(peak) ≈ Q = 2/3 at partial crystallisation density

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_companion_theorems` | **?** | ["peak_sound_speed_value"] | _(field absent)_ |
| `lean_theorem` | **?** | 'peak_sound_speed_is_koide' | _(field absent)_ |
| `notes` | theory | … Q and c_s² peak is heuristic.\n[Session 14, DenseMatter.lean] Lean theorem `peak_sound_speed_is_koide` formalises the algebraic-identity content. Build verified under Mathlib v4.30-rc2, sorry_count =… | … Q and c_s² peak is heuristic.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/DenseMatter.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |
| `status` | theory | 'coherent' | 'untested' |

#### `PRED-revival-exact` — Rotational quantum revival time exact (no collapse)

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'physical_mapping_type', 'proof_results']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | None |
| `notes` | theory | '\n[Session 16] Pre-registered prediction. Discriminator: revival fidelity vs mass at fixed decoherence rate distinguishes QBP, CSL (∝ m²), and Diósi-Penrose (∝ m²/R). Computation in archive/qbp-nanor… | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `predicted_unit` | theory | 'ms (T_rev for 20 nm SiO₂ dumbbell)' | _(field absent)_ |
| `predicted_value` | theory | 153.7 | _(field absent)_ |
| `proof_results` | **?** | 'archive/qbp-nanorotor-analysis.py' | _(field absent)_ |

#### `PRED-urca-onset-3rho0` — Direct URCA onset at ρ = dim(Im ℍ)·ρ₀ = 3ρ₀: cooling transition at crystallisation melting point

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_companion_theorems` | **?** | ["urca_chiral_coincidence"] | _(field absent)_ |
| `lean_scope` | **?** | 'density coincidence between URCA threshold and chiral restoration' | _(field absent)_ |
| `lean_theorem` | **?** | 'urca_chiral_at_three_rho0' | _(field absent)_ |
| `notes` | theory | …ρ₀ and the coincidence breaks.\n[Session 14, DenseMatter.lean] Lean theorem `urca_chiral_at_three_rho0` formalises the algebraic-identity content. Build verified under Mathlib v4.30-rc2, sorry_count =… | …ρ₀ and the coincidence breaks.' |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/DenseMatter.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PRED-wolfenstein-A-sqrt-Q` — Wolfenstein A = √Q = √(2/3): CKM hierarchy from Koide ratio

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_scope', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-14T00:00:00Z' |
| `lean_scope` | **?** | 'algebraic-identity only; physical mechanism remains conjectural' | _(field absent)_ |
| `lean_theorem` | **?** | 'wolfenstein_A_squared' | _(field absent)_ |
| `notes` | theory | …g hierarchy to mass hierarchy.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `wolfenstein_A_squared`. Build verified under Mathlib v4.30-rc2 with sorry_cou… | …g hierarchy to mass hierarchy.' |
| `physical_mapping_type` | **?** | 'type_3_statistical' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-M-proportional-to-a` — Parent BH mass proportional to scale factor: M(a) = M₀a, model-independent

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'verified' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_theorem` | **?** | 'a0_inverse_scale_factor' | _(field absent)_ |
| `notes` | theory | …derivation. Model-independent.\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/RedshiftEvolution.lean as theorem `a0_inverse_scale_factor`. Build verified under Mathlib v4.30-rc2 with sorry_cou… | …derivation. Model-independent.' |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/RedshiftEvolution.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-cl6` — Cl(6) charge quantisation in 1/3

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_migration_remaining', 'lean_migration_scope', 'lean_migration_status', 'lean_migration_target_file', 'lean_theorem', 'physical_mapping_type', 'proof_results', 'python_caveats', 'supporting_python_proof']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["charge_zero","charge_one_third","charge_two_thirds","charge_one","multiplicity_zero","multiplicity_one","multiplicity_two","multiplicity_three","total_state_count","su3_decomposition","particle_char… | _(field absent)_ |
| `lean_migration_remaining` | **?** | 'Full Cl(6) algebra construction from ℂ⊗𝕆 in Mathlib remains open. Current Lean file proves the *consequences* (charge spectrum, multiplicities = C(3,N), anomaly cancellation Σ Q = 0, charge quantisat… | _(field absent)_ |
| `lean_migration_scope` | **?** | 'Formalise Furey 2015 derivation: ℂ⊗𝕆 → six Clifford generators → three ladder operators → number operator N → Q = N/3. Mathlib has CliffordAlgebra; the algebraic content is rational once N is constru… | _(field absent)_ |
| `lean_migration_status` | **?** | 'complete (algebraic-consequences scope)' | _(field absent)_ |
| `lean_migration_target_file` | **?** | 'QBP/Cosmo/Cl6.lean' | _(field absent)_ |
| `lean_theorem` | **?** | 'charge_quantisation' | _(field absent)_ |
| `notes` | theory | "\n[Session 13, 2026-04-30] Anchor's proof_system was incorrectly set to 'lean4' with a non-existent proof_file. Corrected to 'python' pointing at archive/QBP-synthetic-charge.py (Furey 2015 reproduct… | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/Cl6.lean' | 'lean4/QBP/GaugeBosons.lean' |
| `proof_results` | **?** | 'archive/QBP-synthetic-charge-results.txt' | _(field absent)_ |
| `python_caveats` | **?** | 'Step 3 of the script reports a sign-convention mismatch in the Clifford anti-commutation check ({α,α} = +2 instead of -2); Step 5 shows charge mismatches for the fundamental ideal before relabeling. … | _(field absent)_ |
| `supporting_python_proof` | **?** | {"file":"archive/QBP-synthetic-charge.py","results":"archive/QBP-synthetic-charge-results.txt","role":"Independent computational verification of full Furey 2015 chain"} | _(field absent)_ |

#### `PROOF-interpolation-function-derived` — MOND interpolation ν(y) = [1+√(1+4/y)]/2 derived from holographic boundary thermodynamics

- **Routing:** **TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer — _includes rubric-gap fields_ `['integration_test_status', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `last_tested_at` | schema | '2026-04-30T00:00:00Z' | '2026-04-27T00:00:00Z' |
| `lean_theorem` | **?** | 'mond_quadratic_identity' | _(field absent)_ |
| `notes` | theory | …polation function as the gap).\n[Session 13, 2026-04-30] Lean-formalised in QBP/Cosmo/AlgebraicIdentities.lean as theorem `mond_quadratic_identity`. Build verified under Mathlib v4.30-rc2 with sorry_c… | …polation function as the gap).' |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `proof_file` | schema | 'QBP/Cosmo/AlgebraicIdentities.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

### 3.2 THEORY_AXIS — → @qbp-oppenheimer — 0 anchor(s)

_(empty)_

### 3.3 SCHEMA_AXIS — → @cth-implementor (batchable) — 23 anchor(s)

#### `INST-ckm` — CKM mixing angles and CP phase (irreducible input)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_migration_status', 'physical_mapping_type', 'proof_note', 'proof_results']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_migration_status` | **?** | 'planned' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_3_statistical' | _(field absent)_ |
| `proof_file` | schema | 'archive/QBP-fano-to-observables-v2.py' | _(field absent)_ |
| `proof_note` | **?** | 'Hessian/Fano expression search; no algebraic CKM prediction found' | _(field absent)_ |
| `proof_results` | **?** | 'archive/QBP-fano-to-observables-results.txt' | _(field absent)_ |
| `proof_system` | schema | 'python' | _(field absent)_ |

#### `MEAS-mult-threshold` — Hessian multiplicities predict threshold correction pattern

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_migration_status', 'proof_note']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_migration_status` | **?** | 'planned' | _(field absent)_ |
| `proof_file` | schema | 'archive/QBP-tier1-tests.py' | _(field absent)_ |
| `proof_note` | **?** | 'Multiplicity-pattern test: mult model chi² = 0.006 vs others > 7' | _(field absent)_ |
| `proof_system` | schema | 'python' | _(field absent)_ |

#### `OBS-cmb-314` — G2 ratio 3/14 = 0.214 vs Planck birefringence 0.342 (1.4 sigma)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_migration_status', 'proof_note']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_migration_status` | **?** | 'planned' | _(field absent)_ |
| `proof_file` | schema | 'archive/QBP-cmb-evaluation.py' | _(field absent)_ |
| `proof_note` | **?** | 'CMB power-spectrum analysis with G₂ ratio 3/14' | _(field absent)_ |
| `proof_system` | schema | 'python' | _(field absent)_ |

#### `PRED-no-dm-particle` — No dark matter particle: SM is complete, gravity corrections explain rotation curves

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['integration_test_status', 'lean_migration_status', 'physical_mapping_type', 'proof_note', 'proof_results']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `lean_migration_status` | **?** | 'planned' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |
| `proof_file` | schema | 'archive/QBP-gravity-foundation.py' | _(field absent)_ |
| `proof_note` | **?** | 'Gravity-foundation derivation: SM algebra has no DM candidate' | _(field absent)_ |
| `proof_results` | **?** | 'archive/QBP-gravity-foundation-results.txt' | _(field absent)_ |
| `proof_system` | schema | 'python' | _(field absent)_ |

#### `PROOF-3gen` — Exactly three generations

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["dimImH_eq_3"] | _(field absent)_ |
| `lean_theorem` | **?** | 'generation_count' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Elements.lean' | 'lean4/QBP/GaugeBosons.lean' |

#### `PROOF-42zd` — Exactly 42 basis-sum zero divisors in sedenions

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_theorem` | **?** | 'zero_divisor_count_42' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Sedenion.lean' | 'lean4/QBP/Sedenion.lean' |

#### `PROOF-bond-complete` — Three Kitaev bond types exhaust spin-1/2 observables (dim Im ℍ = 3)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_theorem` | **?** | 'bond_completeness' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Kitaev.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-c2zt-square` — (C₂zT)² = +1 distinguishes fragile from robust topology

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["c2z_square_minus_one","c2z_reverses_momentum","protection_type_differs"] | _(field absent)_ |
| `lean_theorem` | **?** | 'c2zt_square_plus_one' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Graphene.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-clifford-majorana` — Clifford Cl(0,3) anticommutation = Majorana fermion algebra

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["clifford_collapse_to_quaternion"] | _(field absent)_ |
| `lean_theorem` | **?** | 'clifford_anticommutation' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Kitaev.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-eigenratios` — Eigenvalue ratios 3:2:1 (12:8:4)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["casimir_identification"] | _(field absent)_ |
| `lean_theorem` | **?** | 'coupling_ratios' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Sedenion.lean' | 'lean4/QBP/GaugeBosons.lean' |

#### `PROOF-fano` — Fano mediator theorem

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["fano_line_closure","fano_anticommutative","fano_associative","imaginary_units_square_neg_one","octonion_non_associative","aut_transitive_on_lines","stabiliser_order_24","stabiliser_transitive","g2_d… | _(field absent)_ |
| `lean_theorem` | **?** | 'aut_fano_168' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/QBP_FanoGenesis.lean' | 'lean4/QBP/Sedenion.lean' |

#### `PROOF-helicity-obstruction` — Nonzero total helicity → Wannier obstruction (fragile topology)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["moire_fragile_topology"] | _(field absent)_ |
| `lean_theorem` | **?** | 'dirac_helicity' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Graphene.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-hessian` — Hessian spectrum {0(x16), 4(x4), 8(x8), 12(x4)} at all 42 ZDs

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["hessian_trace_128_universal","hessian_traceSq_1152_universal"] | _(field absent)_ |
| `lean_theorem` | **?** | 'spectrum_unique' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Sedenion.lean' | 'lean4/QBP/Sedenion.lean' |

#### `PROOF-hurwitz-quat` — Hurwitz norm multiplicativity in ℍ (Berry phase = π, Born rule)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["hurwitz_fails_sedenion"] | _(field absent)_ |
| `lean_theorem` | **?** | 'hurwitz_quaternion' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Quaternion.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-kramers` — Kramers theorem: T²=-1, orthogonality, degeneracy (algebraic)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["time_reversal_square_minus_one","kramers_orthogonality"] | _(field absent)_ |
| `lean_theorem` | **?** | 'kramers_degeneracy' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Quaternion.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-majorana-charge` — Majorana central charge c=1/2 from dim(ℝ)/dim(ℂ)

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_theorem` | **?** | 'majorana_central_charge' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Kitaev.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-nonabelian-braid` — Non-abelian anyons from quaternion non-commutativity

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_theorem` | **?** | 'non_abelian_braiding' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Kitaev.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-plaquette-z2` — Quaternion triple product e₁e₂e₃ = -e₀ → Z₂ gauge structure

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["flux_squared_identity","triple_product_all_orderings"] | _(field absent)_ |
| `lean_theorem` | **?** | 'plaquette_flux_z2' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Kitaev.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-quat-closure` — Quaternion subalgebra ℍ ⊂ 𝕊 is closed + Hamilton table verified

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["quaternion_table","eigenspace_gauge_match"] | _(field absent)_ |
| `lean_theorem` | **?** | 'quaternion_closure' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Quaternion.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-shells` — 2n^2 shell capacity from SU(2) fundamental dimension

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["subshell_counts","noble_gas_atomic_numbers"] | _(field absent)_ |
| `lean_theorem` | **?** | 'shell_capacity_formula' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Elements.lean' | 'lean4/QBP/Elements.lean' |

#### `PROOF-su2-lie` — su(2) Lie algebra from imaginary quaternion commutators

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["su2_casimir"] | _(field absent)_ |
| `lean_theorem` | **?** | 'su2_commutation' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Quaternion.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-z2-cover` — SU(2)/Z₂ = SO(3) double cover → Z₂ topological invariant

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_theorem` | **?** | 'double_cover_z2' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Quaternion.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

#### `PROOF-z3-cyclic` — Honeycomb Z₃ cyclic symmetry from quaternion product e₁e₂=e₃

- **Routing:** **SCHEMA_AXIS** → @cth-implementor — _includes rubric-gap fields_ `['lean_companion_theorems', 'lean_theorem', 'physical_mapping_type']` (auto-resolves via §2 rubric v0.2 extension)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `lean_companion_theorems` | **?** | ["honeycomb_chirality","graphene_z3z2"] | _(field absent)_ |
| `lean_theorem` | **?** | 'honeycomb_z3_cyclic' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |
| `proof_file` | schema | 'archive/qbp-lean/QBP/Graphene.lean' | _(field absent)_ |
| `proof_system` | schema | 'lean4' | _(field absent)_ |
| `sorry_count` | schema | 0 | _(field absent)_ |

### 3.4 UNCLASSIFIABLE under rubric v0.1 (→ SCHEMA_AXIS if v0.2 accepted, see §2) — 7 anchor(s)

#### `PRED-H-equals-Mdot-over-M` — H = Ṁ/M: Hubble parameter is the fractional accretion rate of the parent BH

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |

#### `PRED-born-exact` — Born rule holds exactly at all energies

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |

#### `PRED-correlated-alpha-G` — α and G variations must be correlated (both moments of same f(u))

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |

#### `PRED-cosmic-birefringence` — G₂→SU(3) breaking predicts parity-violating CMB polarisation (cosmic birefringence)

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |

#### `PRED-no-gup` — No generalised uncertainty principle corrections

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |

#### `PRED-w-not-minus-1` — Dark energy w(z) ≠ -1: accretion model predicts dynamical DE

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `integration_test_status` | **?** | 'unverified' | _(field absent)_ |
| `physical_mapping_type` | **?** | 'type_2_integrated' | _(field absent)_ |

#### `PROOF-hurwitz` — Hurwitz theorem: only 4 normed division algebras

- **Routing:** **UNCLASSIFIABLE** — rubric extension needed (see §2)
- **Proposed resolution:** _(falls to adjudicator)_

| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|---|
| `physical_mapping_type` | **?** | 'type_1_direct' | _(field absent)_ |

---

## 4. Stream-only anchor inclusion proposals

These anchors exist in one stream only. Each needs an inclusion decision for unified vNext.

### 4.1 v5_3 only — Session-13 closeout additions — 15 anchor(s)

Each of these anchors exists in one stream only. Proposed inclusion in unified vNext:

| Anchor ID | Name | Tier | Status | Provenance | Proposed action |
|---|---|---|---|---|---|
| `COMP-sm-non-unification-at-1loop` | SM gauge couplings do NOT unify at 1-loop: spectral action u | 1 | coherent | I | → adjudicator decides on inclusion |
| `CONV-cd-tower-in-zeta-moments` | MATHEMATICS: Even-level Cayley-Dickson tower (dim Im H, S, c | 4 | coherent | T | **INCLUDE** (Session-13 closeout finding) |
| `CONV-spectral-entropy-zeta` | MATHEMATICS: Chamseddine-Connes-van Suijlekom 2018 derives u | 4 | marginal | T | **INCLUDE** (Session-13 closeout finding) |
| `INSIGHT-bcc-iron-fano-cube` | BCC iron coordination 8 = dim(𝕆): Fano cube geometry in the  | 4 | untested | T | INCLUDE (suggested; META/INSIGHT class) |
| `INSIGHT-fano-cube-universal-compute-cell` | Fano cube as universal compute cell: Locale, BMA, holographi | 2 | untested | T | INCLUDE (suggested; META/INSIGHT class) |
| `KILLED-f4-info-theoretic-justification` | KILLED: 'f_4 = 0 follows from Axiom 1 (information preserved | 3 | incoherent | T | **INCLUDE** (Session-13 closeout finding) |
| `OBS-nist-big-G-2026` | NIST G measurement: 6.67387×10⁻¹¹, 0.0235% below BIPM, compo | 2 | coherent | E | → adjudicator decides on inclusion |
| `PRED-cutoff-scale-0p04-Planck` | Crystallisation cutoff Λ ≈ 0.04 M_Pl ≈ 5×10¹⁷ GeV from f₂ =  | 1 | marginal | I | → adjudicator decides on inclusion |
| `PRED-f4-zero-vacuum-energy` | Spectral action vacuum energy f₄ = 0: information-theoretic  | 1 | marginal | T | → adjudicator decides on inclusion |
| `PRED-inv-alpha-GUT-16pi` | 1/α_GUT ≈ 16π = 50.3: candidate algebraic expression (2.9% f | 2 | untested | T | → adjudicator decides on inclusion |
| `PRED-profile-function-f0-f2-ratio` | Profile function f₀/f₂ = 1/dim(Im ℍ) = 1/3: gravity-gauge ra | 1 | marginal | T | → adjudicator decides on inclusion |
| `PROOF-beta-function-3-times-7` | SU(3) β-function numerator 21 = dim(Im ℍ) × dim(Im 𝕆) = 3×7: | 1 | coherent | T | → adjudicator decides on inclusion |
| `Q28-alpha-GUT-from-stabiliser` | Q28: Is α_GUT = 1/(|Stab|+1) = 1/25? The missing link for de | 2 | incoherent | T | → adjudicator decides on inclusion |
| `WISDOM-003-there-is-only-f-u` | W-003: Forces are moments of a spectrum. The spectrum is the | 1 | coherent | T | DEFER to wisdom-registry migration (per Beekeeper D2) |
| `WISDOM-schema-vs-instance` | WISDOM: The algebra is the schema, the boundary is the insta | 1 | coherent | T | DEFER to wisdom-registry migration (per Beekeeper D2) |

### 4.2 v5.13 only — federation-tenancy stream additions — 24 anchor(s)

Each of these anchors exists in one stream only. Proposed inclusion in unified vNext:

| Anchor ID | Name | Tier | Status | Provenance | Proposed action |
|---|---|---|---|---|---|
| `FLAG-tov-eos-shape-underdetermined` | TOV integration with QBP-only EOS inputs gives M_max = 3.3 M | 2 | resolved | I | → adjudicator decides on inclusion |
| `INSIGHT-cross-platform-per-feature-class` | Cross-platform Γ-test works within feature class, not across | 3 | coherent | I | INCLUDE (suggested; META/INSIGHT class) |
| `INSIGHT-eos-integration-shifts-tov-by-30pct` | Robust QBP TOV prediction: M_TOV ∈ [2.6, 2.8] M_☉ from algeb | 2 | coherent | I | INCLUDE (suggested; META/INSIGHT class) |
| `INSIGHT-gamma-needs-cross-platform` | Γ-universality test needs cross-platform pooling for multi-σ | 3 | untested | I | INCLUDE (suggested; META/INSIGHT class) |
| `META-physical-mapping-status-field` | CTH schema extension: physical_mapping_status field on PRED- | 4 | coherent | P | INCLUDE (suggested; META/INSIGHT class) |
| `META-regime-of-validity-field` | CTH schema extension: regime_of_validity field | 4 | coherent | P | INCLUDE (suggested; META/INSIGHT class) |
| `OBS-btfr-z-range-validity` | BTFR (1+z) correction supported at 1<z<10, possibly breaks a | 2 | resolved | E | → adjudicator decides on inclusion |
| `OBS-jades-gs-z14-0-vrot-lower-100` | JADES-GS-z14-0 ALMA tentative rotation: v_rot > 100 km/s (Sc | 2 | marginal | E | → adjudicator decides on inclusion |
| `OPEN-Q-parent-bh-retardation-derivation` | Open: rigorous derivation of parent-BH retardation kernel | 3 | untested | T | → adjudicator decides on inclusion |
| `PRED-a0-redshift-linear` | a₀(z) = a₀(today)·(1+z) from M(a) = M₀·a | 3 | marginal | T | → adjudicator decides on inclusion |
| `PRED-a0-saturating-Fmax-7` | Matter-era a₀(z) saturates with F_max = dim(Im 𝕆) = 7 | 1 | coherent | T+L | → adjudicator decides on inclusion |
| `PRED-a0-saturating-matter-era` | a₀(z) saturates at high z due to matter-era parent-BH dynami | 2 | marginal | I | → adjudicator decides on inclusion |
| `PRED-a0-saturation-factor-fano` | Matter-era a₀(z) saturation factor F_max = dim(Im 𝕆) = 7 | 2 | marginal | I | → adjudicator decides on inclusion |
| `PRED-btfr-mass-correction` | BTFR mass-inference correction at high z: M_b(z) = M_b(0)/(1 | 3 | coherent | T | → adjudicator decides on inclusion |
| `PRED-hypergraph-cmb-camb-rerun` | Branch A CMB matches Planck under hypergraph (multi-party) b | 3 | untested | T | → adjudicator decides on inclusion |
| `PRED-jwst-kinematics-z14` | JWST/ALMA z>10 IFU rotation curves: v_rot 25-30% lower than  | 2 | untested | I | → adjudicator decides on inclusion |
| `PRED-tov-mass-at-bump-peak` | M(NS with ρ_c at algebraic bump peak) = 2.20 M_☉ | 2 | coherent | I | → adjudicator decides on inclusion |
| `PROOF-alpha-particle-quaternion` | α-particle (⁴He) mass number = dim ℍ = 4 | 1 | coherent | T | → adjudicator decides on inclusion |
| `PROOF-fano-choice-information` | Fano line selection requires exactly ln 7 nats | 1 | coherent | T | → adjudicator decides on inclusion |
| `PROOF-iron-56-double-octet` | Iron-56 mass number = dim(Im 𝕆) × dim 𝕆 = 7 × 8 | 1 | coherent | T | → adjudicator decides on inclusion |
| `PROOF-iron-to-ns-bridge` | Iron-56 → neutron-star mass bridge through dim(Im 𝕆) = 7 | 1 | coherent | T | → adjudicator decides on inclusion |
| `PROOF-oxygen-16-sedenion` | O-16 mass number = (dim ℍ)² = dim 𝕊 = 16 | 1 | coherent | T | → adjudicator decides on inclusion |
| `PROOF-seed-mass-from-ln7` | Seed mass M_seed = sqrt(ln 7 · ℏc / 4πG) | 1 | coherent | T | → adjudicator decides on inclusion |
| `PROOF-silicon-28-fano-ladder` | Si-28 mass number = dim(Im 𝕆) × dim ℍ = 7 × 4 | 1 | coherent | T | → adjudicator decides on inclusion |

---

## 5. Cycle 3 plan (unified vNext)

Sequencing:

1. **Beekeeper sign-off on rubric v0.2 extension** (§2) — collapses UNCLASSIFIABLE → SCHEMA_AXIS.
2. **@cth-implementor batch resolution of SCHEMA_AXIS bucket** (23 v0.1 → 30 v0.2 after extension). Schema rule defaults are deterministic where noted; cases needing schema-lock discussion route via the `cth-design` channel.
3. **@qbp-oppenheimer per-anchor theory-axis adjudication for TWO_AXIS bucket** (19 anchors) — schema fields land first per (2); theory fields land next using the v5_3 (Session-13) closeout default where Oppenheimer concurs.
4. **Stream-only inclusion decisions** (§4): KILLED-/CONV-/CONJ- Session-13 closeout findings → INCLUDE by default; WISDOM-* defer to the wisdom-registry migration per Beekeeper D2; META-/INSIGHT- from federation-tenancy → INCLUDE by default; everything else → adjudicator.
5. **qbp-implementor produces unified vNext JSON** — `archive/cth-inventory/confluent-trust-inventory-vNext.json` — with full provenance trail (which fields came from which stream, which adjudicator signed off).
6. **BMA re-audit hook** — once vNext lands, BMA (when ready) re-runs the audit per Capability #6 against the unified ledger; ρ_net trajectory shows continuous (no schema breaks).

---

## 6. Provenance

- Script: `scripts/cth_inventory_proposals.py`
- Input v5.13: `archive/cth-inventory/confluent-trust-inventory-v5.13.json` (267472 bytes, 150 anchors)
- Input v5_3: `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (231104 bytes, 141 anchors)
- Rubric v0.1: `docs/workflows/pr7_conflict_routing_rubric.md` (PR #416)
- Cycle 1 delta: `paper/CTH-Inventory-Reconciliation-Delta-v0.1.md` (PR #418)
- Tracked baselines: `archive/cth-inventory/` (PR #422; Beekeeper option (b) of a+b+c, 2026-05-14)
