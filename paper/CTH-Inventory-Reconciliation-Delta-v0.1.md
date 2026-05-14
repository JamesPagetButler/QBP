# CTH Inventory Reconciliation Delta — v5.13 ↔ v5_3

**Generated:** by `scripts/cth_inventory_diff.py` (qbp-implementor, 2026-05-14)
**Routing rubric:** `docs/workflows/pr7_conflict_routing_rubric.md` (PR #416)
**Authority:** Beekeeper D4 (2026-05-13) — theory-axis → qbp-oppenheimer; schema-axis → cth-implementor

---

## Headline counts

| | v5.13 (federation-tenancy) | v5_3 (Session-13) |
|---|---|---|
| Total anchors | 150 | 141 |
| Anchor IDs only in this stream | 24 | 15 |
| Anchor IDs in both | 126 | 126 |

## In-both anchor classification (per rubric)

| Class | Count | Route |
|---|---|---|
| NOT_CONFLICT | 77 | (skip — handle in-stream) |
| SCHEMA_AXIS | 23 | → cth-implementor |
| THEORY_AXIS | 0 | → qbp-oppenheimer |
| TWO_AXIS | 19 | → both, schema first |
| UNCLASSIFIABLE | 7 | → escalate to bridge |

---

## Top-level schema differences

- Top-level keys only in v5.13: `['programme_health', 'session_log']`
- Top-level keys only in v5_3: `['changelog']`

## Anchor-field schema differences

- Anchor fields only in v5.13: `['F_max_interpretation', 'F_max_value', 'analysis_pipeline', 'discriminator', 'experimental_backing', 'functional_form', 'integration_test_status', 'lean_companion_theorems', 'lean_migration_remaining', 'lean_migration_scope', 'lean_migration_status', 'lean_migration_target_file', 'lean_scope', 'lean_theorem', 'literature_constraints', 'null_threshold_R', 'physical_mapping_diagnosis', 'physical_mapping_status', 'physical_mapping_type', 'predicted_value_hi', 'predicted_value_lo', 'predicted_values', 'prediction_at_z_14', 'proof_note', 'proof_results', 'python_caveats', 'qbp_threshold_R', 'regime_of_validity', 'supporting_python_proof', 'synthetic_separation_sigma']`
- Anchor fields only in v5_3: `['converges_with']`

---

## Anchors only in v5.13 (24)

Likely federation-tenancy / qbp-architecture-stream additions. Each needs a decision: import into unified vNext, or drop as federation-only.

| Anchor ID | Name (truncated) | Tier | Provenance |
|---|---|---|---|
| `FLAG-tov-eos-shape-underdetermined` | TOV integration with QBP-only EOS inputs gives M_max = 3.3 M… | 2 | I |
| `INSIGHT-cross-platform-per-feature-class` | Cross-platform Γ-test works within feature class, not across… | 3 | I |
| `INSIGHT-eos-integration-shifts-tov-by-30pct` | Robust QBP TOV prediction: M_TOV ∈ [2.6, 2.8] M_☉ from algeb… | 2 | I |
| `INSIGHT-gamma-needs-cross-platform` | Γ-universality test needs cross-platform pooling for multi-σ… | 3 | I |
| `META-physical-mapping-status-field` | CTH schema extension: physical_mapping_status field on PRED-… | 4 | P |
| `META-regime-of-validity-field` | CTH schema extension: regime_of_validity field | 4 | P |
| `OBS-btfr-z-range-validity` | BTFR (1+z) correction supported at 1<z<10, possibly breaks a… | 2 | E |
| `OBS-jades-gs-z14-0-vrot-lower-100` | JADES-GS-z14-0 ALMA tentative rotation: v_rot > 100 km/s (Sc… | 2 | E |
| `OPEN-Q-parent-bh-retardation-derivation` | Open: rigorous derivation of parent-BH retardation kernel | 3 | T |
| `PRED-a0-redshift-linear` | a₀(z) = a₀(today)·(1+z) from M(a) = M₀·a | 3 | T |
| `PRED-a0-saturating-Fmax-7` | Matter-era a₀(z) saturates with F_max = dim(Im 𝕆) = 7 | 1 | T+L |
| `PRED-a0-saturating-matter-era` | a₀(z) saturates at high z due to matter-era parent-BH dynami… | 2 | I |
| `PRED-a0-saturation-factor-fano` | Matter-era a₀(z) saturation factor F_max = dim(Im 𝕆) = 7 | 2 | I |
| `PRED-btfr-mass-correction` | BTFR mass-inference correction at high z: M_b(z) = M_b(0)/(1… | 3 | T |
| `PRED-hypergraph-cmb-camb-rerun` | Branch A CMB matches Planck under hypergraph (multi-party) b… | 3 | T |
| `PRED-jwst-kinematics-z14` | JWST/ALMA z>10 IFU rotation curves: v_rot 25-30% lower than … | 2 | I |
| `PRED-tov-mass-at-bump-peak` | M(NS with ρ_c at algebraic bump peak) = 2.20 M_☉ | 2 | I |
| `PROOF-alpha-particle-quaternion` | α-particle (⁴He) mass number = dim ℍ = 4 | 1 | T |
| `PROOF-fano-choice-information` | Fano line selection requires exactly ln 7 nats | 1 | T |
| `PROOF-iron-56-double-octet` | Iron-56 mass number = dim(Im 𝕆) × dim 𝕆 = 7 × 8 | 1 | T |
| `PROOF-iron-to-ns-bridge` | Iron-56 → neutron-star mass bridge through dim(Im 𝕆) = 7 | 1 | T |
| `PROOF-oxygen-16-sedenion` | O-16 mass number = (dim ℍ)² = dim 𝕊 = 16 | 1 | T |
| `PROOF-seed-mass-from-ln7` | Seed mass M_seed = sqrt(ln 7 · ℏc / 4πG) | 1 | T |
| `PROOF-silicon-28-fano-ladder` | Si-28 mass number = dim(Im 𝕆) × dim ℍ = 7 × 4 | 1 | T |

## Anchors only in v5_3 (15)

Likely Session-13 / QBP-web-stream additions (including the canonical Session-13 closeout: KILLED-f4-info-theoretic-justification, CONV-cd-tower-in-zeta-moments, CONV-spectral-entropy-zeta).

| Anchor ID | Name (truncated) | Tier | Provenance |
|---|---|---|---|
| `COMP-sm-non-unification-at-1loop` | SM gauge couplings do NOT unify at 1-loop: spectral action u… | 1 | I |
| `CONV-cd-tower-in-zeta-moments` | MATHEMATICS: Even-level Cayley-Dickson tower (dim Im H, S, c… | 4 | T |
| `CONV-spectral-entropy-zeta` | MATHEMATICS: Chamseddine-Connes-van Suijlekom 2018 derives u… | 4 | T |
| `INSIGHT-bcc-iron-fano-cube` | BCC iron coordination 8 = dim(𝕆): Fano cube geometry in the … | 4 | T |
| `INSIGHT-fano-cube-universal-compute-cell` | Fano cube as universal compute cell: Locale, BMA, holographi… | 2 | T |
| `KILLED-f4-info-theoretic-justification` | KILLED: 'f_4 = 0 follows from Axiom 1 (information preserved… | 3 | T |
| `OBS-nist-big-G-2026` | NIST G measurement: 6.67387×10⁻¹¹, 0.0235% below BIPM, compo… | 2 | E |
| `PRED-cutoff-scale-0p04-Planck` | Crystallisation cutoff Λ ≈ 0.04 M_Pl ≈ 5×10¹⁷ GeV from f₂ = … | 1 | I |
| `PRED-f4-zero-vacuum-energy` | Spectral action vacuum energy f₄ = 0: information-theoretic … | 1 | T |
| `PRED-inv-alpha-GUT-16pi` | 1/α_GUT ≈ 16π = 50.3: candidate algebraic expression (2.9% f… | 2 | T |
| `PRED-profile-function-f0-f2-ratio` | Profile function f₀/f₂ = 1/dim(Im ℍ) = 1/3: gravity-gauge ra… | 1 | T |
| `PROOF-beta-function-3-times-7` | SU(3) β-function numerator 21 = dim(Im ℍ) × dim(Im 𝕆) = 3×7:… | 1 | T |
| `Q28-alpha-GUT-from-stabiliser` | Q28: Is α_GUT = 1/(|Stab|+1) = 1/25? The missing link for de… | 2 | T |
| `WISDOM-003-there-is-only-f-u` | W-003: Forces are moments of a spectrum. The spectrum is the… | 1 | T |
| `WISDOM-schema-vs-instance` | WISDOM: The algebra is the schema, the boundary is the insta… | 1 | T |

---

## In-both anchors with differences (detail)

49 of 126 in-both anchors have at least one differing field.

### TWO_AXIS (19)

| Anchor ID | Differing fields | Sample v5.13 | Sample v5_3 |
|---|---|---|---|
| `INSIGHT-iron-handoff-nuclear-to-magnetic` | `lean_companion_theorems`, `lean_theorem`, `notes`, `proof_file`, `proof_system`, `sorry_count` | ['iron_56_g2_alpha_ladder', 'iron_56_is_… | <MISSING> |
| `INSIGHT-urca-threshold-dim-O` | `last_tested_at`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-27T00:00:00Z |
| `PRED-TOV-limit-sqrt-7-over-3` | `integration_test_status`, `last_tested_at`, `lean_companion_theorems`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_diagnosis`, `physical_mapping_status`, `physical_mapping_type`, `proof_file`, `proof_system`, `regime_of_validity`, `sorry_count` | verified-as-regime-specific | <MISSING> |
| `PRED-chiral-restoration-3rho0` | `last_tested_at`, `lean_companion_theorems`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-27T00:00:00Z |
| `PRED-ckm-cp-phase-arctan-sqrt7` | `last_tested_at`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-14T00:00:00Z |
| `PRED-conformal-sound-speed-1-over-3` | `last_tested_at`, `lean_theorem`, `notes`, `physical_mapping_status`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-27T00:00:00Z |
| `PRED-eta-prime-mass-shift-1-over-24` | `last_tested_at`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-27T00:00:00Z |
| `PRED-gamma-universality` | `analysis_pipeline`, `integration_test_status`, `last_tested_at`, `notes`, `null_threshold_R`, `physical_mapping_type`, `qbp_threshold_R` | reviews/nanorotor_gamma_test_synthetic.p… | <MISSING> |
| `PRED-holographic-boundary-gravity` | `integration_test_status`, `last_tested_at`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | unverified | <MISSING> |
| `PRED-koide-phase-2-over-9` | `last_tested_at`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-14T00:00:00Z |
| `PRED-lambda-as-cross-term` | `integration_test_status`, `last_tested_at`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | unverified | <MISSING> |
| `PRED-magnetar-energy-fraction-1-over-3` | `integration_test_status`, `last_tested_at`, `lean_companion_theorems`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `regime_of_validity`, `sorry_count`, `status` | verified-as-upper-bound | <MISSING> |
| `PRED-peak-sound-speed-Q` | `last_tested_at`, `lean_companion_theorems`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count`, `status` | 2026-04-30T00:00:00Z | 2026-04-27T00:00:00Z |
| `PRED-revival-exact` | `integration_test_status`, `last_tested_at`, `notes`, `physical_mapping_type`, `predicted_unit`, `predicted_value`, `proof_results` | unverified | <MISSING> |
| `PRED-urca-onset-3rho0` | `last_tested_at`, `lean_companion_theorems`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-27T00:00:00Z |
| `PRED-wolfenstein-A-sqrt-Q` | `last_tested_at`, `lean_scope`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | 2026-04-30T00:00:00Z | 2026-04-14T00:00:00Z |
| `PROOF-M-proportional-to-a` | `integration_test_status`, `last_tested_at`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | verified | <MISSING> |
| `PROOF-cl6` | `lean_companion_theorems`, `lean_migration_remaining`, `lean_migration_scope`, `lean_migration_status`, `lean_migration_target_file`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_results`, `python_caveats`, `supporting_python_proof` | ['charge_zero', 'charge_one_third', 'cha… | <MISSING> |
| `PROOF-interpolation-function-derived` | `integration_test_status`, `last_tested_at`, `lean_theorem`, `notes`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | unverified | <MISSING> |

### SCHEMA_AXIS (23)

| Anchor ID | Differing fields | Sample v5.13 | Sample v5_3 |
|---|---|---|---|
| `INST-ckm` | `lean_migration_status`, `physical_mapping_type`, `proof_file`, `proof_note`, `proof_results`, `proof_system` | planned | <MISSING> |
| `MEAS-mult-threshold` | `lean_migration_status`, `proof_file`, `proof_note`, `proof_system` | planned | <MISSING> |
| `OBS-cmb-314` | `lean_migration_status`, `proof_file`, `proof_note`, `proof_system` | planned | <MISSING> |
| `PRED-no-dm-particle` | `integration_test_status`, `lean_migration_status`, `physical_mapping_type`, `proof_file`, `proof_note`, `proof_results`, `proof_system` | unverified | <MISSING> |
| `PROOF-3gen` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file` | ['dimImH_eq_3'] | <MISSING> |
| `PROOF-42zd` | `lean_theorem`, `physical_mapping_type`, `proof_file` | zero_divisor_count_42 | <MISSING> |
| `PROOF-bond-complete` | `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | bond_completeness | <MISSING> |
| `PROOF-c2zt-square` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['c2z_square_minus_one', 'c2z_reverses_m… | <MISSING> |
| `PROOF-clifford-majorana` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['clifford_collapse_to_quaternion'] | <MISSING> |
| `PROOF-eigenratios` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file` | ['casimir_identification'] | <MISSING> |
| `PROOF-fano` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file` | ['fano_line_closure', 'fano_anticommutat… | <MISSING> |
| `PROOF-helicity-obstruction` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['moire_fragile_topology'] | <MISSING> |
| `PROOF-hessian` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file` | ['hessian_trace_128_universal', 'hessian… | <MISSING> |
| `PROOF-hurwitz-quat` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['hurwitz_fails_sedenion'] | <MISSING> |
| `PROOF-kramers` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['time_reversal_square_minus_one', 'kram… | <MISSING> |
| `PROOF-majorana-charge` | `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | majorana_central_charge | <MISSING> |
| `PROOF-nonabelian-braid` | `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | non_abelian_braiding | <MISSING> |
| `PROOF-plaquette-z2` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['flux_squared_identity', 'triple_produc… | <MISSING> |
| `PROOF-quat-closure` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['quaternion_table', 'eigenspace_gauge_m… | <MISSING> |
| `PROOF-shells` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file` | ['subshell_counts', 'noble_gas_atomic_nu… | <MISSING> |
| `PROOF-su2-lie` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['su2_casimir'] | <MISSING> |
| `PROOF-z2-cover` | `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | double_cover_z2 | <MISSING> |
| `PROOF-z3-cyclic` | `lean_companion_theorems`, `lean_theorem`, `physical_mapping_type`, `proof_file`, `proof_system`, `sorry_count` | ['honeycomb_chirality', 'graphene_z3z2'] | <MISSING> |

### UNCLASSIFIABLE (7)

| Anchor ID | Differing fields | Sample v5.13 | Sample v5_3 |
|---|---|---|---|
| `PRED-H-equals-Mdot-over-M` | `integration_test_status`, `physical_mapping_type` | unverified | <MISSING> |
| `PRED-born-exact` | `integration_test_status`, `physical_mapping_type` | unverified | <MISSING> |
| `PRED-correlated-alpha-G` | `integration_test_status`, `physical_mapping_type` | unverified | <MISSING> |
| `PRED-cosmic-birefringence` | `integration_test_status`, `physical_mapping_type` | unverified | <MISSING> |
| `PRED-no-gup` | `integration_test_status`, `physical_mapping_type` | unverified | <MISSING> |
| `PRED-w-not-minus-1` | `integration_test_status`, `physical_mapping_type` | unverified | <MISSING> |
| `PROOF-hurwitz` | `physical_mapping_type` | type_1_direct | <MISSING> |

---

## Cycle 1 conclusion

Structural delta surfaced; classification table seeded. Cycle 2 will produce per-anchor merge proposals for THEORY_AXIS + TWO_AXIS entries, routed to @qbp-oppenheimer adjudication. SCHEMA_AXIS entries route to @cth-implementor for schema-level merge decisions. NOT_CONFLICT entries auto-fold into vNext.

## Provenance

- Script: `scripts/cth_inventory_diff.py`
- Input: `archive/confluent-trust-inventory-v5.13.json` (267472 bytes)
- Input: `archive/confluent-trust-inventory-v5_3.json` (231104 bytes)
- Routing rubric: `docs/workflows/pr7_conflict_routing_rubric.md` (PR #416)
