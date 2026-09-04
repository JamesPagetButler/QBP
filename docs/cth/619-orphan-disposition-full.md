# #619 — Full Per-Theorem Disposition Table

Exhaustive per-theorem record for the #619 scope: **748 theorems** across 43 modules — **238 anchored** (→ ledger anchor id), **510 auxiliary** (→ stated reason). Generated from the source theorem enumeration cross-referenced against the CTH ledger (`lean_theorem` + `lean_companion_theorems` + `theorems[]`). Companion to `619-orphan-disposition.md`. No silent skips: every declaration below carries a disposition.

> Auxiliary reasons are category-level per module (the adjudicated role of that file's support lemmas). The load-bearing deliverables and their witnesses are named individually via their anchor id.


### `AngleDependent.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `angle_consistent_with_stern_gerlach` | aux | well-formedness supporting DERIV-angle-dependent-qbp |
| `expectation_angle` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_down_angle` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_down_angle_sin_sq` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_up_angle` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_up_angle_cos_sq` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_up_theta_pi` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_up_theta_pi_div_two` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `prob_up_theta_zero` | 🟢 anchored | DERIV-angle-dependent-qbp |
| `psiAngle_is_pure` | aux | well-formedness supporting DERIV-angle-dependent-qbp |
| `psiAngle_is_unit` | aux | well-formedness supporting DERIV-angle-dependent-qbp |
| `spinZObservable_is_pure` | aux | well-formedness supporting DERIV-angle-dependent-qbp |

### `Artin.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `L5` | aux | Artin-theorem restatement/support for PROOF-artin-theorem |
| `octonion_artin` | 🟢 anchored | PROOF-artin-theorem |
| `octonion_artin_assoc` | 🟢 anchored | PROOF-artin-theorem |
| `octonion_artin_gen` | 🟢 anchored | PROOF-artin-theorem |

### `ArtinCore.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `assoc_gen4_inner_one` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_gen4_inner_x` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_gen4_inner_xy` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_gen4_inner_y` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_gen4_zero` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_one_left` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_one_mid` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_one_right` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_span4` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_vanishes_on_span4` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_x_xy_y` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_xy_survivor` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_xy_x_y` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_xy_y_x` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_y_xy_x` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `assoc_yx_survivor` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |
| `trilinear_vanish_on_span` | aux | Artin-theorem core lemma (self-labeled "does NOT prove Artin"); supports octonion_artin |

### `ArtinSpan.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `L4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `adjoin_pair_le_span4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `bilinear_mem_span` | aux | Artin-theorem span lemma; supports octonion_artin |
| `cdAlg_mul_zero` | aux | Artin-theorem span lemma; supports octonion_artin |
| `cdAlg_zero_mul` | aux | Artin-theorem span lemma; supports octonion_artin |
| `gen4_mul_mem_span` | aux | Artin-theorem span lemma; supports octonion_artin |
| `mem_span4Subalgebra` | aux | Artin-theorem span lemma; supports octonion_artin |
| `mem_span4_of_mem_adjoin` | aux | Artin-theorem span lemma; supports octonion_artin |
| `one_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `span4_mul_closed` | aux | Artin-theorem span lemma; supports octonion_artin |
| `x_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `x_xy_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `xx_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `xy_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `xy_x_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `xy_y_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `xyxy_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `y_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `y_xy_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `yx_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |
| `yy_mem_span_gen4` | aux | Artin-theorem span lemma; supports octonion_artin |

### `ArtinTrace.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `L3` | aux | Artin-theorem trace lemma; supports octonion_artin |
| `N_add` | aux | Artin-theorem trace lemma; supports octonion_artin |
| `cdAlg_mul_add_swap` | aux | Artin-theorem trace lemma; supports octonion_artin |
| `cdAlg_mul_add_swap_pure` | aux | Artin-theorem trace lemma; supports octonion_artin |
| `mul_self_add` | aux | Artin-theorem trace lemma; supports octonion_artin |
| `reCoord_add` | aux | Artin-theorem trace lemma; supports octonion_artin |

### `Basic.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `expectation_orthogonal_is_zero` | 🟢 anchored | DERIV-measurement-ansatz-basic |
| `prob_up_orthogonal_is_half` | 🟢 anchored | DERIV-measurement-ansatz-basic |
| `pure_has_zero_re` | aux | def restatement / constant well-formedness (rfl) |
| `spin_x_is_pure` | aux | def restatement / constant well-formedness (rfl) |
| `spin_y_is_pure` | aux | def restatement / constant well-formedness (rfl) |
| `spin_z_is_pure` | aux | def restatement / constant well-formedness (rfl) |

### `Bi2Se3.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `band_inversion_satisfied` | 🟢 anchored | DERIV-bi2se3-ti |
| `bi_screening_valid` | 🟢 anchored | DERIV-bi2se3-ti |
| `full_chain_consistent` | aux | bundle/well-formedness; model results anchored as DERIV-bi2se3-ti |
| `se_screening_valid` | 🟢 anchored | DERIV-bi2se3-ti |
| `slater_bi_correct` | 🟢 anchored | DERIV-bi2se3-ti |
| `slater_se_correct` | 🟢 anchored | DERIV-bi2se3-ti |

### `Breakdown.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_e_add_e` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `N_zdX` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `N_zdY` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `cdAlg_basis_not_associate` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `cdAlg_basis_not_commute` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `cdAlg_mul_coord_eq_prodCoeff` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `cdAlg_no_order` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `complex_no_linear_order` | 🟢 anchored | PROOF-ops-order-ladder |
| `e_imaginary_sq_eq_neg_one` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `no_linear_strict_order_of_sq_eq_neg_one` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `octonion_no_order` | 🟢 anchored | PROOF-ops-order-ladder |
| `octonion_not_associative` | 🟢 anchored | PROOF-ops-associativity-ladder |
| `octonion_not_commutative` | 🟢 anchored | PROOF-ops-commutativity-ladder |
| `prodIsZero_iff_cdAlg_mul_eq_zero` | 🟢 anchored | PROOF-42zd |
| `quaternion_no_linear_order` | 🟢 anchored | PROOF-ops-order-ladder |
| `quaternion_not_commutative` | 🟢 anchored | PROOF-ops-commutativity-ladder |
| `sedenion_basis_zero_divisor_plane_count_eq_42` | 🟢 anchored | PROOF-42zd |
| `sedenion_no_order` | 🟢 anchored | PROOF-ops-order-ladder |
| `sedenion_norm_not_multiplicative` | 🟢 anchored | PROOF-ops-norm-composition-ladder |
| `sedenion_not_alternative` | 🟢 anchored | PROOF-ops-alternativity-ladder |
| `sedenion_not_associative` | 🟢 anchored | PROOF-ops-associativity-ladder |
| `sedenion_not_commutative` | 🟢 anchored | PROOF-ops-commutativity-ladder |
| `sedenion_zero_divisors` | 🟢 anchored | PROOF-ops-division-ladder |
| `zdX_mul_zdY_eq_zero` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `zdX_ne_zero` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |
| `zdY_ne_zero` | aux | proof-engine / ZD-&-norm computation input for the operations-ladder anchors |

### `CDAlg.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_def` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `add_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `basis_expansion` | 🟢 anchored | PROOF-cd-product-formula |
| `cdAlg_sq_eq` | 🟢 anchored | PROOF-cd-product-formula |
| `conjSign_neg_of` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `conjSign_zero_of` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `conj_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `div_lt_two` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `div_zero_or_one` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `e_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `e_mul_e` | 🟢 anchored | PROOF-cd-product-formula |
| `eq_of_hi_lo` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `ext` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `lo_val` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `lt_two_pow_of_div_zero` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mod_eq_self_of_div_zero` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mulCoeff_antisymm` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mulCoeff_four_eq_sgnTable` | 🟢 anchored | PROOF-cd-structure-constant-tables |
| `mulCoeff_props` | 🟢 anchored | PROOF-cd-product-formula |
| `mulCoeff_self` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mulCoeff_three_eq_fano` | 🟢 anchored | PROOF-cd-structure-constant-tables |
| `mulCoeff_zero_left` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mulCoeff_zero_right` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mul_add_left` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mul_add_right` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mul_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mul_coord_single` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mul_smul_left` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `mul_smul_right` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `neg_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `one_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `one_def` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `smul_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `sub_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `sum_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `val_eq_zero_iff` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `xor_eq_iff` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `xor_left_injective` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `xor_self_eq` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `xor_xor_cancel` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `xor_zero_left` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `xor_zero_right` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `zero_coord` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |
| `zero_mk_eq` | aux | coordinate/simp/instance plumbing for the CD product-formula & structure-constant anchors |

### `CDBridge.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `cdAlg2EquivQuaternion_basis` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `cdAlg_mul_one` | 🟢 anchored | PROOF-cd-associativity-level2 |
| `cdAlg_one_mul` | 🟢 anchored | PROOF-cd-associativity-level2 |
| `cdAlg_two_assoc` | 🟢 anchored | PROOF-cd-associativity-level2 |
| `cdAlg_two_assocCoeffZ_zero` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `cdAlg_two_assoc_basis` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `e_mul_one` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `mul_isBilinear` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `ofQuat_toQuat` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `one_mul_e` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `quat_smul_mul_smul` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `rather` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_add` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_e0` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_e1` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_e2` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_e3` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_mul` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_mul_basis` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_ofQuat` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_one` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_smul` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |
| `toQuat_sum` | aux | toQuat bridge machinery for PROOF-cd-associativity-level2 |

### `CDDimension.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `card_im_index` | aux | auxiliary supporting lemma |
| `cdBasis_eq_e` | aux | auxiliary supporting lemma |
| `e_im_linearIndependent` | aux | auxiliary supporting lemma |
| `e_linearIndependent` | aux | auxiliary supporting lemma |
| `even_tower_imDim` | 🟢 anchored | PROOF-cd-algebra-finrank-2n |
| `finrank_cdAlg` | 🟢 anchored | PROOF-cd-algebra-finrank-2n |
| `finrank_imSubmodule` | 🟢 anchored | PROOF-cd-algebra-finrank-2n |
| `imDim_level_six` | aux | auxiliary supporting lemma |
| `imDim_quaternion` | aux | auxiliary supporting lemma |
| `imDim_sedenion` | aux | auxiliary supporting lemma |

### `CDLifting.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `IsBilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsBilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsQuadrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsQuadrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsQuadrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsQuadrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsTrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsTrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `IsTrilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `assoc_diag_left` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `assoc_diag_right` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `assoc_e` | 🟢 anchored | PROOF-cd-associator-formula |
| `assoc_trilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `laMap_trilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `lift_bilinear_eq` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `lift_quadrilinear_eq` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `lift_trilinear_eq` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `octonion_alternative` | 🟢 anchored | PROOF-ops-alternativity-ladder |
| `octonion_assocCoeffZ_left_alt` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `octonion_assocCoeffZ_right_alt` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `octonion_laMap_basis` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `octonion_left_alternative_polarized` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `octonion_raMap_basis` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `octonion_right_alternative_polarized` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `raMap_trilinear` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `sed_assocCoeffZ_witness` | aux | CD multilinear-lifting plumbing (lift-family = VML candidate #594) |
| `sedenion_not_alternative` | 🟢 anchored | PROOF-ops-alternativity-ladder |

### `CPPhase.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `cos_sq_delta_CP` | 🟢 anchored | PRED-ckm-cp-phase-arctan-sqrt7 |
| `sin_sq_add_cos_sq_delta_CP` | aux | auxiliary supporting lemma |
| `sin_sq_delta_CP` | 🟢 anchored | PRED-ckm-cp-phase-arctan-sqrt7 |
| `tan_delta_CP` | 🟢 anchored | PRED-ckm-cp-phase-arctan-sqrt7 |
| `tan_sq_delta_CP` | aux | auxiliary supporting lemma |

### `Constants.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `eV_in_J_pos` | 🟢 anchored | DERIV-code-si-constants |
| `e_SI_pos` | 🟢 anchored | DERIV-code-si-constants |
| `h_SI_pos` | 🟢 anchored | DERIV-code-si-constants |
| `hbar_SI_pos` | 🟢 anchored | DERIV-code-si-constants |
| `hbar_code_pos` | 🟢 anchored | DERIV-code-si-constants |
| `k0_code_pos` | 🟢 anchored | DERIV-code-si-constants |
| `m_code_pos` | 🟢 anchored | DERIV-code-si-constants |
| `v_z_code_eq_40` | 🟢 anchored | DERIV-code-si-constants |
| `v_z_code_pos` | 🟢 anchored | DERIV-code-si-constants |

### `CrossProduct.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_add` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `N_smul` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `N_sub` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `bil_eq_coord0_mul_conj` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `bil_sub_left` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `bil_sub_right` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `cdAlg2_normMap_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `cdAlg2_norm_composition` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `cdAlg_polar_sq` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `commutator_orth_octonion` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `commutator_orth_quaternion` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `commutator_reCoord_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `crossOrthMap_e` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `crossOrthMap_trilinear` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `crossOrth_scalar_octonion` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `crossOrth_scalar_quaternion` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `cross_antisymm` | 🟢 anchored | PROOF-octonion-cross-product |
| `cross_def` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `cross_reCoord_zero` | 🟢 anchored | PROOF-octonion-cross-product |
| `cross_self` | 🟢 anchored | PROOF-octonion-cross-product |
| `no_sedenion_composition_for_cross` | 🟢 anchored | PROOF-octonion-cross-product |
| `normMap2_basis` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `normMap_e2` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `octonion_crossOrthCoeffZ_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `octonion_crossOrthMap_basis` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `octonion_crossOrthMap_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `octonion_cross_norm_identity` | 🟢 anchored | PROOF-octonion-cross-product |
| `octonion_cross_orthogonal_left` | 🟢 anchored | PROOF-octonion-cross-product |
| `octonion_cross_orthogonal_right` | 🟢 anchored | PROOF-octonion-cross-product |
| `quaternion_crossOrthCoeffZ_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `quaternion_crossOrthMap_basis` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `quaternion_crossOrthMap_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `quaternion_cross_norm_identity` | 🟢 anchored | PROOF-octonion-cross-product |
| `quaternion_cross_orthogonal_left` | 🟢 anchored | PROOF-octonion-cross-product |
| `quaternion_cross_orthogonal_right` | 🟢 anchored | PROOF-octonion-cross-product |
| `quaternion_normCoeffZ_zero` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |
| `reCoord_mul_pure` | aux | bilinear/trilinear map scaffolding for PROOF-octonion-cross-product |

### `Crystallisation.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `convergence_ordering` | 🟢 anchored | DERIV-crystallisation-spectral-moments |
| `growth_enhancement` | 🟢 anchored | DERIV-crystallisation-spectral-moments |
| `half_ratio_universal` | aux | numerology/well-formedness; model results anchored as DERIV-crystallisation-spectral-moments |
| `moment_scaling_hierarchy` | 🟢 anchored | DERIV-crystallisation-spectral-moments |
| `three_moments_dim_imH` | aux | numerology/well-formedness; model results anchored as DERIV-crystallisation-spectral-moments |
| `variation_correlation` | 🟢 anchored | DERIV-crystallisation-spectral-moments |

### `DoubleSlit.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `coeComplex_isComplex` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `complex_mul_j` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `coupling_cancellation` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `coupling_cancellation_inner` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `coupling_decomposition` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `coupling_decomposition_real` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `coupling_decouples_U1_zero` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `decayConstant_mono_U1` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `decayConstant_pos` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `decayLength_pos` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `j_complex_j` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `j_mul_complex` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `normSq_sympForm` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `normSq_sympForm_nonneg` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `normSq_sympForm_zero_psi1` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `qJ_sq` | 🟢 anchored | PROOF-doubleslit-quaternion-algebra |
| `quatFraction_le_one` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `quatFraction_nonneg` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `quatFraction_zero_iff` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `scenarioA_visibility` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `scenarioB_visibility` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `scenarioC_matches_scenarioA_at_detector` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `sympForm_zero_psi1` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `visibility_antitone_background` | 🟢 anchored | DERIV-doubleslit-visibility-model |
| `visibility_correlated` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `visibility_eq_one_sub_quatFraction` | 🟢 anchored | DERIV-doubleslit-visibility-model |
| `visibility_eta_zero` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `visibility_full_when_eta_zero` | aux | setup/well-formedness for the double-slit proof/derivation anchors |
| `visibility_le_one` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `visibility_nonneg` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `visibility_one` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |
| `visibility_zero` | 🟢 anchored | PROOF-doubleslit-visibility-bounds |

### `Elements.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `algebraic_chain_to_atoms` | aux | auxiliary supporting lemma |
| `cabibbo_fano_match` | aux | auxiliary supporting lemma |
| `dimImH_eq_3` | aux | auxiliary supporting lemma |
| `generation_count` | aux | auxiliary supporting lemma |
| `hydrogen_energy_ratios` | aux | auxiliary supporting lemma |
| `koide_ratio_two_thirds` | aux | auxiliary supporting lemma |
| `noble_gas_atomic_numbers` | aux | auxiliary supporting lemma |
| `periodic_table_structure` | aux | auxiliary supporting lemma |
| `quantum_number_structure` | aux | auxiliary supporting lemma |
| `shell_capacity_formula` | 🟢 anchored | PROOF-shells |
| `spin_half_states` | aux | auxiliary supporting lemma |
| `subshell_counts` | aux | auxiliary supporting lemma |

### `Exp.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_eq_re_sq_add_N_imPart` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `N_eq_zero_iff` | 🟢 anchored | PROOF-norm-form-bilinear |
| `N_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `N_nonneg` | 🟢 anchored | PROOF-norm-form-bilinear |
| `N_smul` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cdAlg2Equiv_imI` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cdAlg2Equiv_imJ` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cdAlg2Equiv_imK` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cdAlg2Equiv_imNorm` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cdAlg2Equiv_imPart` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cdAlg2Equiv_re` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `cos_abs` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_def` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_eq_quaternion` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `exp_eq_re_add_imag` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_log` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `exp_neg_mul_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `exp_of_re_zero` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_re_smul_one` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_smul_add` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_smul_add_real` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `exp_unit_axis` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_unit_axis_add` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_unit_axis_add_real` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `exp_unit_axis_real` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `exp_zero` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imNorm_eq_zero_iff` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imNorm_neg` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imNorm_nonneg` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imNorm_sq` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_coord` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_exp` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_imPart` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_mul_imPart` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_neg` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_of_re_zero` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_real_add_imag` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imPart_smul` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `imag_mul_self` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `log_def` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `log_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `octonion_N_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `octonion_exp_log` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `octonion_exp_neg_mul_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `octonion_exp_smul_add` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `octonion_exp_smul_add_real` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `octonion_log_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `re_def` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `re_exp` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `re_imPart` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `re_neg` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `re_real_add_imag` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `re_smul` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `re_smul_one_add_imPart` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `rotor_mul` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `sedenion_N_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `sedenion_exp_log` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `sedenion_exp_neg_mul_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `sedenion_exp_smul_add` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `sedenion_exp_smul_add_real` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `sedenion_log_exp` | 🟢 anchored | PROOF-octonion-sedenion-exp-log |
| `sinc_abs_mul_self` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `sinc_mul_self` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `span_mul` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |
| `unit_span_mul` | aux | coordinate/norm/sinc/definitional plumbing for PROOF-octonion-sedenion-exp-log |

### `FanoGenesis.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `aut_fano_168` | aux | auxiliary supporting lemma |
| `aut_transitive_on_lines` | aux | auxiliary supporting lemma |
| `every_point_on_three_lines` | aux | auxiliary supporting lemma |
| `fano_anticommutative` | 🟢 anchored | PROOF-fano-genesis |
| `fano_associative` | aux | auxiliary supporting lemma |
| `fano_line_closure` | aux | auxiliary supporting lemma |
| `fano_line_positive` | aux | auxiliary supporting lemma |
| `fano_lines_count` | aux | auxiliary supporting lemma |
| `fano_lines_wellformed` | aux | auxiliary supporting lemma |
| `g2_decomposition_14_8_3_3` | aux | auxiliary supporting lemma |
| `identity_element` | aux | auxiliary supporting lemma |
| `imaginary_units_square_neg_one` | 🟢 anchored | PROOF-fano-genesis |
| `insert_pos_unique` | aux | auxiliary supporting lemma |
| `lines_units_consistent` | 🟢 anchored | PROOF-fano-genesis |
| `mem_insertAll` | aux | auxiliary supporting lemma |
| `mem_permsOf` | aux | auxiliary supporting lemma |
| `nodup_insertAll` | aux | auxiliary supporting lemma |
| `nodup_permsOf` | aux | auxiliary supporting lemma |
| `octonion_non_associative` | 🟢 anchored | PROOF-fano-genesis |
| `orbit_stabiliser_bookkeeping` | aux | auxiliary supporting lemma |
| `perm_of_mem_insertAll` | aux | auxiliary supporting lemma |
| `perms7_complete` | aux | auxiliary supporting lemma |
| `perms7_length` | aux | auxiliary supporting lemma |
| `perms7_nodup` | aux | auxiliary supporting lemma |
| `stabWitness_works` | aux | auxiliary supporting lemma |
| `stabiliser_order_24` | aux | auxiliary supporting lemma |
| `stabiliser_transitive` | aux | auxiliary supporting lemma |
| `transWitness_works` | aux | auxiliary supporting lemma |
| `two_points_unique_line` | aux | auxiliary supporting lemma |

### `FanoOrientationF3.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `archiveTable_disagrees_cd` | 🟢 anchored | PROOF-cd-structure-constant-tables |
| `cayleyDickson8_alternative_on_basis` | 🟢 anchored | PROOF-cd-structure-constant-tables |
| `cayleyDickson8_sq_neg_one` | 🟢 anchored | PROOF-cd-structure-constant-tables |
| `fanoTableF4_eq_cayleyDickson` | 🟢 anchored | PROOF-cd-structure-constant-tables |
| `fanoTriple_oriented_123` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriple_oriented_145` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriple_oriented_167` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriple_oriented_246` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriple_oriented_257` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriple_oriented_347` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriple_oriented_356` | aux | bundled fanoTriple member (bundle fanoTriples_oriented is anchored) or well-formedness |
| `fanoTriples_oriented` | 🟢 anchored | PROOF-cd-structure-constant-tables |

### `FanoSubalgebras.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `auto123_spec` | aux | auxiliary supporting lemma |
| `auto145_spec` | aux | auxiliary supporting lemma |
| `auto167_spec` | aux | auxiliary supporting lemma |
| `auto246_spec` | aux | auxiliary supporting lemma |
| `auto257_spec` | aux | auxiliary supporting lemma |
| `auto347_spec` | aux | auxiliary supporting lemma |
| `auto356_spec` | aux | auxiliary supporting lemma |
| `autoWitnesses_act` | aux | auxiliary supporting lemma |
| `autoWitnesses_isAuto` | aux | auxiliary supporting lemma |
| `autoWitnesses_targets_eq_fano` | aux | auxiliary supporting lemma |
| `basisAuto_transitive_on_triples` | aux | auxiliary supporting lemma |
| `exists_imaginary_triple_nonassociative` | aux | auxiliary supporting lemma |
| `fanoTriple_associative` | aux | auxiliary supporting lemma |
| `fanoTriple_xor_closed` | aux | auxiliary supporting lemma |
| `fanoTriples_card` | aux | auxiliary supporting lemma |
| `fanoTriples_eq` | aux | auxiliary supporting lemma |
| `here` | aux | auxiliary supporting lemma |

### `Fraunhofer.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `fraunhoferIntensityFull_at_zero` | aux | setup/well-formedness for DERIV-fraunhofer-optics |
| `fraunhoferIntensityFull_factor` | 🟢 anchored | DERIV-fraunhofer-optics |
| `fraunhoferIntensityFull_le` | 🟢 anchored | DERIV-fraunhofer-optics |
| `fraunhoferIntensityFull_nonneg` | 🟢 anchored | DERIV-fraunhofer-optics |
| `fraunhoferIntensityFull_slit_width_zero` | 🟢 anchored | DERIV-fraunhofer-optics |
| `fringeSpacing_inverse_d` | 🟢 anchored | DERIV-fraunhofer-optics |
| `fringeSpacing_linear_L` | 🟢 anchored | DERIV-fraunhofer-optics |
| `fringeSpacing_linear_lambda` | 🟢 anchored | DERIV-fraunhofer-optics |
| `intensity_at_maximum` | 🟢 anchored | DERIV-fraunhofer-optics |
| `intensity_at_minimum` | 🟢 anchored | DERIV-fraunhofer-optics |

### `G2Transitivity.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `cd_mul_sum` | aux | auxiliary supporting lemma |
| `cd_mul_zero` | aux | auxiliary supporting lemma |
| `cd_prod_expansion` | aux | auxiliary supporting lemma |
| `cd_smul_sum_mul_smul_sum` | aux | auxiliary supporting lemma |
| `cd_sum_mul` | aux | auxiliary supporting lemma |
| `cd_zero_mul` | aux | auxiliary supporting lemma |
| `g2_transitive_genuine_automorphisms` | 🟢 anchored | PROOF-g2 |
| `inducedMap_add` | aux | auxiliary supporting lemma |
| `inducedMap_bijective` | aux | auxiliary supporting lemma |
| `inducedMap_e` | aux | auxiliary supporting lemma |
| `inducedMap_expansion` | aux | auxiliary supporting lemma |
| `inducedMap_isAlgHom` | aux | auxiliary supporting lemma |
| `inducedMap_mul` | aux | auxiliary supporting lemma |
| `inducedMap_mul_basis` | aux | auxiliary supporting lemma |
| `inducedMap_one` | aux | auxiliary supporting lemma |
| `inducedMap_smul` | aux | auxiliary supporting lemma |
| `inducedMap_sum` | aux | auxiliary supporting lemma |
| `inducedMap_zero` | aux | auxiliary supporting lemma |
| `invMap_e_leftInv` | aux | auxiliary supporting lemma |
| `invMap_e_rightInv` | aux | auxiliary supporting lemma |
| `invMap_leftInverse` | aux | auxiliary supporting lemma |
| `invMap_rightInverse` | aux | auxiliary supporting lemma |
| `sgn_sq_one` | aux | auxiliary supporting lemma |

### `General3D.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `expectation_azimuthal_invariance` | 🟢 anchored | DERIV-general3d-qbp |
| `expectation_general` | 🟢 anchored | DERIV-general3d-qbp |
| `obsGeneral_is_pure` | aux | well-formedness supporting DERIV-general3d-qbp |
| `prob_up_antiz_on_z` | 🟢 anchored | DERIV-general3d-qbp |
| `prob_up_general` | 🟢 anchored | DERIV-general3d-qbp |
| `prob_up_same_direction` | 🟢 anchored | DERIV-general3d-qbp |
| `prob_up_x_on_z` | 🟢 anchored | DERIV-general3d-qbp |
| `prob_up_y_on_z` | 🟢 anchored | DERIV-general3d-qbp |
| `prob_up_z_on_z` | 🟢 anchored | DERIV-general3d-qbp |
| `psiGeneral_is_pure` | aux | well-formedness supporting DERIV-general3d-qbp |
| `psiGeneral_is_unit` | aux | well-formedness supporting DERIV-general3d-qbp |
| `psiGeneral_phi_zero` | aux | well-formedness supporting DERIV-general3d-qbp |

### `Graphene.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `alpha_near_inv_sqrt3` | 🟢 anchored | DERIV-graphene-model |
| `c2z_reverses_momentum` | 🟢 anchored | DERIV-graphene-model |
| `c2z_square_minus_one` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-graphene-model |
| `c2zt_square_plus_one` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-graphene-model |
| `dirac_helicity` | 🟢 anchored | DERIV-graphene-model |
| `graphene_z3z2` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-graphene-model |
| `honeycomb_chirality` | 🟢 anchored | DERIV-graphene-model |
| `honeycomb_z3_cyclic` | 🟢 anchored | DERIV-graphene-model |
| `moire_fragile_topology` | 🟢 anchored | DERIV-graphene-model |
| `mott_from_hessian` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-graphene-model |
| `protection_type_differs` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-graphene-model |

### `Hurwitz.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `complex_case` | aux | auxiliary supporting lemma |
| `octonion_dim_eight` | aux | auxiliary supporting lemma |
| `octonion_norm_multiplicative` | 🟢 anchored | PROOF-normed-division-tower-existence |
| `quaternion_case` | aux | auxiliary supporting lemma |
| `real_case` | aux | auxiliary supporting lemma |
| `sedenion_dim_sixteen` | aux | auxiliary supporting lemma |
| `sedenion_not_composition` | 🟢 anchored | PROOF-normed-division-tower-existence |
| `tower_dims_in_1248` | 🟢 anchored | PROOF-normed-division-tower-existence |

### `Kitaev.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `bond_completeness` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-kitaev-model |
| `cl_screening_correct` | 🟢 anchored | DERIV-kitaev-model |
| `clifford_anticommutation` | 🟢 anchored | DERIV-kitaev-model |
| `clifford_collapse_to_quaternion` | 🟢 anchored | DERIV-kitaev-model |
| `flux_squared_identity` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-kitaev-model |
| `full_kitaev_chain` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-kitaev-model |
| `jeff_half_filling` | 🟢 anchored | DERIV-kitaev-model |
| `majorana_central_charge` | aux | bundle/numerology/well-formedness; model results anchored as DERIV-kitaev-model |
| `non_abelian_braiding` | 🟢 anchored | DERIV-kitaev-model |
| `plaquette_flux_z2` | 🟢 anchored | DERIV-kitaev-model |
| `ru_screening_correct` | 🟢 anchored | DERIV-kitaev-model |
| `soc_regime_valid` | 🟢 anchored | DERIV-kitaev-model |
| `triple_product_all_orderings` | 🟢 anchored | DERIV-kitaev-model |

### `LeftMulDet.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_one` | aux | auxiliary supporting lemma |
| `mul_e_coord` | aux | auxiliary supporting lemma |
| `octDetPolyZ_eq` | aux | auxiliary supporting lemma |
| `octDetPoly_eq` | aux | auxiliary supporting lemma |
| `octDetPoly_sq` | aux | auxiliary supporting lemma |
| `octLeftMulPolyZ_eval` | aux | auxiliary supporting lemma |
| `octLeftMulPolyZ_map` | aux | auxiliary supporting lemma |
| `octLeftMulPoly_map_eval` | aux | auxiliary supporting lemma |
| `octNormPolyZ_eval` | aux | auxiliary supporting lemma |
| `octNormPolyZ_map` | aux | auxiliary supporting lemma |
| `octNormPoly_eval` | aux | auxiliary supporting lemma |
| `octonionLeftMul_apply` | aux | auxiliary supporting lemma |
| `octonionLeftMul_det` | 🟢 anchored | PROOF-octonion-zd-hypersurface-empty |
| `octonionLeftMul_det_comm` | 🟢 anchored | PROOF-octonion-zd-hypersurface-empty |
| `octonionLeftMul_det_eq_zero_iff` | 🟢 anchored | PROOF-octonion-zd-hypersurface-empty |
| `octonionLeftMul_det_rat` | aux | auxiliary supporting lemma |
| `octonionLeftMul_det_sq` | aux | auxiliary supporting lemma |
| `octonionLeftMul_mulVec` | aux | auxiliary supporting lemma |
| `octonionLeftMul_one` | aux | auxiliary supporting lemma |
| `octonionLeftMul_transpose_mul` | aux | auxiliary supporting lemma |
| `octonion_bil_comp` | aux | auxiliary supporting lemma |
| `unitCoord_mk` | aux | auxiliary supporting lemma |

### `LieAlgebraIso.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `bracket_qi_qj` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `bracket_qi_qk` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `bracket_qj_qi` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `bracket_qj_qk` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `bracket_qk_qi` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `bracket_qk_qj` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `bracket_self` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `imH_casimir` | 🟢 anchored | PROOF-su2-lie |
| `imH_structure_constants` | 🟢 anchored | PROOF-su2-lie |
| `qi_mul_qi` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qi_mul_qj` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qi_mul_qk` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qi_pure` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qj_mul_qi` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qj_mul_qj` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qj_mul_qk` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qj_pure` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qk_mul_qi` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qk_mul_qj` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qk_mul_qk` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |
| `qk_pure` | aux | Hamilton-table/antisymmetry constituent of the su2-lie bracket/Casimir witnesses |

### `NormForm.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_eq_zero_iff` | 🟢 anchored | PROOF-norm-form-bilinear |
| `N_nonneg` | 🟢 anchored | PROOF-norm-form-bilinear |
| `bil_eq_reCoord_mul_conj` | 🟢 anchored | PROOF-norm-form-bilinear |
| `bil_self_eq_zero_iff` | aux | dedup/corollary of PROOF-norm-form-bilinear |
| `bil_symm` | 🟢 anchored | PROOF-norm-form-bilinear |
| `norm_form_eq_bil_diag` | aux | dedup/corollary of PROOF-norm-form-bilinear |
| `octonion_bilinear_form` | 🟢 anchored | PROOF-norm-form-bilinear |
| `octonion_norm_form_composition` | 🟢 anchored | PROOF-norm-form-bilinear |
| `sedenion_bilinear_form` | 🟢 anchored | PROOF-norm-form-bilinear |
| `sedenion_norm_form_not_composition` | 🟢 anchored | PROOF-norm-form-bilinear |

### `Octonion32Count.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `all_sedenion_lines_associative` | 🟢 anchored | PROOF-octonion-32dim-alternative-count |
| `alternative_subspace_count_32_eq_fifty` | 🟢 anchored | PROOF-octonion-32dim-alternative-count |
| `base_copies_inside_sedenion` | aux | well-formedness/plumbing for PROOF-octonion-32dim-alternative-count |
| `base_copies_persist` | 🟢 anchored | PROOF-octonion-32dim-alternative-count |
| `base_plus_crossing_eq_fifty` | 🟢 anchored | PROOF-octonion-32dim-alternative-count |
| `crossingAlternativeCount_eq_predCount` | aux | well-formedness/plumbing for PROOF-octonion-32dim-alternative-count |
| `crossing_pass_iff_discriminator` | 🟢 anchored | PROOF-octonion-32dim-alternative-count |
| `forty_two_split` | 🟢 anchored | PROOF-octonion-32dim-alternative-count |
| `recompute` | aux | well-formedness/plumbing for PROOF-octonion-32dim-alternative-count |

### `OctonionLaws.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `N_eq_bil` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `assoc_diag_flex` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `bil_add_left` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `bil_add_right` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `bil_def` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `bil_e` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `bil_smul_left` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `bil_smul_right` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `e3_LL` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `e3_LR` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `e4_LLL` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `e4_LLRR` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `e4_LRLL` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `e4_RRR` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `flMap_trilinear` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mLeftMap_basis` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mLeftMap_e` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mLeftMap_quadrilinear` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mMidMap_basis` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mMidMap_e` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mMidMap_quadrilinear` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mRightMap_basis` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mRightMap_e` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mRightMap_quadrilinear` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mul_sub_left` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `mul_sub_right` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `normMap_basis` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `normMap_coord0` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `normMap_e` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `normMap_quadrilinear` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_assocCoeffZ_flex` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_flMap_basis` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_flexible` | 🟢 anchored | PROOF-ops-flexibility-ladder |
| `octonion_flexible_polarized` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_mLeftCoeffZ_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_mLeftMap_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_mMidCoeffZ_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_mMidMap_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_mRightCoeffZ_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_mRightMap_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_moufang_left` | 🟢 anchored | PROOF-octonion-moufang |
| `octonion_moufang_middle` | 🟢 anchored | PROOF-octonion-moufang |
| `octonion_moufang_right` | 🟢 anchored | PROOF-octonion-moufang |
| `octonion_normCoeffZ_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_normMap_zero` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `octonion_norm_composition` | 🟢 anchored | PROOF-ops-norm-composition-ladder |
| `octonion_power_associative` | 🟢 anchored | PROOF-power-associativity |
| `octonion_power_associative_4` | 🟢 anchored | PROOF-power-associativity |
| `sed_assoc_diag_flex` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `sedenion_assocCoeffZ_flex` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `sedenion_flMap_basis` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `sedenion_flexible` | 🟢 anchored | PROOF-ops-flexibility-ladder |
| `sedenion_flexible_polarized` | aux | multilinear-map proof machinery for Moufang / power-assoc / norm-composition |
| `sedenion_power_associative` | 🟢 anchored | PROOF-power-associativity |
| `sedenion_power_associative_4` | 🟢 anchored | PROOF-power-associativity |

### `QBPHorizonFoundations.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `accreting_horizon_spacelike` | 🟢 anchored | DERIV-vaidya-accreting-horizon-spacelike |
| `eta_s2_dirac_pair` | aux | auxiliary supporting lemma |
| `eta_symmetric_spectrum_zero` | 🟢 anchored | INSIGHT-s2-dirac-eta-vanishes |
| `evaporating_horizon_timelike` | 🟢 anchored | DERIV-vaidya-accreting-horizon-spacelike |
| `hubble_half_area` | 🟢 anchored | DERIV-hubble-half-entropy-factor |
| `hubble_half_entropy` | 🟢 anchored | DERIV-hubble-half-entropy-factor |
| `static_horizon_null` | 🟢 anchored | DERIV-vaidya-accreting-horizon-spacelike |
| `vaidya_horizon_normSq_eq` | 🟢 anchored | DERIV-vaidya-accreting-horizon-spacelike |

### `Quaternion.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `double_cover_z2` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `eigenspace_gauge_match` | 🟢 anchored | DERIV-quaternion-physics-kramers |
| `hurwitz_fails_sedenion` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `hurwitz_quaternion` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `kramers_degeneracy` | 🟢 anchored | DERIV-quaternion-physics-kramers |
| `kramers_orthogonality` | 🟢 anchored | DERIV-quaternion-physics-kramers |
| `quaternion_closure` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `quaternion_table` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `su2_casimir` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `su2_commutation` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |
| `time_reversal_square_minus_one` | aux | physical-identification support; see-also Foundations anchors / DERIV-quaternion-physics-kramers |

### `ScaleFactors.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `E0_pos` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `L0_pos` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `T0_def` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `T0_pos` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `energy_linear` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `energy_round_trip` | 🟢 anchored | PROOF-bpm-si-round-trip |
| `energy_scaling` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `energy_zero` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `k_si_pos` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `position_linear` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `position_round_trip` | 🟢 anchored | PROOF-bpm-si-round-trip |
| `position_scaling` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `position_zero` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |
| `v_z_si_pos` | aux | linearity/positivity sign-lemma supporting PROOF-bpm-si-round-trip |

### `Sedenion.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `anticommutation_105` | aux | auxiliary supporting lemma |
| `anticommuting_count` | aux | auxiliary supporting lemma |
| `casimir_identification` | aux | auxiliary supporting lemma |
| `coupling_ratios` | aux | auxiliary supporting lemma |
| `hessian_trace_128_universal` | aux | auxiliary supporting lemma |
| `identity_element` | aux | auxiliary supporting lemma |
| `imaginary_square_minus_one` | aux | auxiliary supporting lemma |
| `spectrum_unique` | aux | auxiliary supporting lemma |
| `zero_divisor_count_42` | 🟢 anchored | PROOF-42zd |

### `SedenionHessianTraceSq.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `hessian_traceSq_1152_universal` | 🟢 anchored | PROOF-hessian |

### `SedenionOctonionCount.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `alternative_fails` | 🟢 anchored | PROOF-sedenion-alternative-hyperplane-count |
| `alternative_hyperplane_count_eq_eight` | 🟢 anchored | PROOF-sedenion-alternative-hyperplane-count |
| `alternative_passes` | 🟢 anchored | PROOF-sedenion-alternative-hyperplane-count |
| `partition_8_7` | aux | consistency restatement supporting PROOF-sedenion-alternative-hyperplane-count |
| `zero_divisor_normal10` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |
| `zero_divisor_normal11` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |
| `zero_divisor_normal12` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |
| `zero_divisor_normal13` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |
| `zero_divisor_normal14` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |
| `zero_divisor_normal15` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |
| `zero_divisor_normal9` | 🟢 anchored | PROOF-sedenion-zero-divisor-witnesses |

### `SpectralMoments.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `ccvsGamma_one` | aux | auxiliary supporting lemma |
| `ccvsGamma_three` | aux | auxiliary supporting lemma |
| `ccvsGamma_two` | aux | auxiliary supporting lemma |
| `ccvsPrefactor_eq_imDim_mul` | aux | auxiliary supporting lemma |
| `ccvsPrefactor_one` | aux | auxiliary supporting lemma |
| `ccvsPrefactor_three` | aux | auxiliary supporting lemma |
| `ccvsPrefactor_two` | aux | auxiliary supporting lemma |
| `f0_invariant` | aux | auxiliary supporting lemma |
| `f2_scaling` | 🟢 anchored | PROOF-spectral-action-moment-scaling |
| `f4_scaling` | 🟢 anchored | PROOF-spectral-action-moment-scaling |
| `moment_scaling_ratio` | aux | auxiliary supporting lemma |
| `profileMoment_dilate` | 🟢 anchored | PROOF-spectral-action-moment-scaling |

### `SternGerlach.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `expectation_x_measured_z_is_zero` | 🟢 anchored | DERIV-sterngerlach-qbp |
| `prob_down_x_measured_z_is_half` | 🟢 anchored | DERIV-sterngerlach-qbp |
| `prob_up_x_measured_z_is_half` | 🟢 anchored | DERIV-sterngerlach-qbp |
| `spinXState_is_pure` | aux | well-formedness (is_pure/is_unit) supporting DERIV-sterngerlach-qbp |
| `spinZObservable_is_pure` | aux | well-formedness (is_pure/is_unit) supporting DERIV-sterngerlach-qbp |
| `x_z_orthogonal` | aux | well-formedness (is_pure/is_unit) supporting DERIV-sterngerlach-qbp |

### `TowerLaws.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `complex_add_comm` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_add_zero` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_alternative` | 🟢 anchored | PROOF-ops-alternativity-ladder |
| `complex_associative` | 🟢 anchored | PROOF-ops-associativity-ladder |
| `complex_bilinear_form` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_conj_antiAut` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_division` | 🟢 anchored | PROOF-ops-division-ladder |
| `complex_exp_exists` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_flexible` | 🟢 anchored | PROOF-ops-flexibility-ladder |
| `complex_log_exists` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_mul_comm` | 🟢 anchored | PROOF-ops-commutativity-ladder |
| `complex_neg_add` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_norm_composition` | 🟢 anchored | PROOF-ops-norm-composition-ladder |
| `complex_norm_form` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_one_mul` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_re_im` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `complex_smul_add` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_add_comm` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_add_zero` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_alternative` | 🟢 anchored | PROOF-ops-alternativity-ladder |
| `quaternion_associative` | 🟢 anchored | PROOF-ops-associativity-ladder |
| `quaternion_bilinear_form` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_conj_antiAut` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_division` | 🟢 anchored | PROOF-ops-division-ladder |
| `quaternion_exp_exists` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_flexible` | 🟢 anchored | PROOF-ops-flexibility-ladder |
| `quaternion_is_cayley_dickson_level2` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_neg_add` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_norm_composition` | 🟢 anchored | PROOF-ops-norm-composition-ladder |
| `quaternion_norm_form` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_one_mul` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_re_im` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `quaternion_smul_add` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_add_comm` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_add_zero` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_alternative` | 🟢 anchored | PROOF-ops-alternativity-ladder |
| `real_associative` | 🟢 anchored | PROOF-ops-associativity-ladder |
| `real_bilinear_form` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_conj_antiAut` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_division` | 🟢 anchored | PROOF-ops-division-ladder |
| `real_exp_exists` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_flexible` | 🟢 anchored | PROOF-ops-flexibility-ladder |
| `real_log_exists` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_mul_comm` | 🟢 anchored | PROOF-ops-commutativity-ladder |
| `real_neg_add` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_norm_composition` | 🟢 anchored | PROOF-ops-norm-composition-ladder |
| `real_norm_form` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_one_mul` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |
| `real_smul_add` | aux | trivial ring/module axiom or norm-machinery (conj/bilinear/exp-exists) behind the ladder ✓-cells |

### `UnitQuaternion.lean`

| theorem | disposition | anchor / reason |
|---|---|---|
| `mem_Sp1_iff_norm` | 🟢 anchored | PROOF-sp1-unit-quaternion-group |
| `mul_star_self_of_unit` | aux | auxiliary supporting lemma |
| `norm_inv_of_unit` | aux | auxiliary supporting lemma |
| `norm_mul_of_unit` | 🟢 anchored | PROOF-sp1-unit-quaternion-group |
| `norm_one_quat` | aux | auxiliary supporting lemma |
| `norm_preserving_iff_unit` | 🟢 anchored | PROOF-sp1-unit-quaternion-group |
| `star_mul_self_of_unit` | aux | auxiliary supporting lemma |
