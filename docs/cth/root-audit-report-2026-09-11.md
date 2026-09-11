# Root audit report (issue #654 D6)

Ledger: `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` — register: `docs/cth/root-audit-register.json`

## Roots (whole population of the root lists)

| Root | lives in | bucket | reason | register issue |
|---|---|---|---|---|
| META-1 | meta_axiom | UNSORTED | no forcing (forced_by), no ruling cite, no kill_condition | https://github.com/JamesPagetButler/QBP/issues/655 |
| AXIOM-1 | axioms | UNSORTED | no forcing (forced_by), no ruling cite, no kill_condition | https://github.com/JamesPagetButler/QBP/issues/647 |
| AXIOM-2 | axioms | UNSORTED | no forcing (forced_by), no ruling cite, no kill_condition | https://github.com/JamesPagetButler/QBP/issues/473 |

## Counts

| bucket | roots |
|---|---|
| bucket-1 PROVED | 0 |
| bucket-2 FORCED | 0 |
| bucket-3 OPEN | 0 |
| UNSORTED (registered or failing) | 3 |
| bucket-4 RETIRED | 0 |

## Chains: 10 principles + 290 anchors; 300 chain owners walked

### Unresolved ids (16) — gated for every owner

- `INST-f0` cited via: MEAS-alpha -> INST-f0; MEAS-sin2tw -> INST-f0; MEAS-alphas -> INST-f0; OBS-f0-2alpha -> INST-f0; CONSTRAINT-ynu -> INST-f0
- `DERIV-rge` cited via: MEAS-sin2tw -> DERIV-rge; MEAS-alphas -> DERIV-rge
- `INST-theta` cited via: MEAS-koide -> INST-theta
- `DERIV-slater` cited via: MEAS-udd -> DERIV-slater; MEAS-delta -> DERIV-slater; MEAS-tolfac -> DERIV-slater; FLAG-postd-IE -> DERIV-slater
- `DERIV-ie` cited via: MEAS-udd -> DERIV-ie; MEAS-delta -> DERIV-ie
- `DERIV-screening` cited via: MEAS-udd -> DERIV-screening
- `DERIV-electronegativity` cited via: MEAS-delta -> DERIV-electronegativity
- `DERIV-tpd` cited via: MEAS-jd -> DERIV-tpd; FLAG-J -> DERIV-tpd; FLAG-Tc -> FLAG-J -> DERIV-tpd; PRED-willow-j -> DERIV-tpd
- `DERIV-teff` cited via: MEAS-jd -> DERIV-teff; FLAG-J -> DERIV-teff; FLAG-Tc -> FLAG-J -> DERIV-teff; FLAG-xi -> DERIV-teff; FLAG-Hc2 -> FLAG-xi -> DERIV-teff
- `DERIV-lambda` cited via: MEAS-jd -> DERIV-lambda
- `DERIV-xi` cited via: MEAS-jd -> DERIV-xi
- `DERIV-ionic-radii` cited via: MEAS-tolfac -> DERIV-ionic-radii
- `DERIV-tolerance` cited via: MEAS-tolfac -> DERIV-tolerance
- `INST-TcJ-ratio` cited via: FLAG-Tc -> INST-TcJ-ratio
- `PROOF-koide` cited via: PRED-koide-phase-2-over-9 -> PROOF-koide; PRED-wolfenstein-A-sqrt-Q -> PROOF-koide
- `PROOF-stabiliser-order-24` cited via: PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; Q27-TOV-limit-from-Fano -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PRED-TOV-limit-sqrt-7-over-3 -> Q27-TOV-limit-from-Fano -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PRED-chiral-restoration-3rho0 -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PRED-peak-sound-speed-Q -> PRED-chiral-restoration-3rho0 -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; INSIGHT-iron-handoff-nuclear-to-magnetic -> PRED-TOV-limit-sqrt-7-over-3 -> Q27-TOV-limit-from-Fano -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PRED-urca-onset-3rho0 -> PRED-chiral-restoration-3rho0 -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PRED-urca-onset-3rho0 -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; FLAG-tov-eos-shape-underdetermined -> PRED-TOV-limit-sqrt-7-over-3 -> Q27-TOV-limit-from-Fano -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; INSIGHT-eos-integration-shifts-tov-by-30pct -> PRED-peak-sound-speed-Q -> PRED-chiral-restoration-3rho0 -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; INSIGHT-eos-integration-shifts-tov-by-30pct -> PRED-chiral-restoration-3rho0 -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PRED-tov-mass-at-bump-peak -> PRED-TOV-limit-sqrt-7-over-3 -> Q27-TOV-limit-from-Fano -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24; PROOF-iron-to-ns-bridge -> PRED-TOV-limit-sqrt-7-over-3 -> Q27-TOV-limit-from-Fano -> PRED-eta-prime-mass-shift-1-over-24 -> PROOF-stabiliser-order-24

### Dangling gated chains — principles / DERIV-* / PRED-* (18)

- `PRED-conformal-sound-speed-1-over-3`: PRED-conformal-sound-speed-1-over-3 (empty chain)
- `PRED-magnetar-energy-fraction-1-over-3`: PRED-magnetar-energy-fraction-1-over-3 (empty chain)
- `PRED-fano-associativity-7beam`: PRED-fano-associativity-7beam (empty chain)
- `PRED-tov-mass-at-bump-peak`: PRED-tov-mass-at-bump-peak -> PRED-conformal-sound-speed-1-over-3 (empty prediction_chain)
- `DERIV-vaidya-accreting-horizon-spacelike`: DERIV-vaidya-accreting-horizon-spacelike -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `DERIV-hubble-half-entropy-factor`: DERIV-hubble-half-entropy-factor -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `DERIV-fraunhofer-optics`: DERIV-fraunhofer-optics (empty chain)
- `DERIV-sterngerlach-qbp`: DERIV-sterngerlach-qbp (empty chain)
- `DERIV-angle-dependent-qbp`: DERIV-angle-dependent-qbp (empty chain)
- `DERIV-general3d-qbp`: DERIV-general3d-qbp (empty chain)
- `DERIV-doubleslit-visibility-model`: DERIV-doubleslit-visibility-model (empty chain)
- `DERIV-measurement-ansatz-basic`: DERIV-measurement-ansatz-basic (empty chain)
- `DERIV-code-si-constants`: DERIV-code-si-constants (empty chain)
- `DERIV-kitaev-model`: DERIV-kitaev-model (empty chain)
- `DERIV-graphene-model`: DERIV-graphene-model (empty chain)
- `DERIV-bi2se3-ti`: DERIV-bi2se3-ti (empty chain)
- `DERIV-crystallisation-spectral-moments`: DERIV-crystallisation-spectral-moments (empty chain)
- `DERIV-quaternion-physics-kramers`: DERIV-quaternion-physics-kramers (empty chain)

### Cycles (0)


### Reported, not gated — other kinds with non-terminating chains (67)

| kind | owners |
|---|---|
| COMP | 1 |
| CONJ | 2 |
| CONV | 3 |
| DEFN | 7 |
| EXT | 2 |
| INSIGHT | 19 |
| INST | 1 |
| KILLED | 1 |
| META | 2 |
| OBS | 1 |
| PROOF | 6 |
| QBP | 2 |
| REF | 18 |
| WISDOM | 2 |

- `INST-ckm`: INST-ckm (empty chain)
- `OBS-finsler-gravity`: OBS-finsler-gravity (empty chain)
- `EXT-dm-particle-mass`: EXT-dm-particle-mass (empty chain)
- `EXT-dm-cross-section`: EXT-dm-cross-section (empty chain)
- `REF-algebraic-crystallisation-paper`: REF-algebraic-crystallisation-paper (empty chain)
- `CONV-flow-fragmentalism`: CONV-flow-fragmentalism (empty chain)
- `REF-jido-eta-prime-chiral-2012`: REF-jido-eta-prime-chiral-2012 (empty chain)
- `INSIGHT-urca-threshold-dim-O`: INSIGHT-urca-threshold-dim-O (empty chain)
- `INSIGHT-entropy-cone-division-algebra-inversion`: INSIGHT-entropy-cone-division-algebra-inversion (empty chain)
- `INSIGHT-bcc-iron-fano-cube`: INSIGHT-bcc-iron-fano-cube (empty chain)
- `INSIGHT-fano-cube-universal-compute-cell`: INSIGHT-fano-cube-universal-compute-cell (empty chain)
- `WISDOM-schema-vs-instance`: WISDOM-schema-vs-instance (empty chain)
- `COMP-sm-non-unification-at-1loop`: COMP-sm-non-unification-at-1loop (empty chain)
- `CONV-spectral-entropy-zeta`: CONV-spectral-entropy-zeta (empty chain)
- `CONV-cd-tower-in-zeta-moments`: CONV-cd-tower-in-zeta-moments (empty chain)
- `DEFN-cayley-dickson-doubling`: DEFN-cayley-dickson-doubling (empty chain)
- `DEFN-real-structural-trivial`: DEFN-real-structural-trivial (empty chain)
- `DEFN-complex-structural-i`: DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `DEFN-quaternion-structural-triad`: DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `DEFN-octonion-structural-fano`: DEFN-octonion-structural-fano -> DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `DEFN-sedenion-structural-box-kite`: DEFN-sedenion-structural-box-kite -> DEFN-octonion-structural-fano -> DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `PROOF-loss-of-order-R-to-C`: PROOF-loss-of-order-R-to-C -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `PROOF-loss-of-commutativity-C-to-H`: PROOF-loss-of-commutativity-C-to-H -> DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `WISDOM-algebra-restricts-state-class-not-scalar-field`: WISDOM-algebra-restricts-state-class-not-scalar-field (empty chain)
- `INSIGHT-eos-integration-shifts-tov-by-30pct`: INSIGHT-eos-integration-shifts-tov-by-30pct -> PRED-conformal-sound-speed-1-over-3 (empty prediction_chain)
- `META-physical-mapping-status-field`: META-physical-mapping-status-field (empty chain)
- `META-regime-of-validity-field`: META-regime-of-validity-field (empty chain)
- `REF-brink-condensed-group-cohomology`: REF-brink-condensed-group-cohomology (empty chain)
- `REF-capoferri-dirac-lorentzian`: REF-capoferri-dirac-lorentzian (empty chain)
- `REF-clausen-scholze-condensed`: REF-clausen-scholze-condensed (empty chain)
- `REF-condensed-categorical-foundations-mathlib`: REF-condensed-categorical-foundations-mathlib (empty chain)
- `REF-continuous-six-functor-lch`: REF-continuous-six-functor-lch (empty chain)
- `REF-fargues-scholze-geometrization`: REF-fargues-scholze-geometrization (empty chain)
- `REF-internal-hom-condensed-prismatic-reals`: REF-internal-hom-condensed-prismatic-reals (empty chain)
- `REF-internal-locales-toposes`: REF-internal-locales-toposes (empty chain)
- `REF-islam-strohmaier-feynman-propagators`: REF-islam-strohmaier-feynman-propagators (empty chain)
- `REF-jubin-schapira-lorentzian`: REF-jubin-schapira-lorentzian (empty chain)
- `REF-liquid-tensor-experiment`: REF-liquid-tensor-experiment (empty chain)
- `REF-pyknotic-condensed-topos-status`: REF-pyknotic-condensed-topos-status (empty chain)
- `REF-sanchez-globally-hyperbolic-slicings`: REF-sanchez-globally-hyperbolic-slicings (empty chain)
- `REF-schapira-causal-propagation`: REF-schapira-causal-propagation (empty chain)
- `REF-vaidya-accreting-horizon`: REF-vaidya-accreting-horizon (empty chain)
- `CONJ-condensed-math-for-transition-state`: CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-condensed-math-deferred`: INSIGHT-condensed-math-deferred (empty chain)
- `INSIGHT-locale-condensed-chain`: INSIGHT-locale-condensed-chain -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-echo-harmony-z2`: INSIGHT-echo-harmony-z2 -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-resonance-vs-amplification-scale-invariance`: INSIGHT-resonance-vs-amplification-scale-invariance -> INSIGHT-echo-harmony-z2 -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-threshold-transition-new-stable-state`: INSIGHT-threshold-transition-new-stable-state -> INSIGHT-resonance-vs-amplification-scale-invariance -> INSIGHT-echo-harmony-z2 -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-s2-dirac-eta-vanishes`: INSIGHT-s2-dirac-eta-vanishes -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-octonion-quaternion-branching`: INSIGHT-octonion-quaternion-branching (empty chain)
- `INSIGHT-crystallisation-ssb-ingredients`: INSIGHT-crystallisation-ssb-ingredients (empty chain)
- `INSIGHT-crystallisation-gauge-vs-physical`: INSIGHT-crystallisation-gauge-vs-physical (empty chain)
- `INSIGHT-octonion-higgs-killed`: INSIGHT-octonion-higgs-killed (empty chain)
- `CONJ-vconstants-keystone`: CONJ-vconstants-keystone -> INSIGHT-octonion-quaternion-branching (empty prediction_chain); CONJ-vconstants-keystone -> INSIGHT-crystallisation-ssb-ingredients (empty prediction_chain)
- `INSIGHT-direct-gamma-fixed-ratio-generic`: INSIGHT-direct-gamma-fixed-ratio-generic -> CONJ-vconstants-keystone -> INSIGHT-octonion-quaternion-branching (empty prediction_chain); INSIGHT-direct-gamma-fixed-ratio-generic -> CONJ-vconstants-keystone -> INSIGHT-crystallisation-ssb-ingredients (empty prediction_chain)
- `QBP-POS-emergent-time`: QBP-POS-emergent-time (empty chain)
- `DEFN-purely-algebraic-derivation-gate`: DEFN-purely-algebraic-derivation-gate (empty chain)
- `INSIGHT-footprint-cd-dimension-pyrrhic`: INSIGHT-footprint-cd-dimension-pyrrhic (empty chain)
- `INSIGHT-constants-no-content-distinct`: INSIGHT-constants-no-content-distinct (empty chain)
- `INSIGHT-loop-closure-structural-obstruction`: INSIGHT-loop-closure-structural-obstruction (empty chain)
- `QBP-POS-organization-not-generator`: QBP-POS-organization-not-generator -> DEFN-purely-algebraic-derivation-gate (empty prediction_chain); QBP-POS-organization-not-generator -> INSIGHT-footprint-cd-dimension-pyrrhic (empty prediction_chain); QBP-POS-organization-not-generator -> INSIGHT-constants-no-content-distinct (empty prediction_chain); QBP-POS-organization-not-generator -> INSIGHT-loop-closure-structural-obstruction (empty prediction_chain)
- `PROOF-cd-algebra-finrank-2n`: PROOF-cd-algebra-finrank-2n -> DEFN-cayley-dickson-doubling (empty prediction_chain)
- `PROOF-sp1-unit-quaternion-group`: PROOF-sp1-unit-quaternion-group -> DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `PROOF-fano-genesis`: PROOF-fano-genesis -> DEFN-octonion-structural-fano -> DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `PROOF-s3-hspace`: PROOF-s3-hspace -> DEFN-quaternion-structural-triad -> DEFN-complex-structural-i -> DEFN-real-structural-trivial (empty prediction_chain)
- `KILLED-locale-forcing-route`: KILLED-locale-forcing-route (empty chain)
- `REF-adams-hopf-invariant-one`: REF-adams-hopf-invariant-one (empty chain)

## Warnings (2)

- registered smuggled root META-physical-mapping-status-field in anchors[] (issue https://github.com/JamesPagetButler/QBP/issues/657)
- registered smuggled root META-regime-of-validity-field in anchors[] (issue https://github.com/JamesPagetButler/QBP/issues/657)

## Gate: PASS

