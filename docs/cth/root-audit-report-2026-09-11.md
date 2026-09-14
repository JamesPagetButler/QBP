# Root audit report (issue #654 D6)

Ledger: `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` — register: `docs/cth/root-audit-register.json`

## Scope of the root population

Roots are the id-bearing records of the root lists ['meta_axiom', 'meta_principles', 'axioms', 'interpretations'] (plus any root-prefixed id found elsewhere, reported as smuggled). A ledger may carry roots the programme names but has not yet encoded as records — e.g. the #654 D6 expectation of six roots (AXIOM-1, POST-hosting, the rule, META-2, the crystal definition, the state-space identification) against the three records below: POST-hosting and META-2 are not encoded until the #652 encode lands; the rule (#635), the crystal definition and the state-space identification live inside other records under non-root prefixes and are outside this gate's reach until encoded as roots. The gate audits what is written, and says so.

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

### Dangling gated chains — principles / DERIV-* / PRED-* (29)

- `INST-ckm`: INST-ckm (empty chain)
- `EXT-dm-particle-mass`: EXT-dm-particle-mass (empty chain)
- `EXT-dm-cross-section`: EXT-dm-cross-section (empty chain)
- `REF-algebraic-crystallisation-paper`: REF-algebraic-crystallisation-paper (empty chain)
- `PRED-conformal-sound-speed-1-over-3`: PRED-conformal-sound-speed-1-over-3 (empty chain)
- `PRED-magnetar-energy-fraction-1-over-3`: PRED-magnetar-energy-fraction-1-over-3 (empty chain)
- `PRED-fano-associativity-7beam`: PRED-fano-associativity-7beam (empty chain)
- `COMP-sm-non-unification-at-1loop`: COMP-sm-non-unification-at-1loop (empty chain)
- `INSIGHT-eos-integration-shifts-tov-by-30pct`: INSIGHT-eos-integration-shifts-tov-by-30pct -> PRED-conformal-sound-speed-1-over-3 (empty prediction_chain)
- `PRED-tov-mass-at-bump-peak`: PRED-tov-mass-at-bump-peak -> PRED-conformal-sound-speed-1-over-3 (empty prediction_chain)
- `INSIGHT-locale-condensed-chain`: INSIGHT-locale-condensed-chain -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-echo-harmony-z2`: INSIGHT-echo-harmony-z2 -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-resonance-vs-amplification-scale-invariance`: INSIGHT-resonance-vs-amplification-scale-invariance -> INSIGHT-echo-harmony-z2 -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-threshold-transition-new-stable-state`: INSIGHT-threshold-transition-new-stable-state -> INSIGHT-resonance-vs-amplification-scale-invariance -> INSIGHT-echo-harmony-z2 -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
- `INSIGHT-s2-dirac-eta-vanishes`: INSIGHT-s2-dirac-eta-vanishes -> CONJ-condensed-math-for-transition-state -> INSIGHT-condensed-math-deferred (empty prediction_chain)
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


### Reported, not gated — other kinds with non-terminating chains (61)

| kind | owners |
|---|---|
| CONJ | 2 |
| CONV | 3 |
| DEFN | 7 |
| EXT | 1 |
| INSIGHT | 14 |
| KILLED | 1 |
| META | 2 |
| OBS | 1 |
| PRED | 1 |
| PROOF | 7 |
| QBP | 2 |
| REF | 18 |
| WISDOM | 2 |

- `OBS-finsler-gravity`: OBS-finsler-gravity (empty chain)
- `EXT-dm-null-detection`: EXT-dm-null-detection (empty chain)
- `CONV-flow-fragmentalism`: CONV-flow-fragmentalism (empty chain)
- `REF-jido-eta-prime-chiral-2012`: REF-jido-eta-prime-chiral-2012 (empty chain)
- `INSIGHT-urca-threshold-dim-O`: INSIGHT-urca-threshold-dim-O (empty chain)
- `INSIGHT-entropy-cone-division-algebra-inversion`: INSIGHT-entropy-cone-division-algebra-inversion (empty chain)
- `PROOF-division-algebra-entropy-cone-mapping`: PROOF-division-algebra-entropy-cone-mapping (empty chain)
- `INSIGHT-branch-A-hypergraph-boundary`: INSIGHT-branch-A-hypergraph-boundary -> PROOF-division-algebra-entropy-cone-mapping (empty prediction_chain)
- `INSIGHT-bcc-iron-fano-cube`: INSIGHT-bcc-iron-fano-cube (empty chain)
- `INSIGHT-fano-cube-universal-compute-cell`: INSIGHT-fano-cube-universal-compute-cell (empty chain)
- `WISDOM-schema-vs-instance`: WISDOM-schema-vs-instance (empty chain)
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
- `META-physical-mapping-status-field`: META-physical-mapping-status-field (empty chain)
- `META-regime-of-validity-field`: META-regime-of-validity-field (empty chain)
- `PRED-hypergraph-cmb-camb-rerun`: PRED-hypergraph-cmb-camb-rerun -> INSIGHT-branch-A-hypergraph-boundary -> PROOF-division-algebra-entropy-cone-mapping (empty prediction_chain); PRED-hypergraph-cmb-camb-rerun -> PROOF-division-algebra-entropy-cone-mapping (empty prediction_chain)
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
- `REF-phantom-cohesion-before-computation`: REF-phantom-cohesion-before-computation (empty chain)
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

## Dead anchors (status killed / incoherent / refuted) — visibility (qbp-implementor, live-test 1336)

A dead anchor carries no derivation obligation of its own AND satisfies nobody else's: it is
not a terminator and not a forcing. Marking an anchor dead is a reviewed status change; this
section makes a wave of such changes visible on the report, not only in a diff.

- dead owners (ungated for termination): 19 — `PROOF-fano`, `FLAG-J`, `FLAG-Tc`, `FLAG-xi`, `FLAG-Hc2`, `FLAG-postd-IE`, `EXT-dm-null-detection`, `PRED-conformal-profile`, `COMP-branch-A-cmb-boundary-analysis`, `INSIGHT-entropy-cone-division-algebra-inversion`, `PROOF-division-algebra-entropy-cone-mapping`, `Q28-alpha-GUT-from-stabiliser`, `KILLED-f4-info-theoretic-justification`, `PRED-hypergraph-cmb-camb-rerun`, `FLAG-ngc2683-mass-discrepancy`, `FLAG-seam-dynamics-open`, `REF-phantom-cohesion-before-computation`, `INSIGHT-octonion-higgs-killed`, `KILLED-locale-forcing-route`
- dead anchors reached directly by live chains (each such chain must ground elsewhere): 3 — `PROOF-fano` (×6), `PROOF-division-algebra-entropy-cone-mapping` (×1), `COMP-branch-A-cmb-boundary-analysis` (×1)
- roots rejected for a dead `forced_by`: 0

## Warnings (2)

- registered smuggled root META-physical-mapping-status-field in anchors[154][] (issue https://github.com/JamesPagetButler/QBP/issues/657)
- registered smuggled root META-regime-of-validity-field in anchors[155][] (issue https://github.com/JamesPagetButler/QBP/issues/657)

## Gate: PASS

