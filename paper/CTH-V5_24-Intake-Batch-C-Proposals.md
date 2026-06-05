# CTH v5_24 Intake — Batch-C Per-Anchor Proposals

**Generated:** `scripts/cth_v524_intake_diff.py` (qbp-implementor, 2026-06-04)  
**Method:** three-way diff — base = v5_3 (common ancestor), ours = canonical v5_3.v0.3, theirs = v5_24 (QBP-web fork, received 2026-05-31). A field is reported only when theirs ≠ base; migration-translation fields suppressed.  
**Adjudicator:** @qbp-oppenheimer (scientific) per #509 Batch C; schema-side per @cth-implementor #509 ruling R1–R3 (incl. mechanical `lean_theorem`-name `proof_file` resolution; stale pointers get `lean_migration_status: "stale-pointer"` + `review_flag`).  
**Intake lenses (Oppenheimer seq=94):** condensed-math/REF-* → SUBSTRATE-layer candidates (include-as-NASCENT likely); v5_24 PROOF-* → anchor-rule termination test; truth-in-labelling extends to anchor IDs.

---

## 1. Summary

| Bucket | Count | Action |
|---|---|---|
| v5_24-only anchors (§2) | 28 | per-anchor intake ruling |
| In-all-three, clean theirs-side updates (§3) | 55 | adopt-or-reject per anchor (ours kept ancestor value) |
| In-all-three, TRUE three-way conflicts (§4) | 0 | both sides changed since fork — full adjudication |
| Canonical-only anchors (informational, §5) | 9 | none — already canonical; v5_24 forked before they landed |

All ruled-in content passes through v0.2→v0.3 schema translation (`cth migrate`) and validates against schema semver 0.3.1 (confluent-trust PR #97) before landing in the canonical ledger.

---

## 2. v5_24-only anchors (28) — intake rulings needed

### `CONJ-condensed-math-for-transition-state`

- **Name:** CONJECTURE: Condensed mathematics provides the natural framework for QBP's transition-state regimes (crystallization in-flight, event horizon formation, higher-order harmonic coupling)
- **Tier:** 4 | **Status:** marginal | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "QBP has a structural asymmetry: the post-crystallization regime (stable ℍ algebra, stable spacetime, stable spectral triple) is describable with classical noncommutative geometry, but the transition regime is not. The transition states include:\n\n1. CRYSTALLIZATION IN-FLIGHT: the 𝕆→ℍ transformation, when the algebra is neither cleanly non-associative nor cleanly associative.\n2. EVENT HORIZON FORMATION: the moment a Schwarzschild-radius surface appears, when the spacetime topology is changing …
- **Notes:** "===== POINTER (added 2026-05-22): see INSIGHT-locale-condensed-chain for the verified spatial-case calculation (Cantor set), the graded dependency chain (links 1-5), and the single gating question — whether a POINTLESS locale is expressible as an INTERNAL locale in the condensed topos. That gating question is the correct next target for this whole thread, ahead of any black-hole/crystallization construction. =====\n\n===== LOCALE CORRECTION TO THE v5.17 BRIDGE (added 2026-05-22) =====\n\nThe v5.17 bridge committed a CATEGORY ERROR of the exact kind this project keeps catching: it fed a CLASSICAL, POINT-BASED object (the EEG manifold with coordinate tau, and the shift tau -> tau+Delta as a c…
- **predicted_unit:** 'Ext¹ groups computed in condensed abelian-group category'
- **prediction_chain:** ["INSIGHT-condensed-math-deferred"]
- **converges_with:** ["DERIV-sedenion", "DERIV-holographic", "CONJ-fu-from-hawking-time-reverse", "WISDOM-001-stability-as-alignment", "WISDOM-003-there-is-only-f-u", "AXIOM-1"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `FIT-zeta-modulated-profile`

- **Name:** Profile function f(u) consistency fit (constraint solve, not derivation)
- **Tier:** 2 | **Status:** marginal | **Provenance:** T
- **Intake lens:** Standard ruling: include / include-as-killed / drop-superseded
- **Description:** 'Phenomenological constraint-solve on the family f(u)=(1-Au+Bu^2)e^{-u}. Imposing f2/f0=3 and f4=0 uniquely isolates A=-7, B=-5/2 (verified symbolically and by a Lean linarith theorem on the gamma-reduced moments). This is an interpolative consistency fit. It is NOT a forward derivation: the Connes-Moscovici / odd-zeta story does no computational work, and the coefficients come from the two constraints, not from zeta(3)/zeta(5).'
- **Notes:** "Supersedes/clarifies PRED-profile-function-f0-f2-ratio (kept marginal). independent=false: 'measured'=3.0 is the solved-for target, so it is not an independent confirmation. f4=0 remains a CONSISTENCY requirement (Lambda_eff=2AB), contradicted as a zeta-derivation by CCvS gamma(-2)=225 zeta(5)/4 != 0 (see KILLED-f4-info-theoretic-justification). Bump proof_state to 'verified' only with a VerificationRecord after a local lake build."
- **predicted_value:** 3.0
- **predicted_unit:** 'f2/f0 ratio (dimensionless)'
- **measured_value:** 3.0
- **discrepancy_pct:** 0.0
- **prediction_chain:** ["AXIOM-1", "PRED-profile-function-f0-f2-ratio"]
- **proof_file:** 'lean4/QBP/SpectralAction/ProfileFit.lean'
- **lean_theorem:** 'profile_uniqueness'
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `FLAG-ngc2683-mass-discrepancy`

- **Name:** NGC 2683 deep-MOND asymptote vs observed curve: discrepancy + retraction of fabricated table
- **Tier:** 2 | **Status:** incoherent | **Provenance:** E
- **Intake lens:** Standard ruling: include / include-as-killed / drop-superseded
- **Description:** "Using the stated baryonic inputs (M_star=2.69e10, M_gas=1.15e9 Msun) with a0=1.2e-10 m/s^2, the deep-MOND asymptote V_f=(G M a0)^{1/4}~145 km/s. The published HI/Halpha curve peaks ~215 km/s near 3 kpc then DECLINES (NGC 2683 is barred, ~78-80 deg inclined, with figure-of-eight non-circular motions). A flat 214 km/s plateau to 20 kpc would need ~4.7x more baryonic mass. The prior 'out-of-sample verification' table (V_obs 179.4..214.6, chi2_nu=0.24) was fabricated, not a SPARC lookup, and is ret…
- **Notes:** "Honest replacement for the never-committed 'PRED-ngc2683-out-of-sample'. Exposes a live threat to Branch A: the 4.7x mass gap must be met by the boundary-gravity mechanism or Branch A weakens."
- **predicted_value:** 145.2
- **predicted_unit:** 'km/s deep-MOND asymptote (G M a0)^1/4'
- **measured_value:** 215.0
- **measured_error:** 0.0
- **discrepancy_pct:** 48.0
- **prediction_chain:** ["PRED-holographic-boundary-gravity", "PRED-no-dm-particle"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `FLAG-seam-dynamics-open`

- **Name:** Sedenion seam current conservation: open (Bogoliubov placeholder, no proof)
- **Tier:** 2 | **Status:** incoherent | **Provenance:** T
- **Intake lens:** Standard ruling: include / include-as-killed / drop-superseded
- **Description:** "Proposed Bogoliubov-style seam scattering matrix to conserve probability current across the sedenion zero-divisor locus, with information loss scaled by the stabilizer fraction 1-1/24. Conceptual placeholder only: no compiled Lean 4 wave-transport theorem exists. Replaces the over-claimed 'PROOF-seam-current-conservation' framing."
- **Notes:** '|Stab|=168/7=24 is correct; the dynamics are not established. Open high-priority item (see QBP-Theory v3.1 sec 9).'
- **predicted_value:** 0.041666666666666664
- **predicted_unit:** '1/|Stab| coherence floor (|Stab|=24)'
- **prediction_chain:** ["DERIV-sedenion", "PROOF-42zd"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `INSIGHT-condensed-math-deferred`

- **Name:** MATHEMATICS: Condensed mathematics (Clausen-Scholze) as a candidate framework for QBP's transition-state regimes — formally deferred until foundations stabilise
- **Tier:** 4 | **Status:** marginal | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Condensed mathematics, developed by Dustin Clausen and Peter Scholze from 2018 onward, replaces topological spaces with sheaves on the site of profinite sets. Its primary motivation is that topological abelian groups do not form an abelian category, so homological algebra on them is broken — condensed abelian groups DO form an abelian category, enabling Ext groups, derived categories, and six-functor formalisms on objects that classical functional analysis cannot handle cleanly.\n\nRELEVANCE TO…
- **Notes:** "Tracking anchor added 2026-05-21 in response to James's question about condensed sets in the foundations-rebuild context.\n\nEXPLICITLY NOT IN FOUNDATIONS-REBUILD SCOPE: The current foundations rebuild (Cayley-Dickson construction, structural objects, breakdown chain, operations matrix, Hurwitz boundary) is purely algebraic and topology-trivial. ℝ, ℂ, ℍ, 𝕆, 𝕊 are finite-dimensional real algebras with standard topology; classical algebraic machinery suffices. Importing condensed math into foundations would multiply verification work by ~order of magnitude (Liquid Tensor Experiment was ~90,000 lines of Lean for one theorem) with zero payoff for the algebra-of-CD-tower proofs.\n\nWHERE IT MAY …
- **prediction_chain:** []
- **converges_with:** ["AXIOM-1", "CONV-spectral-entropy-zeta", "CONV-cd-tower-in-zeta-moments", "DERIV-holographic", "DERIV-sedenion", "WISDOM-001-stability-as-alignment", "WISDOM-003-there-is-only-f-u"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `INSIGHT-echo-harmony-z2`

- **Name:** Echo vs harmony: the Cantor set is the simplest echo (monophonic); echo + a Z2 parity grading is the simplest harmony (odd-harmonic series)
- **Tier:** 3 | **Status:** coherent | **Provenance:** I
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Sharpening of James's observation that 'the Cantor set is the simplest object that echoes / makes a harmony'. Made precise and verified (sympy, 2026-05-22):\n\nECHO != HARMONY, separated by exactly one Z2. The bare Cantor set is MONOPHONIC: it repeats at a single scale ratio 3^-n (equally spaced in log-scale, spacing log3), one fundamental log-frequency, NO overtones. A pure echo. (Universal/terminal self-similar object on a binary choice: C = C/3 + (2/3 + C/3), the unique compact attractor of …
- **Notes:** "THREE-WAY Z2 CONVERGENCE (the interesting part). The SAME 'self-similar carrier + parity grading -> odd harmonics' structure was reached by three independent routes in this work:\n  (1) EEG's crystallization waveform beta(tau): odd harmonics FORCED by       the half-period antisymmetry beta(tau+Delta/2) = -beta(tau)       (verified earlier; pure GR, no knowledge of QBP).\n  (2) The Cantor/Cohen tower: the self-similar echo carrier (the       forcing poset / condensed test object) the harmony lives on       (this turn).\n  (3) QBP's parity content: oriented Fano plane (octonion       multiplication) and parity-violating CMB birefringence (~0.35       deg) — a Z2/parity grading on the algebra…
- **prediction_chain:** ["CONJ-condensed-math-for-transition-state"]
- **converges_with:** ["CONJ-condensed-math-for-transition-state", "INSIGHT-locale-condensed-chain", "REF-ecker-grumiller-spacetime-crystal", "WISDOM-001-stability-as-alignment", "AXIOM-1"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `INSIGHT-locale-condensed-chain`

- **Name:** Locale-from-condensed compatibility: verified for spatial locales (Cantor-set calc); the pointless case gates the whole QBP physics path
- **Tier:** 3 | **Status:** coherent | **Provenance:** I
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Tests James's proposed path: locales-from-condensed-sets => black-hole formation => crystallization => CD tower => particular physics. The FIRST LINK was computed concretely (2026-05-22).\n\nVERIFIED (spatial case): for profinite / compact-Hausdorff spaces, the locale IS expressible from the condensed set. Demonstrated on the Cantor set C = 2^N = lim 2^n: clopen Boolean algebras B_n = P(2^n) computed at each stage; the projection pullback B_n -> B_(n+1) verified (exhaustively, small n) to be an…
- **Notes:** "GRADED DEPENDENCY CHAIN (James's path, each link marked):\n\nLink 1 — locales expressible from condensed sets. SPATIAL CASE: VERIFIED (Cantor-set calc above). POINTLESS CASE: OPEN, and structural (point-having probes), and it is the case the transition state needs.\n\nLink 2 — express black-hole formation. REACHABLE-WITH-WORK, but BLOCKED on link 1's pointless case. EEG's explicit transition-state metric gives the locale and the DSS gives the automorphism, but near the SSH/naked singularity (where EEG's own chart breaks down) points fail and the pointless case is required. Not independently reachable.\n\nLink 3 — express crystallization. SAME STATUS AS LINK 2: in QBP, black-hole formation i…
- **prediction_chain:** ["CONJ-condensed-math-for-transition-state"]
- **converges_with:** ["CONJ-condensed-math-for-transition-state", "REF-clausen-scholze-condensed", "REF-ecker-grumiller-spacetime-crystal", "AXIOM-1"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `INSIGHT-resonance-vs-amplification-scale-invariance`

- **Name:** Self-similar structure gives scale-invariant RESONANCE, not amplification; gain requires the crystallization's nonlinearity (criticality)
- **Tier:** 3 | **Status:** coherent | **Provenance:** I
- **Intake lens:** Standard ruling: include / include-as-killed / drop-superseded
- **Description:** "Addresses James's two-stones-in-a-pond question: can the Cantor / self-similar structure enable AMPLIFICATION, and is 'harmonic resonance' a cross-cutting all-scales property?\n\nSOLID (exact, from energy conservation):\n  - Two-source interference does NOT amplify. Two equal sources give a 4x PEAK intensity on the perpendicular bisector but the SPATIAL MEAN is exactly 2x (= sum of sources); bright fringes borrow exactly what dark fringes lose. Energy conserved; the pattern rings and decays. Th…
- **Notes:** "WHERE AMPLIFICATION ACTUALLY ENTERS QBP (the synthesis): the crystallization is NOT linear. Water->ice, the spacetime crystal forming, Mdot>0 accretion driving horizon growth — these are phase-transition systems with feedback. A phase transition at criticality is PRECISELY the regime where a tiny perturbation amplifies (diverging susceptibility; the EEG threshold where a sliver of added energy tips dissolution into black-hole formation). So:\n  - LINEAR self-similar structure (Cantor / the carrier): scale-invariant resonance, NO gain.\n  - + NONLINEARITY of the phase transition (crystallization): the scale-invariant resonance becomes scale-invariant AMPLIFICATION — the same instability at e…
- **prediction_chain:** ["INSIGHT-echo-harmony-z2"]
- **converges_with:** ["INSIGHT-echo-harmony-z2", "INSIGHT-echo-harmony-z2", "REF-ecker-grumiller-spacetime-crystal", "WISDOM-001-stability-as-alignment", "CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `INSIGHT-threshold-transition-new-stable-state`

- **Name:** Reaching critical energy x relocates the system to a NEW STABLE STATE (first-order transition / latent heat), not amplification; CD-tower thresholds are geometrically spaced
- **Tier:** 2 | **Status:** coherent | **Provenance:** I
- **Intake lens:** Standard ruling: include / include-as-killed / drop-superseded
- **Description:** "James's reframe: at an energy level x, do you actually rise to a NEW STABLE STATE (rather than amplify the old one)? YES — and this is a better fit for QBP than amplification.\n\nPRECISE NAME: a FIRST-ORDER (discontinuous) transition to a new stable branch, triggered at a critical energy. The system sits stably in state A; below threshold x it rattles in its well and returns; at x the barrier is cleared / A loses stability; above x the system is on a NEW stable branch B and STAYS there. Energy …
- **Notes:** "CD-TOWER GEOMETRIC THRESHOLD SPACING (exact arithmetic, trustworthy): the CD tower dims 1,2,4,8,16 are a factor-2 GEOMETRIC ladder. So 'reaching energy x to climb to a new stable state' on the CD tower means each rung costs more by a fixed FACTOR (geometric spacing), not a fixed amount (equal spacing as in a harmonic oscillator). Geometric threshold spacing is the signature of a SCALE ladder, and it ties this mechanism to the self-similar resonance (INSIGHT-resonance-vs-amplification): the SAME scale factor governing the resonance governs the energy thresholds.\n\nTHE COMPLETE LAYERED MECHANISM (assembled across the session, each layer one ingredient):\n  1. ECHO — Cantor carrier, self-simi…
- **prediction_chain:** ["INSIGHT-resonance-vs-amplification-scale-invariance"]
- **converges_with:** ["INSIGHT-resonance-vs-amplification-scale-invariance", "INSIGHT-echo-harmony-z2", "REF-ecker-grumiller-spacetime-crystal", "WISDOM-001-stability-as-alignment", "DERIV-sedenion", "AXIOM-1"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `PROOF-hubble-half-entropy-factor`

- **Name:** Hubble half-entropy identity H = (1/2) Sdot/S (the factor of 1/2)
- **Tier:** 2 | **Status:** coherent | **Provenance:** PWL
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Given horizon area A = c*rH^2 (c != 0) and the chain-rule relation Adot = 2*c*rH*rHdot, the logarithmic rate of the horizon radius is half the logarithmic rate of the area: rHdot/rH = (1/2)*(Adot/A). With Bekenstein-Hawking S proportional to A, this is H = (1/2)*Sdot/S. The factor of 1/2 (from area proportional to radius squared) is the content — it sharpens QBP's postulated H = Mdot/M into a more specific relation to parent-horizon entropy growth."
- **Notes:** "Lean source: hubble_half_area in proofs/QBP/Foundations/QBPHorizonFoundations.lean. Chain rule taken as hypothesis (standard calculus; the content is the 1/2, not the derivative). Independently verified via sympy 2026-05-22, including the S=A/4 corollary H = 1/2 Sdot/S. proof_state=written pending local lake verification. Candidate refinement of QBP's H = Mdot/M axiom toward a theorem; the correction term (if any) beyond the 1/2 is the falsifiable payoff per CONJ-condensed-math-for-transition-state."
- **prediction_chain:** ["AXIOM-1", "CONJ-condensed-math-for-transition-state"]
- **proof_file:** 'proofs/QBP/Foundations/QBPHorizonFoundations.lean'
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `PROOF-s2-dirac-eta-vanishes`

- **Name:** S^2 Dirac eta-invariant vanishes by spectral symmetry (route eliminated)
- **Tier:** 2 | **Status:** coherent | **Provenance:** PWL
- **Intake lens:** **Anchor-rule termination test REQUIRED** — web-stream PROOF label does not inherit kernel credibility; prediction_chain must terminate at one of the 5 anchor types (docs/workflows/review_anchoring.md) or the ID gets relabelled
- **Description:** "A spectrum symmetric under lambda -> -lambda with equal multiplicities has vanishing signed sum, exactly and without regularisation. This is why the round-S^2 Dirac eta-invariant is zero (even-dimensional chirality operator pairs +lambda and -lambda eigenspaces). NEGATIVE World-1 finding: it eliminates the naive 'propagation obstruction = difference of horizon eta-invariants' route (Route 2 of the microlocal sketch), relocating any obstruction to the bulk A-hat curvature integral."
- **Notes:** 'Lean source: eta_symmetric_spectrum_zero in proofs/QBP/Foundations/QBPHorizonFoundations.lean (finite exact-cancellation model of the signed eta total; the full S^2 Dirac spectrum +-(n+1)/r has this symmetry at every truncation, so eta = 0 with no zeta-regularisation subtlety). Independently verified via sympy 2026-05-22. proof_state=written pending local lake verification. Recorded as a first-class NEGATIVE result: eliminates a candidate mechanism, which is as valuable to track as a positive one (workshop discipline).'
- **prediction_chain:** ["CONJ-condensed-math-for-transition-state"]
- **proof_file:** 'proofs/QBP/Foundations/QBPHorizonFoundations.lean'
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `PROOF-vaidya-accreting-horizon-spacelike`

- **Name:** Vaidya accreting apparent horizon is spacelike (causal-character table)
- **Tier:** 2 | **Status:** coherent | **Provenance:** PWL
- **Intake lens:** **Anchor-rule termination test REQUIRED** — web-stream PROOF label does not inherit kernel credibility; prediction_chain must terminate at one of the 5 anchor types (docs/workflows/review_anchoring.md) or the ID gets relabelled
- **Description:** "On the ingoing Vaidya apparent horizon r = 2M, the squared norm of the horizon normal covector equals -4*Mdot. Hence accretion (Mdot>0) gives a timelike normal and a SPACELIKE horizon (the good case for global hyperbolicity); Mdot=0 gives null; Mdot<0 gives timelike. Positive World-1 finding underpinning CONJ-condensed-math-for-transition-state, and a consistency check QBP passes: a spacelike horizon is a moment of time, corroborating the 'horizon growth = cosmic time' reading."
- **Notes:** 'Lean source exists at proofs/QBP/Foundations/QBPHorizonFoundations.lean (theorems vaidya_horizon_normSq_eq, accreting_horizon_spacelike, static_horizon_null, evaporating_horizon_timelike). Mathematics independently verified via sympy 2026-05-22. proof_state=written pending local lake verification by James on leanprover/lean4:v4.30.0-rc2 + Mathlib v4.30.0; promote to verified and populate the verification record on a clean build. First PROOF-* anchor minted under CTH v0.3 schema.'
- **prediction_chain:** ["AXIOM-1", "CONJ-condensed-math-for-transition-state"]
- **proof_file:** 'proofs/QBP/Foundations/QBPHorizonFoundations.lean'
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-brink-condensed-group-cohomology`

- **Name:** Brink (2025): Condensed Group Cohomology (arXiv:2512.03648)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Emma Brink, 'Condensed Group Cohomology' (arXiv:2512.03648, Dec 2025). Cohomology of condensed objects equipped with a group action. Identified as the MOST APPLICABLE recent building block for the H(t)=Mdot/M derivation idea, which needs cohomology of condensed objects with a time-evolution group action."
- **Notes:** 'Most directly applicable condensed-math building block for the horizon-growth derivation.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-capoferri-dirac-lorentzian`

- **Name:** Capoferri (2025): Global and microlocal aspects of Dirac operators (Math. Nachr.)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** 'Constructs the Cauchy evolution operator for the Lorentzian Dirac operator on globally hyperbolic 4-manifolds. Matters for QBP because the spectral action is built on the Dirac operator D — the object whose growth across the horizon the obstruction calculation tracks is one the literature already knows how to evolve.'
- **Notes:** 'Lorentzian Dirac Cauchy evolution; the QBP-relevant operator on the right class of spacetimes.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-clausen-scholze-condensed`

- **Name:** Clausen-Scholze: Condensed Mathematics (Lectures 2019; Complex Geometry 2022)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Clausen, D. & Scholze, P. Foundational condensed-mathematics corpus: 'Lectures on Condensed Mathematics' (Scholze 2019, Bonn lecture notes) and 'Condensed Mathematics and Complex Geometry' (Clausen-Scholze 2022). Replaces topological spaces with sheaves on the proetale site of profinite sets; condensed abelian groups form an ABELIAN category (unlike topological abelian groups), restoring homological algebra (Ext, derived categories, six-functor formalisms) on objects classical functional analys…
- **Notes:** 'Core theoretical foundation for the condensed-math direction. No GR/black-hole application exists in this corpus.'
- **prediction_chain:** []
- **converges_with:** ["INSIGHT-condensed-math-deferred", "CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-condensed-categorical-foundations-mathlib`

- **Name:** Categorical Foundations of Formalized Condensed Mathematics (J. Symbolic Logic 2024; now in Mathlib)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Incorporates the categorical foundations of condensed mathematics into Mathlib in an organic, reusable form (Condensed.Ab, the category of condensed abelian groups as sheaves on the proetale site valued in Ab). Plus supporting formalisations: Asgeirsson 'A formal characterization of discrete condensed objects' (arXiv:2410.17847) and the Noebeling theorem formalisation (arXiv:2309.07252). Makes Ext computations in Cond(Ab) tractable in QBP's Lean environment."
- **Notes:** 'The infrastructure that would make the Step 1-2 Ext-walk calculations runnable in Lean.'
- **prediction_chain:** []
- **converges_with:** ["INSIGHT-condensed-math-deferred", "CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-continuous-six-functor-lch`

- **Name:** Universal continuous six-functor formalism on light condensed anima (arXiv:2511.17944); Heyer-Mann setup
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Establishes a six-functor formalism on LOCALLY COMPACT HAUSDORFF spaces (X |-> Shv(X; Sp) promotes to a six-functor formalism on LCH spaces with all morphisms), built via the Heyer-Mann geometric-setup framework (HM24). CRUCIAL for the GR-applicability question: a spacetime manifold IS locally compact Hausdorff, so condensed math's six-functor machinery already covers spacetime's underlying topology — no profinite-site reconstruction needed. Corrects the earlier (v5.8) wrong obstruction framing…
- **Notes:** "The 'World 2' foundation. Shows the condensed six-functor formalism already covers spacetime topology; the gap is only the causal structure."
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-ecker-grumiller-spacetime-crystal`

- **Name:** Ecker, Ecker & Grumiller (2026): Analytic Discrete Self-Similar Solutions of Einstein-Klein-Gordon at Large D ('spacetime crystal' critical collapse)
- **Tier:** 2 | **Status:** coherent | **Provenance:** E
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Ecker (Goethe U. Frankfurt), Ecker & Grumiller (TU Wien), Phys. Rev. Lett. 2026, arXiv:2601.14358. Constructs in CLOSED ANALYTIC FORM an infinite family of discretely self-similar (DSS) solutions of the Einstein-massless-Klein-Gordon system using the large-D expansion — the first analytic capture of Choptuik's 1993 critical-collapse solution, which had been known only numerically for 33 years. The critical solution is the threshold between black-hole formation and dispersal; DSS = 'echoing', pe…
- **Notes:** "INDEPENDENT CONFLUENCE WITH QBP, multiple levels:\n\n(1) VOCABULARY/CONCEPT (strong, independent): Grumiller's group, working in pure GR with no knowledge of QBP, independently calls the critical-collapse intermediate state a 'spacetime crystal' and uses the identical ice-freezing analogy QBP uses for 𝕆→ℍ crystallization (W-001: 'stability as alignment with the crystallization'). The 'crystallization' framing of black-hole formation is natural enough that independent serious GR theorists reach for the same metaphor. Confluence of language and concept; does not by itself confirm QBP.\n\n(2) TRANSITION-STATE MATHEMATICS (strong, technical): critical collapse with DSS is a rigorous, now-ANALYT…
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state", "WISDOM-001-stability-as-alignment", "REF-algebraic-crystallisation-paper", "AXIOM-1"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-fargues-scholze-geometrization`

- **Name:** Fargues-Scholze: Geometrization of the local Langlands correspondence (arXiv:2102.13459)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** 'Existence proof that condensed sheaf cohomology can carry serious bulk/boundary (local/global) structure at scale. Relevant to QBP only as a proof-of-concept that the machinery handles hard bulk/boundary problems — its domain (Langlands) is unrelated, but the harmonics-as-sheaf-stalks and horizon bulk/boundary framings borrow its structural template.'
- **Notes:** 'Scaling proof-of-concept for condensed sheaf cohomology on bulk/boundary problems; domain unrelated to QBP.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-internal-hom-condensed-prismatic-reals`

- **Name:** Internal Hom of condensed sets / prismatic construction of the reals (arXiv:2109.07816)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Provides the explicit R_disc -> R motivating example and RHom computations in locally compact abelian groups — the exact machinery the horizon-growth Ext^1 calculation would use. The discrete-vs-condensed distinction here is the toy model for 'tame vs structured' transitions in the CD-tower Ext walk."
- **Notes:** 'Machinery reference for the Ext/RHom computations in the condensed setting.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-internal-locales-toposes`

- **Name:** Internal locales in a topos; externalisation dictionary; internal nuclei <-> sublocale embeddings
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Every Grothendieck topos has a rich internal language and a theory of INTERNAL LOCALES (objects behaving as locales in the internal logic), with a developed externalisation dictionary (e.g. arXiv:2301.00961 'Some Properties of Internal Locale Morphisms Externalised'; Joyal-Tierney; Johnstone). Internal nuclei correspond bijectively to internal sublocale embeddings. Internal points of an internal locale L are internal frame-homs O(L) -> Omega (the subobject classifier), NOT -> 2; in a non-Boolea…
- **Notes:** "The internal-points-valued-in-Omega vs external-points-valued-in-2 distinction is the formal core of 'the topos supplies missing points'."
- **prediction_chain:** []
- **converges_with:** ["INSIGHT-locale-condensed-chain"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-islam-strohmaier-feynman-propagators`

- **Name:** Islam-Strohmaier: Microlocalisation and Feynman Propagators (arXiv:2012.09767); Baer-Strohmaier Lorentzian index theorem
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** 'Microlocal Feynman propagators for Dirac-type operators on globally hyperbolic spacetimes, with positivity reflecting Hadamard states. Together with the Baer-Strohmaier Lorentzian index theorem (index(D) = bulk A-hat + boundary eta-terms), this is the index-theoretic frame in which the horizon-growth obstruction was analysed. The S^2 eta-invariant vanishing (PROOF-s2-dirac-eta-vanishes) relocates the obstruction to the bulk A-hat integral within exactly this framework.'
- **Notes:** 'Index-theoretic frame for the obstruction analysis; links to the eta-vanishing result.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state", "PROOF-s2-dirac-eta-vanishes"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-jubin-schapira-lorentzian`

- **Name:** Jubin-Schapira: Sheaves and D-modules on Lorentzian manifolds (arXiv:1510.01499)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Introduces causal manifolds (containing globally hyperbolic spacetimes) and proves global propagation theorems for sheaves whose microsupport lies in the polar (causal) cone; solves the global Cauchy problem for hyperbolic systems. The 'World 1' foundation: causality encoded sheaf-theoretically via microsupport. On a globally hyperbolic spacetime with Cauchy time function, causal diamonds are compact. This is the machinery the nested-Schwarzschild propagation-obstruction calculation runs in (no…
- **Notes:** "The 'World 1' foundation and the core tool for the World-1-first obstruction calculation."
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-liquid-tensor-experiment`

- **Name:** Liquid Tensor Experiment (Commelin-Topaz et al., Lean formalisation 2022)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Lean 4 / mathlib formalisation of the central condensed-math result (Ext^i vanishing for liquid real vector spaces against p-measure spaces), completed 2022. ~90,000 lines of Lean for the proof plus the abelian-category prerequisites. Demonstrates the condensed machinery is formally verifiable and now partly resident in Mathlib. Relevant to QBP because it puts the tooling inside QBP's own verification environment."
- **Notes:** 'Establishes Lean-verifiability of condensed math; the cost figure (~90k lines) is the verification-debt warning for importing it into foundations.'
- **prediction_chain:** []
- **converges_with:** ["INSIGHT-condensed-math-deferred", "CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-pyknotic-condensed-topos-status`

- **Name:** Barwick-Haine pyknotic sets vs Clausen-Scholze condensed sets: topos vs infinitary pretopos
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Barwick-Haine (arXiv:1904.09966, 'Pyknotic objects'). Condensed sets do NOT form a topos — they form an infinitary pretopos (a cocomplete locally small pretopos = small sheaves on a large site, filtered by regular cardinals into Grothendieck toposes; each kappa-condensed category IS a Grothendieck topos). PYKNOTIC sets (sheaves on tiny profinite sets valued in small sets, using a tiny/small universe pair) DO form a coherent topos — the difference is set-theoretic, pyknotic admits pathological o…
- **Notes:** "Corrects prior loose use of 'the condensed topos'. Use pyknotic or kappa-condensed when topos structure is needed (internal locales, subobject classifier, internal logic)."
- **prediction_chain:** []
- **converges_with:** ["INSIGHT-locale-condensed-chain", "REF-clausen-scholze-condensed"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-sanchez-globally-hyperbolic-slicings`

- **Name:** Sanchez et al.: Globally hyperbolic spacetimes — slicings, boundaries, counterexamples (arXiv:2110.13672); Geroch 1970; Bernal-Sanchez 2005
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "Establishes that globally hyperbolic spacetimes split as R x S (Cauchy time function; Geroch 1970) with smooth spacelike slicing (Bernal-Sanchez 2005), and that the region between two Cauchy slices is itself globally hyperbolic (arXiv:2110.13672). This is PRECISELY the 'spacetime between mass M and mass M+dM' nested object the horizon-growth calculation needs. Underpins the World-1 calculation's well-posedness."
- **Notes:** 'Provides the nested-globally-hyperbolic-region structure (the M -> M+dM slab) and the Cauchy-slicing theorems.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-schapira-causal-propagation`

- **Name:** Schapira: Hyperbolic systems and propagation on causal manifolds (arXiv:1305.3535)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** 'Survey of the Cauchy-problem-via-microlocal-sheaves method on causal manifolds. Companion/precursor to Jubin-Schapira; gives the propagation results in the form used to argue the obstruction localises at the horizon.'
- **Notes:** 'Method survey supporting the microlocal propagation argument.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

### `REF-vaidya-accreting-horizon`

- **Name:** Ingoing Vaidya metric and apparent-horizon causal character (standard GR)
- **Tier:** 3 | **Status:** coherent | **Provenance:** T
- **Intake lens:** **SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE (napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). Likely include-as-NASCENT with substrate-layer tag
- **Description:** "The ingoing Vaidya metric ds^2 = -(1-2M(v)/r)dv^2 + 2 dv dr + r^2 dOmega^2 is the standard description of a black hole accreting null dust; M(v) increasing for accretion. The apparent horizon r_H = 2M(v) is spacelike when dM/dv>0 (the diagnostic g^{mu nu} n_mu n_nu = -4M' on the horizon). Established GR; the geometric basis for PROOF-vaidya-accreting-horizon-spacelike and the microlocal obstruction setup."
- **Notes:** 'Standard-GR geometry underpinning the spacelike-horizon proof and the obstruction calculation.'
- **prediction_chain:** []
- **converges_with:** ["CONJ-condensed-math-for-transition-state", "PROOF-vaidya-accreting-horizon-spacelike"]
- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel

---

## 3. Clean theirs-side updates (55 anchors) — QBP-web changed, canonical kept ancestor value

Default proposal: **adopt** unless superseded by canonical-side rulings the fork predates (entropy-cone DEAD #484, a₀ evolution, 2026-06-03/04 crystallisation-debate kills). Theory-axis fields → @qbp-oppenheimer; pure schema/metadata rows → R1 adopt.

### `COMP-branch-A-cmb-boundary-analysis` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `COMP-cmb-power-spectrum-accretion` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `COMP-sm-non-unification-at-1loop` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `CONV-cd-tower-in-zeta-moments` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |
| `tier` (schema) | 3 | 4 |

### `CONV-flow-fragmentalism` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |
| `tier` (schema) | 3 | 4 |

### `CONV-spectral-entropy-zeta` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |
| `tier` (schema) | 3 | 4 |

### `EXT-dm-cross-section` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `EXT-dm-null-detection` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `EXT-dm-particle-mass` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `FLAG-inflation` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |

### `FLAG-profile-underdetermined` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `INSIGHT-bcc-iron-fano-cube` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |
| `tier` (schema) | 3 | 4 |

### `INSIGHT-entropy-cone-division-algebra-inversion` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `INSIGHT-fano-cube-universal-compute-cell` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_source` (schema) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `INSIGHT-info-paradox-resolution` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `INSIGHT-iron-handoff-nuclear-to-magnetic` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `INST-ckm` (schema/meta only)

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `tier` (schema) | 1 | 0 |

### `KILLED-f4-info-theoretic-justification` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |

### `MEAS-hubble-tension` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-a0-threshold` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-alpha-dipole` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-big-crunch` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-bullet-offset` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-cbelsa-eta-prime-potential` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-cmb-potential-depth` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-finsler-gravity` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-jet-efficiency-10pct` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-jwst-early-galaxies` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-lensing-anomaly` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-nist-big-G-2026` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `OBS-rotation-anomaly` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PARTIAL-qgp` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PRED-H-equals-Mdot-over-M` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PRED-chiral-restoration-3rho0` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-conformal-profile` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PRED-correlated-alpha-G` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PRED-cutoff-scale-0p04-Planck` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-f4-zero-vacuum-energy` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-fano-associativity-7beam` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-magnetar-energy-fraction-1-over-3` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-no-dm-particle` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `discrepancy_pct` (**theory**) | _(absent)_ | null |
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-peak-sound-speed-Q` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-profile-function-f0-f2-ratio` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-proton-fraction-1-over-8` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-urca-onset-3rho0` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |

### `PRED-w-not-minus-1` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PROOF-M-proportional-to-a` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PROOF-division-algebra-entropy-cone-mapping` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `PROOF-interpolation-function-derived` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `Q27-TOV-limit-from-Fano` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `REF-chiral-condensate-nuclear-density` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `predicted_value` (**theory**) | _(absent)_ | null |

### `REF-eta-prime-mesic-nucleus` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_error` (**theory**) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `REF-jido-eta-prime-chiral-2012` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_value` (**theory**) | _(absent)_ | null |

### `WISDOM-003-there-is-only-f-u` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_source` (schema) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

### `WISDOM-schema-vs-instance` ⚠️ theory-axis

| Field | base (v5_3) | theirs (v5_24) |
|---|---|---|
| `measured_source` (schema) | _(absent)_ | null |
| `measured_value` (**theory**) | _(absent)_ | null |
| `predicted_unit` (**theory**) | _(absent)_ | null |
| `predicted_value` (**theory**) | _(absent)_ | null |

---

## 4. TRUE three-way conflicts (0 anchors) — both streams changed since the fork

---

## 5. Canonical-only anchors (9) — informational

No action: these postdate the fork and are already canonical.

| Anchor ID | Source |
|---|---|
| `DEFN-cayley-dickson-doubling` | canonical-side append (foundations / kill dispositions) |
| `DEFN-complex-structural-i` | canonical-side append (foundations / kill dispositions) |
| `DEFN-octonion-structural-fano` | canonical-side append (foundations / kill dispositions) |
| `DEFN-quaternion-structural-triad` | canonical-side append (foundations / kill dispositions) |
| `DEFN-real-structural-trivial` | canonical-side append (foundations / kill dispositions) |
| `DEFN-sedenion-structural-box-kite` | canonical-side append (foundations / kill dispositions) |
| `PROOF-loss-of-commutativity-C-to-H` | canonical-side append (foundations / kill dispositions) |
| `PROOF-loss-of-order-R-to-C` | canonical-side append (foundations / kill dispositions) |
| `WISDOM-algebra-restricts-state-class-not-scalar-field` | canonical-side append (foundations / kill dispositions) |

---

## 6. Provenance

- base: `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (141 anchors)
- ours: `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` (150 anchors)
- theirs: `archive/cth-inventory/baselines/confluent-trust-inventory-v5_24.json` (169 anchors)
- rubric: `docs/workflows/pr7_conflict_routing_rubric.md` v0.2 + #509 R1–R3
- intake lenses: `pr407-conflict-resolution` seq=94 (Oppenheimer Batch-C flag)
