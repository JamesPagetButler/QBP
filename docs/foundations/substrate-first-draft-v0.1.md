# The QBP substrate, first draft v0.1 (2026-09-25)

**Status:** assembly document for #684 (parent #473), branch `research/473-substrate-first-draft`, author qbp-oppenheimer. The substrate stated in one place, every claim tagged. **No new mathematics, no kill's status touched, no acceptance criterion of #473 claimed.** Ledger of record: `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` 6.8.0 (331 anchors, master `b111eb4`). Tier-2 review.

## 0. Reading guide

| Tag | Meaning | Cites |
|---|---|---|
| **PROVED** | a 0-sorry Lean 4 or `--safe` Cubical Agda theorem anchored on the ledger; the sentence stays inside the anchor's NOT-claimed clause | an anchor id; eight anchors on open PRs are cited "PR #681/#682, pending merge" |
| **NUMERICAL** | a scripted computation or an analytic derivation not machine-checked | an `analysis/` file |
| **POSTULATE** | a clause the theory asserts and does not derive (PERMITTED, never FORCED) | the ruling or issue stating it |
| **OPEN** | not settled either way | the owning issue, or "no issue" |

This is the assembly of ingredients scattered across six addenda, five attack reports, three Lean files and the ledger, holes named as holes; not a derivation, a ruling, or a completion of AC1/AC2/AC3. Unsourced facts are marked `[UNSOURCED — needs …]`, not supplied.

## 1. Carrier

| Object | Statement | Tag | Source |
|---|---|---|---|
| Algebra 𝕊 | 𝕊 = CD(𝕆) = `CDAlg ℝ 4` as ℝ¹⁶; s = a + bℓ with octonions a = `cdLo s`, b = `cdHi s` | **PROVED** | PROOF-substrate-hosting-definition |
| Metric N | the Cayley–Dickson norm form, positive definite at level 4; the only metric on record | **PROVED** | PROOF-normed-division-tower-existence |
| StateSphere | `{s : s₀ = 0 ∧ N s = 1}`, the imaginary unit sphere S¹⁴ | **PROVED** | PROOF-substrate-hosting-definition |
| Potential V | V(s) = N([a, b]) = 4(AC − P²), A = N(Im a), C = N(Im b), P = ⟪Im a, Im b⟫, unconditionally; V ≥ 0; V ≤ N(s)² | **PROVED** | PROOF-delta-landscape-descent; PROOF-potential-bounded-by-normForm-sq-frozen-max |
| Gram invariants | V depends on (A, C, P) only, so it descends to S¹⁴/G₂; with B = b₀² these are §2's coordinates | **PROVED** | PROOF-delta-landscape-descent |
| Vacua (crystals) | {V = 0} ∩ StateSphere = `UniverseSpace`; V = 0 ⇔ the components commute ⇔ the left alternator vanishes ⇔ a = αu, Im b = γu for one imaginary direction u (poles u = 0: s = b₀ℓ) | **PROVED** | PROOF-alternator-vanishes-iff-commute; PROOF-vacuum-parametrisation |
| Vacuum topology | modulo G₂ a 2-sphere (θ mod 180°, b₀); modulo S₃ the orbifold S²(2,2,3) | **NUMERICAL** | `analysis/473-dirac-probe/orbit_space.py`, `lmaps_check.py`, `aut_s3.py` (NOT formalised, per PROOF-vacuum-parametrisation) |
| Partition | StateSphere = UniverseSpace ⊔ InFlight = {V > 0}; both non-empty; vacua beyond the ℂ-poles exist | **PROVED** | PROOF-substrate-hosting-definition |
| Frozen ridge | on StateSphere V attains its maximum, exactly 1, and every point with V = 1 is a rest point of the rule field | **PROVED** | PROOF-potential-bounded-by-normForm-sq-frozen-max |
| Ridge dimension | {V = 1} has dimension 11 (codimension 3) | **NUMERICAL** | "numerically 11", NOT proved, per PROOF-potential-bounded-by-normForm-sq-frozen-max; `[UNSOURCED — needs the measuring script]` |
| Zero divisors on the ridge | \|N(sx) − N(s)N(x)\| ≤ √V(s)·N(x) (sharp, both-handed); every zero divisor has V = N², on the sphere V = 1; nonzero crystals are never zero divisors | **PROVED** | PROOF-zero-divisors-sit-at-potential-max |
| Ridge ⊇ zero divisors, not = | the converse V = N² ⇒ zero divisor is NOT proved (numerically true) | **OPEN** | NOT-proved clause of PROOF-zero-divisors-sit-at-potential-max; the P5-open marker in `RuleFlow.lean` §18; no issue |
| Basis-sum zero divisors | exactly 42 basis-sum zero-divisor planes (kernel `decide`) | **PROVED** | PROOF-42zd |
| Seam witness kernel | at z = e₁ + e₁₀: ker L_z is exactly a 4-plane (rank 12); ker L_z = ker R_z; the 4-plane is not a subalgebra (k₁² = −2·1) | **PROVED** | PROOF-seam-zd-witness-kernel-four; PROOF-seam-zd-witness-kernels-coincide; PROOF-seam-zd-witness-kernel-not-subalgebra |
| Seam spectrum | at z = e₁ + e₁₀: L_zᵀL_z has spectrum exactly 4 (×4), 2 (×8), 0 (×4); R_z shares it; the top eigenspace T(z) lies on the ridge and consists of two-sided zero divisors; T(e₁+e₁₀) = ker L_{e₁−e₁₀}; for every basis pair e_a ± e_b the spectrum lies in [0, 4] with E₄(G₊) = ker L_{z₋}, E₀ = ker L_z (no multiplicity fixed) | **PROVED** | PROOF-seam-zd-gram-spectrum-4-8-4, PROOF-seam-top-plane-on-frozen-ridge, PROOF-seam-right-gram-equals-left, PROOF-basis-pair-gram-uniform-bounds (PR #682, pending merge) |
| S₃ action, ℤ/2 | `gradeAut` (ℓ ↦ −ℓ) is a non-identity automorphism carrying vacua and hosted algebras along | **PROVED** | PROOF-crystal-hosts-quaternion |
| S₃ action, order 3 | `rotAut3` ρ (ρ³ = id, ρℓ = ℓ) is an automorphism carrying a universe's crystal, membership and hosted algebra along | **PROVED** | PROOF-hosting-equivariant-under-order-three |
| Aut(𝕊) = G₂ × S₃ | Brown's identification, and that `gradeAut` and ρ generate the S₃ | **OPEN** | #639 (e); NOT claimed by either anchor above |

**Reading.** The carrier is theorem-shaped end to end; two facts stay numerical (vacuum topology; ridge dimension), and the 4/8/4 multiplicities are proved at one witness only. "Crystallisation" means **subalgebra selection** (v0.6 addendum §3), never a homomorphism 𝕆 → ℍ: 𝕆 is simple.

## 2. Rule

The eight clauses of the G1 draft (#635, issuecomment-5828899452); substance reproduced, nothing re-derived.

| # | Clause | Tag | Source |
|---|---|---|---|
| P1 Carrier | StateSphere and V as in §1 | **PROVED** | PROOF-substrate-hosting-definition; PROOF-delta-landscape-descent |
| P2 Field | F(s) = −(∇V(s) − ⟪∇V(s), s⟫ s − (∇V(s))₀·1): overdamped descent of V in the N-metric, projected tangent to the sphere and to Im 𝕊. ∇V closed-form; V is Cᵏ for every k; F tangent (StateSphere invariant); F = 0 at every crystal; F ≢ 0 | **PROVED** (the form) | PROOF-rule-gradient-and-tangent-field |
| P3 Dynamics | γ′ = F ∘ γ | **POSTULATE** | `RuleFlow.lean` header "THE RULE IS A POSTULATE"; #635 |
| P4 Existence | integral curves exist through every initial state | **OPEN** | FLAG-rule-flow-open; #635; §2a |
| P5 Consequences | the table below | **PROVED** (conditional) | PR #681, pending merge |
| P6 No merging | the table below | **PROVED** (conditional) | PROOF-rule-flow-finite-time-uniqueness; PROOF-rule-euler-step-injective; PROOF-rule-descent-avoids-zero-divisors |
| P7 Initial ensemble | N's normalised surface measure on StateSphere (horn 1), PERMITTED as MaxEnt with N's geometry as reference, not FORCED | **POSTULATE** | beekeeper ruling 2026-09-05, #473 issuecomment-5555310567 (gloss 5555866101) |
| P8 Protocol β(t) | A quench / B anneal / C ℓ-axis map / hold | **OPEN** | #635 (G1 ruling request); §2b |

**Consequences of the form.** Every row ASSUMES γ is an integral curve of F; P4 is open, so no row asserts a trajectory exists.

| Result | Statement | Tag | Source |
|---|---|---|---|
| Descent | V ∘ γ is monotone non-increasing; d/dt V(γ t) = −N(F(γ t)) | **PROVED** | PROOF-potential-descent-along-rule |
| Gram-invariant ODEs | Ȧ = 4V(2A − 1), Ċ = 4V(2C − 1), Ṗ = 8VP, ḃ₀ = 4Vb₀; Euler identity ⟪∇V, s⟫ = 4V; A + C + b₀² conserved | **PROVED** | PROOF-rule-gram-invariants-ode (PR #681, pending merge) |
| Straight ray | (A − ½, C − ½, P, b₀²) moves on a straight ray through (½, ½, 0, 0), any time parametrisation | **PROVED** | PROOF-rule-descent-straight-ray (PR #681, pending merge) |
| Monotone b₀² | b₀² is non-decreasing along any curve | **PROVED** | PROOF-ell-coefficient-monotone-along-rule (PR #681, pending merge) |
| Conditional endpoint | ADDITIONALLY ASSUMES V(γ t) → 0 and b₀²(γ t) → L: then L = b₀²/(b₀² + √((1 − b₀²)² − V₀)) in the initial data | **PROVED** (conditional) | PROOF-quench-endpoint-closed-form-conditional (PR #681, pending merge) |
| Backward uniqueness | two curves agreeing at one time agree at every earlier time (Grönwall): no finite-time merging | **PROVED** | PROOF-rule-flow-finite-time-uniqueness |
| Euler step injective | s ↦ s + hF(s) is injective on the sphere for hK < 1; the renormalised step the scripts run is proved injective only on level sets of ‖F‖ | **PROVED** | PROOF-rule-euler-step-injective |
| Avoids zero divisors | a forward curve from V < 1 is never a zero divisor, either side, at finite time or in its ω-limit set | **PROVED** | PROOF-rule-descent-avoids-zero-divisors |
| Ensemble mean, A | ⟨b₀²⟩ = E_Haar[B/(B + (1 − B)√(1 − 4κ))] = 0.141587 (quadrature; 10⁷ MC 0.14162 ± 0.00005; RK4/DP45 match the closed form to 10⁻¹¹ per seed); every on-record 0.146 carried a +0.0031 Euler bias | **NUMERICAL** | `analysis/473-kill-attack/attack1_anneal_vs_quench.md` §3, `quench_exact.py`, `quench_rk4.py` |
| Ensemble mean, B | Gibbs e^{−βV}, β → ∞: the Laplace factor (8(1 − b₀²))⁻³ cancels the surface element (1 − b₀²)³; limit round-uniform on the vacuum S²; ⟨b₀²⟩ = 1/3 exactly, approach 1/3 − 0.554 β^{−1/2} | **NUMERICAL** (analytic derivation + quadrature + MCMC; not Lean) | `attack1_anneal_vs_quench.md` §1–§2, `anneal_quadrature.py`, `anneal_mcmc.py`, `hessian_isotropy.py` |
| Ensemble mean, C | iterating (s + ℓ)/‖s + ℓ‖ has attractor ±ℓ, ⟨b₀²⟩ → 1 | **NUMERICAL** | `analysis/473-dirac-probe/flow_big.py` (#629), cited by FLAG-rule-flow-open |

### 2a. Existence of the flow

| Question | Tag | Source |
|---|---|---|
| Do integral curves of F exist, locally or globally? | **OPEN** | FLAG-rule-flow-open; `RuleFlow.lean` ("Local existence is not proved either") |
| Does V(γ t) → 0 along a curve (Łojasiewicz-type convergence)? | **OPEN** | FLAG-rule-flow-open; `RuleFlow.lean` NOT-proved list |
| Is any ensemble average a theorem? | **OPEN** | PR #681 NOT-claimed clause ("0.1416 stays numerical") |

The rows above "Ensemble mean" concern a postulated form and curves hypothesised, not shown, to exist; 0.1416, 1/3 and 1 are not predictions until P4 and P8 are settled.

### 2b. The protocol decision point (G1)

| Option | Protocol on the horn-1 ensemble | ⟨b₀²⟩ | Evidence | Killed if |
|---|---|---|---|---|
| A quench | follow γ′ = F(γ) to V → 0 | 0.1416 | NUMERICAL (per-seed map PROVED conditional, PR #681) | positive-measure seeds with non-vacuum ω-limit, or endpoint law ≠ the closed-form pushforward |
| B anneal | Gibbs e^{−βV}, β → ∞ | 1/3 | NUMERICAL + analytic, not Lean | Laplace cancellation failing on a stratum; β(t) stalling off {V = 0} on positive measure |
| C ℓ-axis map | iterate (s + ℓ)/‖s + ℓ‖ | 1 | NUMERICAL | any observed \|b₀\| < 1 |

The choice (A, B, C, or hold) is the beekeeper's: **OPEN** (#635); kills K1–K4 are in the G1 draft. Dependencies: the G2 rewrite of AXIOM-1's kill clause (#668, trigger #647) lands before or with any `POST-…` encode, the current clause being defective both ways (**OPEN**, #668); and one universe supplies one b₀, so A vs B is distributional while C dies on one observation (§5).

## 3. Hosting

| Item | Statement | Tag | Source |
|---|---|---|---|
| Definition | a `Universe` = a crystal s ∈ UniverseSpace plus `hosted`, the subalgebra {1, s, ℓ} generates; `hosted` ⊆ span{1, ℓ, U, ℓU} (a quaternion subalgebra), a proper part of 𝕊; at ±ℓ the hosted algebra is exactly span{1, ℓ} ≅ ℂ | **PROVED** | PROOF-substrate-hosting-definition |
| Crystal witness | every crystal s has a direction u with every word in {1, s, ℓ} in span{1, u, ℓ, ℓu}; the ℍ relations hold; the span is exactly 4-dimensional and proper; k = ℓu and k = uℓ span the same 4-space (orientation NOT fixed by the landscape) | **PROVED** | PROOF-crystal-hosts-quaternion |
| Local spectrum | at a crystal s(sx) = −N(s)x for every x, characterising crystals among imaginary s; N(s) the unique eigenvalue; off a crystal the alternator is exactly first order | **PROVED** | PROOF-local-spectrum-at-crystal |
| Equivariance | ℓ-fixing automorphisms (G₂ side), `gradeAut` (ℤ/2) and ρ (order 3) preserve sphere, vacua and hosted algebras | **PROVED** | PROOF-substrate-hosting-definition; PROOF-crystal-hosts-quaternion; PROOF-hosting-equivariant-under-order-three |
| Fails in flight | at every in-flight state the identity s(sx) = −N(s)x fails (¬∀x); on the sphere s ∈ UniverseSpace ⇔ ∀x, s(sx) = −x; InFlight is non-empty | **PROVED** | PROOF-hosting-identity-fails-in-flight |
| Not claimed with it | that no 4-dimensional subalgebra containing {1, s, ℓ} exists in flight; that a hosting bundle's fibre is empty in flight (both WITHDRAWN, Red Team F4) | **OPEN** | NOT-claimed clause of PROOF-hosting-identity-fails-in-flight; no issue |
| Direction u canonical? | uniqueness of u up to sign for a non-pole crystal (`Universe.dir` is a `Classical.choose`) | **OPEN** | hosting definition §6; #634/#639 |
| Observer reading | that the hosted ℍ is "the observer's ℍ" | **OPEN** | POST-observer-associativity (open root, flag-3 split); NOT claimed by any hosting anchor |

Hosting is a definition with coherence theorems; it hosts, it does not derive. "Not yet crystallised" is the theorem that the scalar spectrum fails.

### 3a. Hosting witnesses (AC1(a), (b)) and their transport

| Item | Statement | Tag | Source |
|---|---|---|---|
| S³ H-space | an H-space structure on S³ from Cayley–Dickson multiplication (Cubical Agda, `--safe`) | **PROVED** | PROOF-s3-hspace (`proofs/agda-cubical/S3FromCD.agda`) |
| AC1(a) charge | Skyrmion baryon number is a complete homotopy invariant: ∥S³ → S³∥₂ ≅ ℤ | **PROVED** | PROOF-skyrmion-baryon-complete-invariant (`SkyrmionCharge.agda`) |
| AC1(b) additivity | B(f ⋆ g) = B f + B g under the substrate quaternion product at the concrete S³ H-space | **PROVED** | PROOF-substrate-baryon-additive (`SubstrateCharge.agda`); #607 closed |
| Transport to every crystal | transport of the H-space and charges to the unit sphere of every ℍ_s via ℍ_s ≅ ℍ ("Agda wiring, to do") | **OPEN** | `substrate-hosting-definition-2026-09-07.md` §2 (a), (e); #639 (c), (e); #554 |
| Remaining #595 | Hopfion charge via the quaternionic Hopf map; Derrick/Bogomolny | **OPEN** | #595 |
| Local type-checking | Agda checked in CI only | **OPEN** | #576 |

Correction to the brief this draft was written from: the AC1(a)/(b) witnesses are machine-checked and anchored in this repository (Agda); open are their transport to every ℍ_s, the rest of #595, and local checking. The Lean side cites the Agda side without formalising it (`Hosting.lean` §0).

## 4. Transition state (the in-flight region)

| Item | Statement | Tag | Source |
|---|---|---|---|
| Tangent count | at every s in the set StateSphere, Tangent s := ker(x ↦ (⟪x, s⟫, x₀)) has finrank 14 (a linear subspace, not a manifold tangent space) | **PROVED** | PROOF-in-flight-first-order-data-constrains-at-most-one-direction |
| At most one direction | with g the tangential gradient (g = −F(s), cited from RuleFlow, not a theorem of the file): VNeutral s g has finrank 13 where g ≠ 0 and equals Tangent s (14) where g = 0. V constrains at most one of 14 directions: one where F(s) ≠ 0, none at rest points, i.e. crystals AND the frozen ridge | **PROVED** | PROOF-in-flight-first-order-data-constrains-at-most-one-direction |
| Rule-blind invariants | adding a V-neutral vector to a candidate rule field leaves the sphere, the imaginary part and dV(F) unchanged while changing the rule (a nonzero V-neutral vector exists); any functional of V's level-set topology alone is constant as the rule varies (quench and anneal give the identical object) | **PROVED** | PROOF-level-set-invariants-rule-blind |
| Vacuum sublocale | for continuous V on X the nucleus U ↦ U ⊔ V⁻¹(ℝ∖{0}) is V-natural with fixed frame Ω({V = 0}): the vacuum support with its full topology; no measure, no transport, no clock | **PROVED** | PROOF-vacuum-sublocale-v-natural |
| Sublevel filtration | for V ≥ 0, ⨅_{c>0}{V < c} = interior{V = 0}; a function of V alone; ⊥ under the hypothesis interior{V = 0} = ∅ (true on S¹⁴ by the analytic-zero-set argument, NOT formalised) | **PROVED** (hypothesis form) | PROOF-sublevel-infimum-rule-independent |
| "13 at any in-flight state" | FALSE, not claimed: on the ridge the count is 14 | **PROVED** (the correction) | same anchor (Red Team M1) |
| Ext¹ clause (b) "identically zero" | WITHDRAWN: HH²(ℍ, ℍ) = 0 rigidifies ℍ's product, but ℍ ↪ 𝕆 has 8-dimensional moduli T(G₂/SO(4)) | **OPEN** | PROOF-level-set-invariants-rule-blind (Red Team M3); CONJ-condensed-math-for-transition-state (marginal) |
| Positive in-flight account | what the in-flight region IS as a space with configurations (hosting clause (c)'s "pointless" half); which of {orbit space of the rule, a locale/condensed object, a limit of finite approximations} is a definition | **OPEN** | **no issue** (named in the hosting definition §5 Q3 and the #473 plan §4; nothing owns it) |

**Stated honestly.** Everything proved here is negative or structural: V sees at most one of fourteen directions, so no functional of its level sets can select the rule. No positive account of the in-flight region is on record and no issue tracks one; the negatives say only that the potential alone does not describe its dynamics.

## 5. Prediction candidate (AC2)

| Item | Statement | Tag | Source |
|---|---|---|---|
| Route status | the locale/condensed forcing route is OPEN research again (ruling 2026-09-25); the KILLED record is kept as history, superseded, marginal | **OPEN** | FLAG-locale-forcing-route-reopened; KILLED-locale-forcing-route |
| Its kill | Prop 13(b) with the honest class, quoted below | **OPEN** | FLAG-locale-forcing-route-reopened; v0.6 addendum §6 |
| Spatial first link | Ω(X) ≅ Ω(condensedSetToTopCat X̲) for compactly generated X, ℝ included | **PROVED** | PROOF-spatial-first-link-condensed-locale |
| Profinite structure inert | the CD index tower's dual Cantor group acts by sign automorphisms; every continuous profinite action on 𝕊 has finite image (Aut(𝕊) a compact Lie group); its discrete measure gives ⟨b₀²⟩ = 1/15 | **NUMERICAL** (numerical + argument, not Lean) | `analysis/473-kill-attack/attack4_dual_cantor_group.md` |
| b₀ observable | one candidate mapping of b₀ to at least two measured constants, with its kill; "landscape, not identification" kept | **OPEN** | #637 (G3, pending) |
| One or many | whether the theory admits domains; effect on distributional predictions | **OPEN** | #638 |
| Composite rule | no multi-particle composition rule in the hosted layer; Efimov data force one | **OPEN** | FLAG-hosted-composite-rule-open; #669, #672 |

What would reverse the reopened route, quoted from the v0.6 addendum §6:

> A mechanism that supplies **both** a reference measure on each level set of V **and** a transport between level sets from topological or measure-theoretic data alone. Attack 3 proves the frame supplies neither; attack 5 proves level-set invariants are rule-blind; attack 4 proves profinite structure is inert. So the class is **metric-carrying (enriched) locales**, and any such candidate must show that the metric it carries is not simply N re-labelled (Prop 8's relocation test). Until then the route is open, not validated.

No AC2 candidate is on record: ⟨b₀²⟩ depends on the protocol (§2b) and is a decision, not a prediction; an observable for b₀ is owed (#637), A vs B is distributional (#638).

## 6. Kills and reversals

The five attacks of 2026-09-24, quoted (condensed) from `docs/foundations/473-ac1-v0.6-addendum-2026-09-25.md` §2, the record.

| # | Attack | Leg | Outcome (addendum wording) | Tag |
|---|---|---|---|---|
| 1 | Gibbs β→∞ exact; quench, three integrators | Prop 9 | "held on the anneal (1/3 exactly …); missed on the quench: exact 0.1416 … a +0.0031 renormalised-Euler (h = 0.02) bias" | **NUMERICAL** (Lean target (i) = PR #681) |
| 2 | words in (s, ℓ, z), z over the 84 canonical zero divisors | Prop 16 | "mis-posed as a reachability claim — the kill FIRED literally … the preimage of the vacuum has codimension ≥ 4 … '0 hits' was non-discriminating. What survives is the dynamical negative: no positive-measure steering onto the vacuum and no non-pole vacuum attractor" | **NUMERICAL** (exact structure = PR #682) |
| 3 | V-natural frame endomorphisms and valuations | Prop 12 | "the driver's sealed sentence is FALSE (Prop 12's own claim is CONFIRMED) … Kill not reversed: the nucleus … no clock, identical for both rules" | **PROVED** (the two LocaleDynamics anchors of §4) |
| 4 | the CD index group's Pontryagin dual | Prop 10′ | "held; and Prop 10′ has a wording gap … the object exists … but is inert" | **NUMERICAL** |
| 5 | condensed Ext¹ as formation rate | Prop 13(b) | "rule-independent by construction, proved … (a) ill-typed …; (b) ill-posed …; (c) no clock" | **PROVED** (the two TransitionState anchors of §4) |

| Consequence | Statement | Tag | Source |
|---|---|---|---|
| The ruling | "killed" was not proof-backed; two supporting sentences fell, neither conclusion fell; the kill's conclusion (no topological or measure-theoretic mechanism supplies the rule) was not reversed | **OPEN** | v0.6 addendum §0; FLAG-locale-forcing-route-reopened |
| Corrections of record | quench 0.146 → 0.1416; anneal "≈ 1/3" → "= 1/3 exactly"; Prop 10′ reworded; Prop 12's parenthesis replaced; Prop 16 qualified; vocabulary firewall | **NUMERICAL** | v0.6 addendum §3 |
| The lesson on kills | attack 2's kill "fired literally" on a codimension-≥4 hit, "'0 hits' was non-discriminating"; the hosting definition's clause (b) kill: "Until then this kill cannot fire — recorded as such, not as a pass". Kills are since stated in positive-measure form (G1 §3, G2) | **OPEN** (a process rule) | v0.6 addendum §2 row 2; `substrate-hosting-definition-2026-09-07.md` §4; #668 |

The drafting direction phrased the lesson as "a test that passes only because it structurally cannot fire is not a kill that held". That sentence is not verbatim in any file or comment searched (`docs/`, `analysis/`, threads #473, #635, #675, #676, #679, #684): its source is qbp-architecture on the live-test bridge during the attack-2 review (2026-09-25), a bridge message and not a repo record, so it is quoted here as a reviewer's sentence, not a ruling. The wording on record is the addendum's.

## 7. Ledger and issue map

| § | PROVED (anchor ids) | NUMERICAL (analysis files) | POSTULATE | OPEN (issues) |
|---|---|---|---|---|
| 1 Carrier | PROOF-substrate-hosting-definition; PROOF-normed-division-tower-existence; PROOF-delta-landscape-descent; PROOF-potential-bounded-by-normForm-sq-frozen-max; PROOF-alternator-vanishes-iff-commute; PROOF-vacuum-parametrisation; PROOF-zero-divisors-sit-at-potential-max; PROOF-42zd; PROOF-seam-zd-witness-kernel-four; PROOF-seam-zd-witness-kernels-coincide; PROOF-seam-zd-witness-kernel-not-subalgebra; PROOF-crystal-hosts-quaternion; PROOF-hosting-equivariant-under-order-three; PR #682, pending merge: PROOF-seam-zd-gram-spectrum-4-8-4, PROOF-seam-top-plane-on-frozen-ridge, PROOF-seam-right-gram-equals-left, PROOF-basis-pair-gram-uniform-bounds | `analysis/473-dirac-probe/orbit_space.py`, `lmaps_check.py`, `aut_s3.py`; ridge dimension (unsourced) | — | #639 (e); converse V = N² ⇒ zero divisor (no issue) |
| 2 Rule | PROOF-rule-gradient-and-tangent-field; PROOF-potential-descent-along-rule; PROOF-rule-flow-finite-time-uniqueness; PROOF-rule-euler-step-injective; PROOF-rule-descent-avoids-zero-divisors; PR #681, pending merge: PROOF-rule-gram-invariants-ode, PROOF-rule-descent-straight-ray, PROOF-ell-coefficient-monotone-along-rule, PROOF-quench-endpoint-closed-form-conditional | `analysis/473-kill-attack/attack1_anneal_vs_quench.md`, `quench_exact.py`, `quench_rk4.py`, `anneal_quadrature.py`, `anneal_mcmc.py`, `hessian_isotropy.py`; `analysis/473-dirac-probe/flow_big.py` | P3 (#635); P7 (horn-1 ruling) | P4: FLAG-rule-flow-open, #635; P8: #635; AXIOM-1 kill clause: #668, #647 |
| 3 Hosting | PROOF-substrate-hosting-definition; PROOF-crystal-hosts-quaternion; PROOF-local-spectrum-at-crystal; PROOF-hosting-identity-fails-in-flight; PROOF-hosting-equivariant-under-order-three | — | — | #634/#639 (u canonical); POST-observer-associativity |
| 3a Witnesses | PROOF-s3-hspace; PROOF-skyrmion-baryon-complete-invariant; PROOF-substrate-baryon-additive | — | — | #639 (c)/(e); #595; #576; #554 |
| 4 Transition state | PROOF-in-flight-first-order-data-constrains-at-most-one-direction; PROOF-level-set-invariants-rule-blind; PROOF-vacuum-sublocale-v-natural; PROOF-sublevel-infimum-rule-independent | — | — | positive account: **no issue**; CONJ-condensed-math-for-transition-state |
| 5 Prediction | PROOF-spatial-first-link-condensed-locale | `analysis/473-kill-attack/attack4_dual_cantor_group.md` | — | FLAG-locale-forcing-route-reopened; KILLED-locale-forcing-route (history); #637; #638; FLAG-hosted-composite-rule-open, #669, #672 |
| 6 Kills | (attacks 3, 5: the §4 anchors) | `analysis/473-kill-attack/attack{1,2,3,4,5}_*.md` | — | #668; #683 |
| Not in v0.1 | — | — | — | #661; #596/#600; #636; FLAG-seam-dynamics-open |

## 8. What v0.2 would need

| Item | What has to exist | Owner |
|---|---|---|
| G1 ruling encoded | A / B / C / hold ruled on #635; P1–P8 encoded as `POST-…` with the chosen kills, confined writer, Tier 3 | #635; beekeeper |
| G2 landed | AXIOM-1 kill_condition[0] in positive-measure form, ratified, beekeeper's go; before or with the G1 encode | #668 (+ #647) |
| G5 merged | PR #681 and PR #682 on master, so the eight "pending merge" citations resolve | #684 G5 |
| Positive in-flight account | a definition (not a description) of the in-flight region consistent with §4's negatives; needs an issue first | none yet |
| AC2 candidate | a Prop 13(b)-class mechanism passing the relocation test, or a b₀ observable with a distributional statement | FLAG-locale-forcing-route-reopened; #637; #638 |
| Existence | local existence of integral curves and convergence V → 0, discharging §2's conditionals | FLAG-rule-flow-open; #635 |
| Carrier numerics into Lean | vacuum topology; ridge dimension | #634 |

Nothing here is FORCED; the substrate stays PERMITTED (since 2026-06-01): a theorem-shaped carrier, a postulated rule with proved consequences and no proved existence, witnesses at the model S³ without transport, a transition state described only negatively, no prediction.
