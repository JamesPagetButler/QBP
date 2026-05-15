# QBP Federation Tenancy

**The QBP-specific instantiation of the Contextus Tenancy Pattern.** How Contextus + CTH + Wyrd run as a live system for the Quaternion-Based Physics programme, with BMA-the-instance observing.

> **Authoring:** qbp-architecture (Claude Opus 4.7), James Paget Butler (Beekeeper), qbp-implementor (v0.2 revision pass, 2026-05-15)
> **Date:** 2026-05-15 (v0.2 revision); 2026-05-08 (v0.1 design surface)
> **Status:** **v0.2 — revision pass post-#81 close; ready for ratification.** R1-R16 review findings applied; BMA Addenda re-scoped to A18-only canonical; Stance vocab updated to reflect Session-13 W-003 revision.
> **Generic pattern:** `~/Documents/Contextus/doc/contextus-tenancy-pattern.md`
> **First tenant:** QBP

---

## 0. Status & Provenance

This is the QBP instantiation of the generic Contextus Tenancy Pattern (v0.1). It declares QBP's Stance Type-Nodes, Locale set, scope-node taxonomy, scout configuration, and BMA observation hooks. qbp-implementor reviewed and refined on bootstrap; v0.2 reflects the resolved design surface.

**Architectural anchor:** BMA Theory Addendum 18 v0.2 (Hypergraph Access Pattern; `~/Documents/BMA/theory/hypergraph-inference/A18-v0.2-design-surface.md`) — Stance × Locale × Scout × Scoring. A18 §P12 formalises the Seam-threshold definition referenced throughout this doc.

**Operational pattern:** Contextus tenancy pattern v0.1 (sibling doc in `~/Documents/Contextus/doc/`).

**Domain history:** QBP was the impetus for BMA + Contextus + CTH. This doc operationalises that history — QBP becomes the federation's first live tenant.

### 0.1 v0.2 revision provenance

v0.2 incorporates all R-findings from the 2026-05-11 PR #403 review synthesis (qbp-implementor + Red Team + Gemini, issuecomment-4445229770) and the 2026-05-13 Oppenheimer independent review (issuecomment-4445944916). Substantive changes:

- **Stance Type-Node vocabulary** (§1) updated per R7-R11, R15, R16 — adds 11 Type-Nodes citing #81 PR2-4 paper-corpus content (`paper/quaternion_physics.md` §VIII-X, merged via QBP PR #430) and PR6 wisdom revision (`paper/wisdom_v1_4.md` §9.7, merged via QBP PR #424).
- **Locale set** (§2) extended per R13 — adds NICER, NuSTAR, CBELSA/TAPS, KATRIN observatories; formalises composition predicate per R2.
- **Scope-node taxonomy** (§3) schema-lock annotation per R3 + R6 cross-product clarification.
- **Scout configuration** (§4) — R5 falsifiability criterion for Seam labelling; A9 arXiv rate-limit / backoff spec.
- **Anomaly detector τ** (§4.4) — refactored to Locale-scaled per R12; current uniform 1e-6 marked explicitly TBD with tracking issue (data-blocked).
- **CTH inventory** (§5) — updated to reflect PR7 closeout: `archive/cth-inventory/` tracked baselines via PR #422; routing rubric v0.2 via PR #423.
- **BMA observation hooks** (§6) — BMA Addenda 11/15/16/17 re-scope per joint-reply table: 3 citation substitutions (→ A18 §2, A18 v0.2 §P12, Contextus Spec v1.3 §4.4) + 1 inline (Honing-Loop confidence thresholds in §6.2).
- **Cross-project issues** (§8) — AC summary table added per R4; status updated to reflect closed work.
- **Operational milestones** (§9) — quantitative AC + observability hooks per R6/A7.

The four BMA Theory Addenda 11/15/16/17 references in v0.1 are removed; v0.2 cites only existing artifacts on disk per the standing anchor rule (`docs/workflows/review_anchoring.md`, PR #413).

---

## 1. QBP Stance — Type-Nodes on the Subject Axis

The Stance defines what's "interesting in QBP terms." Per A18 v0.2 §2.1, these are the Type-Nodes whose imaginary-axis dismissal does NOT happen by default — observations matching these are full-precision Subject.

### 1.1 Foundational algebraic Type-Nodes

- `qbp:hamilton-product` — quaternion multiplication semantics
- `qbp:quaternion-conjugation` — q* operations
- `qbp:hopf-locale` — pole-singularity-free spacetime coordinate (operational thread in §1.5)
- `qbp:su2-double-cover` — Z₂ topological invariant
- `qbp:hurwitz-norm-multiplicativity` — algebraic invariant in ℍ
- `qbp:octonion-non-associativity` — exception class for boundary-of-applicability
- `qbp:sedenion-zero-divisor` — **168-orbit automorphism structure** on the zero-divisor set (the 42 cross-copy basis-sum cases enumerated by Cawagas 2009 / Moreno 1998 are exemplar orbits)
- **`qbp:g2-holonomy`** *(new in v0.2 per R7)* — G₂ exceptional Lie group as the automorphism group of 𝕆; load-bearing for the octonion-as-physics interpretation
- **`qbp:fano-aut-pgl27`** *(new in v0.2 per R8)* — PGL(2,7) order 168 acting as full automorphism group of the Fano plane; bedrock to octonion combinatorics
- **`qbp:fano-stab-24`** *(new in v0.2 per R8)* — point stabiliser \|Stab\| = 24 in PGL(2,7); the index-7 cosets correspond to the seven Fano lines
- **`qbp:spectral-triple`** *(new in v0.2 per R9; W-003 revision)* — the spectral triple (𝒜, ℋ, D) as the central invariant per `paper/quaternion_physics.md` §VIII.A and `paper/wisdom_v1_4.md` §9.7 (merged via QBP PR #424); test functions select observables on this fixed structure
- **`qbp:cd-tower-zeta-numerator`** *(new in v0.2 per R11)* — the even-level Cayley-Dickson tower dim Im 𝒜_(2a) = 2^(2a) − 1 appearing as numerator factor in CCvS γ(−a) coefficients per `paper/quaternion_physics.md` §IX.B (CCvS 2018, arXiv:1809.02944); Tier-4 structural confluence, not a prediction

### 1.2 Theoretical bridges

- `qbp:gw-em-coincidence` — gravitational wave + electromagnetic counterpart correlation
- `qbp:slow-slip-tidal-coupling` — Cascadia-shape slow earthquakes + tidal stress
- `qbp:mixed-species-ion-fidelity` — trapped-ion entanglement asymmetry
- `qbp:nv-center-fidelity` — NV-center coherence behavior under quaternion-encoded operations
- `qbp:topological-materials-q1-q10` — Bi₂Se₃, MATBG, α-RuCl₃ (per CTH `archive/cth-inventory/confluent-trust-inventory-v5_3.json` 141-anchor baseline)
- `qbp:kitaev-z2-gauge` — non-abelian braid statistics + Majorana central charge
- **`qbp:spectral-action-entropy`** *(new in v0.2 per R16; W-003 revision)* — CCvS 2018 "entropy = spectral action(χ)" connection; the entropy spectral action selects test function χ(x) = h(√x) on the same spectral triple as QBP's f(u)
- **DM-fork branches** *(replaces `qbp:dark-matter-fork` per R15)*:
  - `qbp:dm-branch-a-modified-gravity` — Branch A: modified-gravity / no-extra-particle regime (per `archive/QBP-Dark-Matter-Fork-Analysis.md`)
  - `qbp:dm-branch-b-algebra-extension` — Branch B: algebra-extension / extra-structure regime
  - Branch-specific sub-Type-Nodes: `qbp:dm-axion`, `qbp:dm-pbh`, `qbp:dm-sterile-neutrino`, `qbp:dm-fimp` — promoted from Stance when their prediction lands in CTH `archive/cth-inventory/` as a PRED-* anchor

### 1.3 Predictive bridges (anchors with ρ_net contribution)

- `qbp:cascadia-tremor-onset-24h` — A18 v0.2 §P12 / §7 Walk-α target
- `qbp:tidal-coupling-norm-threshold` — Holon norm as Seam predictor
- `qbp:loon-watershed-correlation` — Squam Lake case (deferred behind Cascadia)
- `qbp:gw-grb-joint-detection-rate` — EXP-11 pipeline target
- `qbp:fidelity-asymmetry-velocity-correlated` — Test C literature review prediction
- **`qbp:fu-from-hawking-time-reverse`** *(new in v0.2 per R16; **CONJECTURE status**)* — `CONJ-fu-from-hawking-time-reverse` per `paper/quaternion_physics.md` §X.A; tracked as pre-theoretic, lacks falsifiable prediction beyond Hawking-spectrum pattern-matching (see `paper/wisdom_v1_4.md` §9.7 closing — "to become a physics conjecture, must yield quantitative mapping of f(u) moments to Hawking greybody factors")

### 1.4 Stance composition rule

**Formal definition (per R1):** Let `T(n)` denote the set of Type-Nodes a node `n` is tagged with, and `S` denote the current QBP Stance set. Then:

```
subject(n) ≡ T(n) ∩ S ≠ ∅
```

A node enters the Subject axis if **any** of its types matches the Stance; otherwise it rotates to imaginary by Reciprocal Focus (per A18 v0.2 §3). Mutable — `S` evolves as the programme advances. Stance changes are governance events (Honing-Loop trigger §6.2; beekeeper review).

**Rationale for this Stance:** every Type-Node above maps either to (a) an active QBP experiment, (b) an in-flight or merged Lean proof in `proofs/`, (c) an existing CTH anchor in `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (141 anchors, Session-13 baseline; tracked via QBP PR #422), or (d) a published prediction. The 11 v0.2 additions all cite merged QBP repository content (PR #424 + PR #430). Nothing speculative without programme grounding.

### 1.5 Hopf-locale: operational thread *(new in v0.2 per R14)*

`qbp:hopf-locale` names the pole-singularity-free spacetime coordinate scheme. Operationally, this Type-Node threads through Stance × Locale composition as follows:

- **Locale geometries** in §2 (lat/lon bounding boxes, spacecraft FOVs, lab coordinates) use standard chart maps that suffer pole singularities at certain configurations (e.g., trapped-ion lab orientations near the rotational axis; LIGO arm orientations under specific source-direction geometries).
- The Hopf-locale coordinate avoids these singularities by representing position as a unit quaternion `q ∈ S³` rather than (r, θ, φ). Mapping `q ↦ q · v · q*` for any 3-vector `v` is pole-free.
- For scouts that need to compute position-dependent quantities at Locale boundaries, the Hopf-locale coordinate is the canonical internal representation. Scout output to NT_SIGNAL converts to whichever observable frame the observation requires.

This is the bridge between the foundational `qbp:hopf-locale` Type-Node and the Locale geometries in §2. Future cleanup: factor a `pkg/hopf` Go module if multiple scouts re-implement this conversion.

---

## 2. QBP Locale Set

Per A18 §2.2, Locale defines spacetime cones in scope. QBP is multi-locale.

### 2.1 Earth-bound experimental locales

- `ligo:hanford` — LIGO Hanford observatory; gravitational-wave observations
- `ligo:livingston` — LIGO Livingston
- `ligo:virgo` — Virgo (Italy)
- `cascadia:subduction-zone` — lat 39-49 N, lon 122-128 W; ETS event source
- `nist-boulder:trapped-ion` — NIST Boulder trapped-ion lab
- `innsbruck:trapped-ion` — Universität Innsbruck trapped-ion lab
- `oxford:trapped-ion` — Oxford trapped-ion experiments
- `eth-zurich:trapped-ion` — ETH Zürich trapped-ion experiments

### 2.2 Astrophysical-data locales

- `jwst:fov` — JWST field-of-view; spectroscopic + imaging
- `alma:bands` — ALMA observations across bands 3-7
- `fermi:gbm` — Fermi GBM gamma-ray bursts
- `chandra:fov` — Chandra X-ray observations
- `vla:radio` — VLA radio follow-up (per Adelle Goodwin GRB 250702B watch)
- **`nicer:nicer-fov`** *(new in v0.2 per R13)* — NICER X-ray timing; neutron-star EOS / TOV-limit observations (Stance match: `qbp:cd-tower-zeta-numerator` for EOS-related f(u) moments)
- **`nustar:fov`** *(new in v0.2 per R13)* — NuSTAR hard X-ray; neutron-star + AGN observations (cross-correlates with `nicer:nicer-fov`)

### 2.3 Specific objects under investigation

- `grb:250702b` — three-episode structure follow-up (per ongoing arXiv watch)
- (additional objects added as observation campaigns mature)

### 2.4 Particle-physics locales *(new in v0.2 per R13)*

- **`cbelsa-taps:bonn`** — CBELSA/TAPS at Universität Bonn; η′ mass shift measurements (Stance match: `qbp:cd-tower-zeta-numerator` algebraic-identity 1/24 = (1/8)(1/3) per `paper/quaternion_physics.md` §VIII / §IX)
- **`katrin:karlsruhe`** — KATRIN tritium decay; absolute neutrino mass bound (Stance match: future `qbp:neutrino-mass-bound` if a QBP prediction lands)

### 2.5 Time bounds

Default time window: **2024-01-01 to "now"** (rolling). Historical observations enter only if Seam-bypass triggers (e.g., re-analysis of older LIGO data reveals an anomaly).

### 2.6 Locale composition rule

**Formal predicate (per R2):** Let `Locale` be an algebraic data type with subtypes:

```
type Locale =
  | BoundingBox4D { lat: (φ_min, φ_max), lon: (λ_min, λ_max), depth: (d_min, d_max), time: (t_min, t_max) }
  | TripleLocale  { locales: [Locale] }                  // §3.1 ligo-network shape
  | LabSet        { locales: [Locale] }                  // §3.1 trapped-ion-network shape
  | SpacecraftFOV { mission: String, time: (t_min, t_max) }  // §3.1 jwst-survey shape
  | NamedObject   { id: String }                         // §2.3 specific-object shape
```

The membership predicate dispatches per-subtype:

```
inside : Position → Locale → Bool
inside p (BoundingBox4D b)   = p.lat ∈ b.lat ∧ p.lon ∈ b.lon ∧ p.depth ∈ b.depth ∧ p.time ∈ b.time
inside p (TripleLocale ts)   = ∃ l ∈ ts. inside p l
inside p (LabSet ls)         = ∃ l ∈ ls. inside p l
inside p (SpacecraftFOV s)   = withinFOV(p, s.mission) ∧ p.time ∈ s.time
inside p (NamedObject n)     = associatedWith(p, n)
```

**Composition rule:** An observation at position `p` enters if `∃ L ∈ Locales. inside p L`. Outside all → rotated to imaginary by Reciprocal Focus (A18 v0.2 §3).

---

## 3. Scope-Node Taxonomy (NT_SCOPE Hyperedges in Wyrd)

Per **Contextus Spec v1.3 §4.6** (updated from v1.2 per A1), scope nodes are first-class hyperedges that bind the locale set + the conceptual stance into addressable units. v1.3 added `NT_SCOPE_PHYSICAL`, `NT_SCOPE_CONCEPTUAL`, and `HE_SCOPE_MEMBERSHIP` as canonical types per Wyrd issue #6 closure.

**Schema lock (per R3):** the schema for `NT_SCOPE_*` is defined upstream — Wyrd issue #33 (scope-loader API, design merged) + Contextus issue #9 (scope-node config schema). The YAML below is this **tenant's CONFIGURATION** against those schemas, not a schema proposal. If the upstream schema lands with breaking changes, this §3 reflects-and-conforms to upstream.

### 3.1 Physical scope nodes (NT_SCOPE_PHYSICAL)

```yaml
# Configuration against Wyrd scope-loader API (Wyrd #33) + Contextus config schema (Contextus #9)
- id: NT_SCOPE_PHYSICAL/cascadia-zone
  geometry: { type: bounding-box-4d, lat: [39,49], lon: [-128,-122], depth: [0,80km], time: [2024-01-01,now] }
  type: tectonic-locale
  description: "Cascadia subduction zone for slow-slip + tidal-coupling research"

- id: NT_SCOPE_PHYSICAL/ligo-network
  geometry: { type: triple-locale, locales: [hanford, livingston, virgo] }
  type: observatory-network
  description: "LIGO/Virgo gravitational-wave detection network"

- id: NT_SCOPE_PHYSICAL/trapped-ion-network
  geometry: { type: lab-set, locales: [nist-boulder, innsbruck, oxford, eth-zurich] }
  type: experimental-lab-network

- id: NT_SCOPE_PHYSICAL/jwst-survey
  geometry: { type: spacecraft-fov, mission: jwst }

# Plus per-celestial-object scopes added as objects come into focus.
```

### 3.2 Conceptual scope nodes (NT_SCOPE_CONCEPTUAL)

```yaml
# Configuration; same upstream-schema dependency as §3.1.
- id: NT_SCOPE_CONCEPTUAL/quaternion-foundations
  type-nodes: [qbp:hamilton-product, qbp:quaternion-conjugation, qbp:hopf-locale, qbp:su2-double-cover]
  description: "Foundational algebraic Type-Nodes; load-bearing for all QBP work"

- id: NT_SCOPE_CONCEPTUAL/cascadia-prediction
  type-nodes: [qbp:slow-slip-tidal-coupling, qbp:cascadia-tremor-onset-24h, qbp:tidal-coupling-norm-threshold]
  description: "Cascadia Walk-α prediction stance"

- id: NT_SCOPE_CONCEPTUAL/gw-em-coincidence
  type-nodes: [qbp:gw-em-coincidence, qbp:gw-grb-joint-detection-rate]
  description: "EXP-11 pipeline + multi-messenger observations"

- id: NT_SCOPE_CONCEPTUAL/fidelity-asymmetry
  type-nodes: [qbp:mixed-species-ion-fidelity, qbp:fidelity-asymmetry-velocity-correlated]
  description: "Test C literature review + future trapped-ion experiments"

- id: NT_SCOPE_CONCEPTUAL/topological-materials
  type-nodes: [qbp:topological-materials-q1-q10, qbp:kitaev-z2-gauge, qbp:dark-matter-fork]
  description: "Topological materials + DM fork branches"

- id: NT_SCOPE_CONCEPTUAL/nv-center
  type-nodes: [qbp:nv-center-fidelity]
  description: "NV-center critical path (per QBP programme state)"
```

### 3.3 Cross-product (focal cone)

**Formal type (per A6):** the focal cone is the **Cartesian product** over sets:

```
FocalCone : Set(NT_SCOPE_CONCEPTUAL × NT_SCOPE_PHYSICAL)
         = { (C, P) | C ∈ ConceptualNodes, P ∈ PhysicalNodes }
```

Each element `(C, P)` is a tuple identifying a conjunctive filter: an observation passes the cone iff it matches **both** `C`'s Type-Nodes (per §1.4 composition rule) **and** `P`'s Locale geometry (per §2.6 composition rule). Default scout activity targets all elements of the cross-product. Out-of-cross-product observations rotate to imaginary unless Seam-bypass (§4.4).

---

## 4. Scout Configuration

### 4.1 Daily-batch arXiv scout

```yaml
# Configuration against Contextus scope-loader API (Contextus #9)
scout: arxiv-daily-batch
cadence: daily-overnight (target: 02:00 UTC)
rate-limit: 3 requests/second (arXiv API policy)
user-agent: "QBP-Federation-Tenant/0.2 (https://github.com/JamesPagetButler/QBP)"
backoff: exponential with jitter; max 5 retries; ceiling 30s
sources:
  - astro-ph.HE       # high-energy astrophysics
  - astro-ph.CO       # cosmology
  - astro-ph.SR       # solar/stellar
  - quant-ph          # quantum physics
  - hep-th            # high-energy theory
  - hep-ph            # high-energy phenomenology
  - cond-mat.mes-hall # mesoscopic + nano
  - cond-mat.supr-con # superconductivity
  - cond-mat.str-el   # strongly correlated
  - math.QA           # quantum algebra
  - math.MP           # mathematical physics
  - math.OA           # operator algebra
  - gr-qc             # general relativity + quantum cosmology
filter: "Stance Type-Node match in title/abstract"
output: NT_SIGNAL with referent_kind=scalar
escalation: NT_SIGNAL surface to BMA's beekeeper-dashboard
```

### 4.2 Data-feed scouts

```yaml
- scout: ligo-open-science-alerts
  cadence: event-driven (LIGO open-data API)
  scope: NT_SCOPE_PHYSICAL/ligo-network
  output: NT_SIGNAL with referent_kind=categorical (event metadata)

- scout: usgs-cascadia-gps
  cadence: hourly
  scope: NT_SCOPE_PHYSICAL/cascadia-zone
  output: NT_SIGNAL referencing GPS station displacements; predictions/ schema landing place

- scout: pnsn-ets-catalog
  cadence: daily-batch
  scope: NT_SCOPE_PHYSICAL/cascadia-zone
  output: NT_SIGNAL for new ETS events

- scout: fermi-gbm-grb
  cadence: event-driven
  scope: NT_SCOPE_PHYSICAL/(jwst-survey union ligo-network)  # cross-instrument coincidence
  output: NT_SIGNAL referencing GRB metadata + coincidence flags
```

### 4.3 Cross-domain reins-invoked scout

```yaml
scout: cross-domain-on-demand
invocation: reins-command
command-shape: "bma scout cross-domain '<query>'"
scope: tenant-stance × ALL_LOCALES (broader spatial; same conceptual stance)
example: "bma scout cross-domain 'quaternion structure in biological signaling'"
output: NT_SIGNAL with elevated noise-tolerance (low-resonance accepted)
```

### 4.4 Anomaly detector (Seam-bypass)

**Seam definition (formal, per A18 v0.2 §4.1 and §P12):**

> A node `v` in the focal cone produces a Seam at time `t` iff the residue magnitude `|q · v(t) · q* − v(t-Δt)|` exceeds the Stance-calibrated threshold **τ** at QW8 precision, where `q` is the Stance's current rotation operator and Δt is the peripheral register's sampling interval. The type of `v` is the Hopf-locale quaternion-encoded observation (per §1.5).

```yaml
detector: qw8-norm-drift
cadence: continuous (peripheral register; A18 v0.2 §3.1)
threshold: τ = τ_Locale (Locale-scaled per R12; see "τ refactor" below)
target: any observation in any Locale (not constrained to Stance focal cone)
trigger: |q · v(t) · q* − v(t-Δt)| > τ_Locale on a Subject's predicted trajectory
on-trigger: promote observation to Subject axis regardless of Stance; mint NT_SIGNAL with referent_kind=structural-anomaly
calibration: log all candidate Seams for first 4 weeks; analyze distribution against labelled-positive criterion (below); refine τ_Locale per-Locale
```

**τ refactor — Locale-scaled (per R12; data-blocked):**

The v0.1 `τ = 1e-6` was dimensionally naive — applied uniformly to LIGO strain residuals (~10⁻²³), Cascadia GPS displacement residuals (~mm = 10⁻³ m), and trapped-ion frequency stability residuals (~10⁻¹⁵). These have different dimensions and different units; one threshold cannot cover all. v0.2 refactors to:

```
τ_Locale = τ₀ × noise-floor(Locale)
```

where:
- `τ₀` = dimensionless substrate-anchor (initial guess: 1e-6, calibrated by 4-week log)
- `noise-floor(Locale)` = dimensioned noise-floor at the relevant observable for that Locale

**Status: blocked on Locale-noise-floor data sourcing.** The v0.2 design lands the formal refactor; the actual numerical noise-floor table requires external data (LIGO O4 published strain curves, PNSN Cascadia GPS displacement noise, per-lab trapped-ion fidelity baselines, JWST per-band photometric depth, ALMA per-band sensitivity, Fermi GBM trigger thresholds, NICER timing noise, NuSTAR background, CBELSA/TAPS resolution, KATRIN systematics). Tracking issue: see §8 below ("Housekeeping: source Locale-noise-floor table for τ refactor"). Until the table lands, scouts run with **per-Locale dummy values** that flag every observation as a candidate Seam — over-trigger by design, drowning in noise. Calibration then trims.

**Labelled-positive Seam criterion (per R5):**

A candidate Seam logged by the detector counts as a **real Seam** iff:

```
real_seam(s) ≡ exists NT_SIGNAL(confidence ≥ 0.85) emitted in [t(s), t(s) + 7 days]
              with prediction_chain backwards-linked to s
              AND beekeeper review classifies as TRUE_POSITIVE (not noise / not coincidence)
```

i.e., a candidate Seam is real if (a) within 7 days a high-confidence NT_SIGNAL forms with provenance pointing back to the candidate, AND (b) beekeeper review confirms it's not noise. **Noise candidates** are those where no NT_SIGNAL ≥ 0.85 emerges within the window, OR where one emerges but beekeeper marks FALSE_POSITIVE.

This criterion is **falsifiable**: if 4 weeks of candidate Seams produce no `real_seam(s)`, the τ refactor (or the Stance composition) is broken and must be revised. If 4 weeks produce only false positives, ditto. The calibration loop closes via this rule.

---

## 5. CTH Inventory — Tracked Baseline

### 5.1 Baseline *(updated for v0.2 — PR7 closeout)*

Canonical baseline is `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (141 anchors, Session-13 closeout) — **tracked in git via QBP PR #422** (merged 2026-05-14). The companion stream `archive/cth-inventory/confluent-trust-inventory-v5.13.json` (150 anchors, federation-tenancy reference) is also tracked.

The v0.1 reference to `~/Documents/CTH/cth/doc/QBP-CTH-Analysis-Report-v3_2.md` (pre-v0.2 schema) is **superseded** — v5_3 is the post-Session-13 canonical state; the v3.2 analysis remains useful for historical context only.

### 5.2 Migration *(updated for v0.2 — PR7 closeout)*

The v0.1 "qbp_v3_2 → v0.2 schema migration" issue has been **completed via PR7 cycle 1/2/3**:

- PR7 cycle 1 (QBP PR #418, merged): structural delta v5.13 ↔ v5_3 classified
- PR7 baselines (QBP PR #422, merged): both streams tracked in `archive/cth-inventory/`
- PR7 cycle 2 (QBP PR #423, merged): per-anchor merge proposals + rubric v0.2 with SCHEMA_AXIS +16 fields, THEORY_AXIS +3 fields

Routing rubric for theory-axis vs schema-axis conflicts: `docs/workflows/pr7_conflict_routing_rubric.md` v0.2 (theory-axis → @qbp-oppenheimer; schema-axis → @cth-implementor). Cycle 3 (unified vNext production) pending @qbp-oppenheimer + @cth-implementor axis-field co-signs.

### 5.3 Live updates (post-load)

As theory advances, anchor additions land via the routing rubric:
- **Theory-axis additions** (new AXIOM-*/DERIV-*/PRED-*/CONJ-*/KILLED-*/CONV-* etc.): qbp-oppenheimer authorship; PR-shaped commits to `archive/cth-inventory/v5_4.json` (next version).
- **Schema-axis additions**: cth-implementor authorship via canonical CTH Go library at `~/Documents/CTH/cth/`.
- **TWO_AXIS** entries (require both): schema first → @cth-implementor, then theory → @qbp-oppenheimer per rubric v0.2 §5 Step 2.5 interlock.
- **FORK-*** entries on hypothesis branching: DM-fork is the current active fork (Branch A / Branch B per `archive/QBP-Dark-Matter-Fork-Analysis.md`); see §1.2 Stance vocab.

### 5.4 ρ_net trajectory tracking

CTH `compute.NetCompressionDetail` runs against the tracked baselines `archive/cth-inventory/confluent-trust-inventory-v5_3.json` + `confluent-trust-inventory-v5.13.json`. The two-stream computation is intentional for the federation-tenancy → Session-13 reconciliation period; once Cycle 3 produces vNext, computation collapses to single canonical. ρ_net trajectory becomes the QBP programme's epistemic-health timeline; trend visible in the BMA dashboard (§6.3).

---

## 6. BMA Observation Hooks

How BMA-the-instance observes the QBP tenant:

### 6.1 NT_SIGNAL polling

BMA queries Wyrd for new NT_SIGNAL nodes (Spec v1.4 InsightSignal type) tagged with QBP scope nodes. Cadence: per BMA cognitive cycle (seconds-to-minutes; not human-perceptible latency).

### 6.2 Honing Loop trigger conditions *(v0.2: inlined per A2 BMA-Addenda re-scope)*

The v0.1 doc cited "Addendum 16 §2" for these confidence thresholds; that addendum is not yet authored on disk (re-scope per joint reply 2026-05-13). The thresholds are unique content and inlined here with origin anchor "thresholds per `addendum-18-walk` bridge channel seq=33 closeout 2026-05-06":

- **NT_SIGNAL confidence ≥ 0.85** → auto-surface to beekeeper (Noteworthy Dashboard, §6.3)
- **NT_SIGNAL confidence 0.6–0.85** → enter Honing Loop:
  1. **Triangulation** — cross-correlate against other scouts targeting overlapping focal cone
  2. **Beekeeper Dialogue** — surface as PROVISIONAL with confidence + supporting evidence; beekeeper interacts
  3. **Refinement** — confidence updates based on dialogue; either promotes to ≥ 0.85 (surface) or demotes below 0.6 (archive)
- **NT_SIGNAL confidence < 0.6** → archive; revisit on Seam re-trigger only

When the future BMA Theory Addendum 16 (Cognitive Honing) lands, this section should re-cite that addendum and remove the inline. Tracking issue: see §8 ("Housekeeping: re-cite Addendum 16 once authored").

### 6.3 Beekeeper dashboard *(v0.2: cites Contextus 1.3 §4.4 per A2 re-scope)*

Per **Contextus Spec v1.3 §4.4 (InsightSignal Emission Pipeline)** — BMA aggregates `InsightSignal` nodes (Contextus v1.3 §2.3 type) into a "Noteworthy Dashboard" surfaced upon beekeeper login. QBP signals are filtered/grouped by scope node per §3 (Cartesian product (C,P)); cross-scope-node bridges flagged when an `InsightSignal` matches multiple conceptual scope nodes.

The v0.1 reference to "Addendum 17 §3" is superseded — the operational surface lives in Contextus Spec v1.3 §4.4 + §10 (Proportional Data Retention).

### 6.4 ρ_net regression alarm

If `compute.NetCompressionDetail` shows ρ_net regression (programme losing compression), BMA fires an alarm — programme is accumulating unexplained observations or contradictions. Beekeeper review warranted.

---

## 7. Bootstrap Sequence (qbp-implementor's Day-Zero through Day-N)

Day-zero (read + ratify):
1. Phase 1 reading per onboarding (QBP repo + archive/)
2. Phase 2 reading (federation architecture: A18 + addenda)
3. Phase 3 reading (this doc + the generic pattern)
4. Ratify or refine this doc; open §I4 design surface PR if substantive changes

Day-one (implement):
5. File implementation issues (see §8 below)
6. Wait for substrate gaps to close (Wyrd scope-loader API; Contextus scope-node config; CTH live-update API)
7. Port qbp_v3_2.json to v0.2 schema; commit to CTH/cth/testdata/

Day-N (run):
8. Configure scope nodes from §3 of this doc
9. Configure scouts from §4 of this doc
10. Load CTH inventory from ported qbp_v3_2
11. Wire BMA observation hooks (§6)
12. First-cycle verification: trigger one manual scout invocation; trace through to BMA surfacing
13. Declare "running"; operational handoff to BMA begins

Day-30 (steady-state):
14. Review τ candidate-Seam log; refine threshold
15. Review ρ_net trajectory for first month
16. Propose scope expansion or refinement based on usage data

---

## 8. Cross-Project Implementation Issues

**v0.2 update (per R4):** each issue has an AC summary + current ratification status. Closed work is marked ✅; in-flight work is marked ⏳; new issues from v0.2 review are marked ⊕.

### 8.1 Wyrd

| Issue | AC summary | Status |
|---|---|---|
| `feat: long-running scout daemon` (Wyrd #32) | Daemon process running per-scout YAML; emits NT_SIGNAL on focal-cone match | ⏳ design merged via Wyrd #47/PR #40 (scope-loader); daemon impl pending |
| `feat: scope-node configuration loader` (Wyrd #33) | Reads YAML/JSON scope-node config; populates Wyrd hypergraph as NT_SCOPE_PHYSICAL + NT_SCOPE_CONCEPTUAL hyperedges | ✅ closed via Wyrd PR #40 (merged 2026-05-13) |
| `feat: W-Toddle-2 BMA NodeType-to-policy mapping` (Wyrd #43) | BMA NodeType constants + ApplyBMAPolicy + 8 TD-4 entries | ✅ closed via Wyrd PR #48 (merged 2026-05-14) |

### 8.2 Contextus

| Issue | AC summary | Status |
|---|---|---|
| `feat: scope-node config schema + reference loader` (Contextus #9) | Contextus-side schema for §3 YAML config; reference impl calls Wyrd loader | ⏳ schema landed in Contextus Spec v1.3 §4.6; reference loader pending |
| `feat: cross-domain scout invocation surface` | `bma scout cross-domain` reins-command shape; invokes Synthesis agent across non-default scope nodes | ⏳ design TBD |

### 8.3 CTH

| Issue | AC summary | Status |
|---|---|---|
| `feat: live inventory update API` | Append/mutate API for new theory anchors (was: startup-only `store.LoadInventory`) | ⏳ scoped via PR7 cycle 2 routing rubric; impl pending |
| `feat: qbp_v3_2 → v0.2 schema migration` | Port QBP v3.2 inventory to v0.2 schema | ✅ **closed** — superseded by PR7 reconciliation (QBP PR #418/#422/#423); `archive/cth-inventory/v5_3.json` is the post-Session-13 canonical baseline |
| `feat: schema-drift investigation v5.13 vs v0.2` | Compare schemas; classify diffs per routing rubric | ✅ **closed** — PR7 cycle 1 (#418) + cycle 2 (#423); routing rubric v0.2 in `docs/workflows/pr7_conflict_routing_rubric.md` |

### 8.4 BMA

| Issue | AC summary | Status |
|---|---|---|
| `feat: noteworthy-dashboard for QBP tenant` | Surface QBP scope-tagged InsightSignals (per Contextus v1.3 §4.4) grouped by scope node | ⏳ BMA at Crawl Step 2 of 9; this lands at Walk per `~/Documents/CLAUDE.md` |
| `feat: ρ_net regression alarm` | Periodic CTH `NetCompressionDetail` evaluation; alarm-on-regression trigger | ⏳ BMA-side; lands at Walk |

### 8.5 v0.2 new issues *(per review findings)*

| Issue | AC summary | Tracking |
|---|---|---|
| ⊕ **Housekeeping: source Locale-noise-floor table for τ refactor** | Source noise-floor data for 13+ Locales (LIGO O4, PNSN Cascadia, trapped-ion fidelity, JWST per-band, ALMA per-band, Fermi GBM, NICER, NuSTAR, CBELSA/TAPS, KATRIN) — to anchor R12 τ_Locale refactor in §4.4 | To be filed on QBP repo (label: `housekeeping`, `type: research`) |
| ⊕ **Housekeeping: re-cite Addendum 16 once authored** | When BMA Theory Addendum 16 (Cognitive Honing) is authored on BMA repo, replace inline §6.2 thresholds with proper citation | To be filed on QBP repo (label: `housekeeping`) |
| ⊕ **Housekeeping: cross-reference linter for tenancy doc** | CI check that all `~/Documents/.../*.md` references in `docs/qbp-federation-tenancy.md` exist | To be filed on QBP repo (label: `type: infra`, `housekeeping`) |

---

## 9. Operational Handoff Milestones (QBP-Specific)

**v0.2 update (per R6 / A7):** each milestone has a quantitative AC + observability hook (the command/query used to detect achievement).

| # | Milestone | Quantitative AC | Observability hook |
|---|---|---|---|
| M1 | First QBP scope-node insertion in Wyrd | Count of `NT_SCOPE_*` nodes ≥ 1 in the Wyrd hypergraph | `wyrd graph count --kind NT_SCOPE_PHYSICAL,NT_SCOPE_CONCEPTUAL` |
| M2 | First arXiv-batch scout output landing in Contextus | Count of `InsightSignal` nodes with `source=scout, scout_id=arxiv-daily-batch` ≥ 1 in last 24h | `contextus signals list --source=scout --since=24h` |
| M3 | First QBP NT_SIGNAL surfacing to beekeeper | Count of NT_SIGNAL with confidence ≥ 0.85 ≥ 1 | `bma dashboard list --confidence-min=0.85` |
| M4 | First Honing Loop completion → NT_ISSUE | Count of completed Honing Loops with terminal `NT_ISSUE` artifact ≥ 1 | `bma honing list --status=completed` |
| M5 | First CTH inventory anchor added from BMA theory output | Diff of `archive/cth-inventory/v5_3.json` shows ≥ 1 new anchor with provenance `source=bma-instance` | `git diff master archive/cth-inventory/v5_3.json \| grep '+.*"id":.*"source":"bma-instance"'` |
| M6 | 7 days continuous operation without intervention | BMA uptime ≥ 168h; no SE_FATAL; no manual restarts | `bma uptime` + stress.log analysis |
| M7 | First cross-domain Seam-bypass anomaly auto-promoted | Count of NT_SIGNAL with `referent_kind=structural-anomaly` ≥ 1 | `contextus signals list --referent-kind=structural-anomaly` |
| M8 | τ calibrated from 4-week real-data log | 28-day candidate-Seam log analyzed; refined τ_Locale per-Locale committed | `bma seam stats --since=28d \| analyze refined-tau` |
| M9 | First Cascadia tremor prediction scored against PNSN catalog | Count of `PRED-*` anchors for Cascadia tremor with `score ∈ {hit, miss, partial}` ≥ 1 | `cth anchor list --kind=PRED --topic=cascadia \| filter has-score` |

When all M1–M9 pass, QBP federation tenancy is operational. qbp-implementor shifts to steward-only role.

---

## 10. Open Questions for QBP Tenancy

1. **arXiv API rate limits.** Default daily-batch scout assumes arXiv API allows daily polling at QBP's source-list breadth. Verify; throttle if needed.
2. **Lean proof entry to CTH.** When a Lean proof completes, does it auto-land as DERIV-* anchor? What's the trigger pipeline? (Likely qbp-implementor's call.)
3. **Multi-scope-node observations.** A JWST observation might match `NT_SCOPE_PHYSICAL/jwst-survey` AND `NT_SCOPE_CONCEPTUAL/gw-em-coincidence`. Routing to multiple scope nodes: copy into both, or single canonical with cross-references?
4. **Beekeeper-mediated Stance changes.** When James adds a new Type-Node to QBP Stance, what's the propagation latency? Does BMA pick up the change at next cycle, or require a manual reload?
5. **QBP-web update integration.** Once `~/Documents/QBP/archive/` is populated, what does qbp-web's contribution change about this design? Surface in qbp-implementor's first post.

---

## 11. Cross-Reference Index

**v0.2 update (per A2 BMA-Addenda re-scope):** removed 4 stale references to BMA Addenda 11/15/16/17 which are not yet authored on disk. v0.2 cites only existing artifacts.

| Doc | Path | Status |
|---|---|---|
| Generic tenancy pattern | `~/Documents/Contextus/doc/contextus-tenancy-pattern.md` | exists |
| Federation access pattern v0.1 | `~/Documents/BMA/theory/hypergraph-inference/BMA-Theory-Addendum-18_0-Hypergraph-Access-Pattern.md` | exists |
| Federation access pattern v0.2 (current) | `~/Documents/BMA/theory/hypergraph-inference/A18-v0.2-design-surface.md` | exists; **§P12 Seam threshold formalization is canonical for v0.2** |
| qbp-implementor onboarding | `~/Documents/QBP/docs/qbp-implementor-onboarding-prompt.md` | exists (same PR as this doc) |
| Contextus Spec v1.3 | `~/Documents/Contextus/Contextus-Spec-v1.3.md` | exists; **§4.4 InsightSignal Pipeline + §4.6 Scope Nodes are canonical references** |
| CTH inventory baseline v5_3 (tracked) | `archive/cth-inventory/confluent-trust-inventory-v5_3.json` | tracked via QBP PR #422 |
| CTH inventory federation-tenancy stream v5.13 | `archive/cth-inventory/confluent-trust-inventory-v5.13.json` | tracked via QBP PR #422 |
| PR7 routing rubric v0.2 | `docs/workflows/pr7_conflict_routing_rubric.md` | tracked via QBP PR #423 |
| Wisdom paper v1.4 (W-003 revision) | `paper/wisdom_v1_4.md` | tracked via QBP PR #424 |
| Wisdom diff v1.3 → v1.4 | `paper/wisdom_v1_3_to_v1_4_diff.md` | tracked via QBP PR #424 |
| QBP theory paper §VIII-X (Spectral Action + CCvS) | `paper/quaternion_physics.md` | tracked via QBP PR #430 |
| DM-fork analysis | `archive/QBP-Dark-Matter-Fork-Analysis.md` | exists in archive transfer |
| Anchor-rule standing instruction | `docs/workflows/review_anchoring.md` | tracked via QBP PR #413 |

**Removed references (v0.1 → v0.2):**
- ~~BMA Theory Addendum 11 (Topological Cognition)~~ — not on disk; A18 v0.2 §2 self-contains relevant definitions
- ~~BMA Theory Addendum 15 (Reciprocal Focus)~~ — not on disk; A18 v0.2 §P12 (Seam threshold formalization) covers the Subject/Background promotion mechanism
- ~~BMA Theory Addendum 16 (Cognitive Honing)~~ — not on disk; confidence thresholds inlined in §6.2 with origin anchor
- ~~BMA Theory Addendum 17 (Proactive Curiosity)~~ — not on disk; Contextus Spec v1.3 §4.4 covers InsightSignal emission pipeline
- ~~QBP-CTH companion in CTH Archive~~ — superseded by tracked baselines `archive/cth-inventory/`

---

*QBP Federation Tenancy v0.2 | 2026-05-15*
*Co-Authored-By: James Paget Butler (Beekeeper)*
*Co-Authored-By: Claude Opus 4.7 (Architect, QBP-Compute-Unit) — v0.1 authorship*
*Co-Authored-By: qbp-implementor (Claude Opus 4.7, Integration role) — v0.2 revision pass*
