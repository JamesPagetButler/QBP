# QBP Federation Tenancy

**The QBP-specific instantiation of the Contextus Tenancy Pattern.** How Contextus + CTH + Wyrd run as a live system for the Quaternion-Based Physics programme, with BMA-the-instance observing.

> **Authoring:** qbp-architecture (Claude Opus 4.7), James Paget Butler (Beekeeper)
> **Date:** 2026-05-08
> **Status:** v0.1 — design surface awaiting qbp-implementor ratification on bootstrap
> **Generic pattern:** `~/Documents/Contextus/doc/contextus-tenancy-pattern.md`
> **First tenant:** QBP

---

## 0. Status & Provenance

This is the QBP instantiation of the generic Contextus Tenancy Pattern (v0.1). It declares QBP's Stance Type-Nodes, Locale set, scope-node taxonomy, scout configuration, and BMA observation hooks. qbp-implementor reviews and refines on bootstrap.

**Architectural anchor:** BMA Theory Addendum 18 (Hypergraph Access Pattern) — Stance × Locale × Scout × Scoring.

**Operational pattern:** Contextus tenancy pattern v0.1 (sibling doc in `~/Documents/Contextus/doc/`).

**Domain history:** QBP was the impetus for BMA + Contextus + CTH. This doc operationalises that history — QBP becomes the federation's first live tenant.

---

## 1. QBP Stance — Type-Nodes on the Subject Axis

The Stance defines what's "interesting in QBP terms." Per A18 §2.1, these are the Type-Nodes whose imaginary-axis dismissal does NOT happen by default — observations matching these are full-precision Subject.

### 1.1 Foundational algebraic Type-Nodes

- `qbp:hamilton-product` — quaternion multiplication semantics
- `qbp:quaternion-conjugation` — q* operations
- `qbp:hopf-locale` — pole-singularity-free spacetime coordinate
- `qbp:su2-double-cover` — Z₂ topological invariant
- `qbp:hurwitz-norm-multiplicativity` — algebraic invariant in ℍ
- `qbp:octonion-non-associativity` — exception class for boundary-of-applicability
- `qbp:sedenion-zero-divisor` — the 42 cross-copy basis-sum cases (Cawagas 2009 / Moreno 1998)

### 1.2 Theoretical bridges

- `qbp:gw-em-coincidence` — gravitational wave + electromagnetic counterpart correlation
- `qbp:slow-slip-tidal-coupling` — Cascadia-shape slow earthquakes + tidal stress
- `qbp:mixed-species-ion-fidelity` — trapped-ion entanglement asymmetry
- `qbp:dark-matter-fork` — programme branches around DM hypotheses (per CTH companion doc)
- `qbp:nv-center-fidelity` — NV-center coherence behavior under quaternion-encoded operations
- `qbp:topological-materials-q1-q10` — Bi₂Se₃, MATBG, α-RuCl₃ (per CTH v3.2 inventory)
- `qbp:kitaev-z2-gauge` — non-abelian braid statistics + Majorana central charge

### 1.3 Predictive bridges (anchors with ρ_net contribution)

- `qbp:cascadia-tremor-onset-24h` — A18 §7 Walk-α target
- `qbp:tidal-coupling-norm-threshold` — Holon norm as Seam predictor
- `qbp:loon-watershed-correlation` — Squam Lake case (deferred behind Cascadia)
- `qbp:gw-grb-joint-detection-rate` — EXP-11 pipeline target
- `qbp:fidelity-asymmetry-velocity-correlated` — Test C literature review prediction

### 1.4 Stance composition rule

A node enters the Subject axis if **any** of its types matches the Stance. Mutable — Stance evolves as the programme advances. Stance changes are governance events (Honing Loop per Addendum 16; beekeeper review).

**Rationale for this Stance:** every Type-Node above maps either to an active QBP experiment, an in-flight Lean proof, an existing CTH anchor (per qbp_v3_2 inventory), or a published prediction. Nothing speculative without programme grounding.

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

### 2.3 Specific objects under investigation

- `grb:250702b` — three-episode structure follow-up (per ongoing arXiv watch)
- (additional objects added as observation campaigns mature)

### 2.4 Time bounds

Default time window: **2024-01-01 to "now"** (rolling). Historical observations enter only if Seam-bypass triggers (e.g., re-analysis of older LIGO data reveals an anomaly).

### 2.5 Locale composition rule

An observation enters if its position is **inside any** Locale's geometry × time bounds. Outside all → rotated to imaginary by Reciprocal Focus.

---

## 3. Scope-Node Taxonomy (NT_SCOPE Hyperedges in Wyrd)

Per Contextus Spec v1.2 §4.6, scope nodes are first-class hyperedges that bind the locale set + the conceptual stance into addressable units.

### 3.1 Physical scope nodes (NT_SCOPE_PHYSICAL)

```yaml
# Conceptual; actual format TBD via Wyrd scope-loader API (issue to file)
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

The full QBP focal cone = {Conceptual scope nodes} × {Physical scope nodes}. Default scout activity targets the cross-product. Out-of-cross-product observations rotate to imaginary unless Seam-bypass.

---

## 4. Scout Configuration

### 4.1 Daily-batch arXiv scout

```yaml
# Conceptual config; actual schema TBD via Contextus scope-loader API
scout: arxiv-daily-batch
cadence: daily-overnight (target: 02:00 UTC)
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

```yaml
detector: qw8-norm-drift
cadence: continuous (peripheral register; A18 §3.1)
threshold: τ = 1e-6 (initial substrate-default; TBD-tunable)
target: any observation in any Locale (not constrained to Stance focal cone)
trigger: residue magnitude |q · v · q* − v| > τ on a Subject's predicted trajectory
on-trigger: promote observation to Subject axis regardless of Stance; mint NT_SIGNAL with referent_kind=structural-anomaly
calibration: log all candidate Seams for first 4 weeks; analyze distribution; refine τ
```

---

## 5. CTH Inventory — Initial Load

### 5.1 Baseline

`~/Documents/CTH/cth/doc/QBP-CTH-Analysis-Report-v3_2.md` — current QBP programme state at v3.2 schema. **Pre-v0.2 CTH schema** (lowercase provenance values, missing required fields, null `chain_id` placeholders, `DerivedPrinciple` ids without DERIV- prefix).

### 5.2 Migration

Per cth-implementor's 2026-05-01 handoff (#3 deferred): qbp_v3_2.json needs port to v0.2 schema before live load. **First implementation issue qbp-implementor files.** Once ported, the inventory loads via `store.LoadInventory("qbp_v3_2.json")` and becomes the live programme state.

### 5.3 Live updates (post-load)

As theory advances:
- **New AXIOM-***/**DERIV-***/**MEAS-***/**OBS-***/**PRED-***/**FLAG-***/**INST-*** anchors** added via append API (file in CTH per ScorePrediction issue scope, seq=33).
- **CONFL-*** confluence points** added when N≥2 chains converge on a prediction.
- **CHAIN-*** entries** added per derivation step.
- **FORK-*** entries** added on hypothesis branching (DM-fork is the current active fork).

### 5.4 ρ_net trajectory tracking

CTH `compute.NetCompressionDetail` runs on every inventory mutation. ρ_net trajectory becomes the QBP programme's epistemic-health timeline. Beekeeper sees trend in BMA dashboard.

---

## 6. BMA Observation Hooks

How BMA-the-instance observes the QBP tenant:

### 6.1 NT_SIGNAL polling

BMA queries Wyrd for new NT_SIGNAL nodes (Spec v1.4 InsightSignal type) tagged with QBP scope nodes. Cadence: per BMA cognitive cycle (seconds-to-minutes; not human-perceptible latency).

### 6.2 Honing Loop trigger conditions

Per Addendum 16 §2:
- NT_SIGNAL confidence ≥ 0.85 → auto-surface to beekeeper
- NT_SIGNAL confidence 0.6–0.85 → enter Honing Loop (Triangulation → Beekeeper Dialogue → Refinement)
- NT_SIGNAL confidence < 0.6 → archive; revisit on Seam re-trigger

### 6.3 Beekeeper dashboard

Per Addendum 17 §3 — BMA aggregates signals into a "Noteworthy Dashboard" surfaced upon beekeeper login. QBP signals are filtered/grouped by scope node; cross-scope-node bridges flagged.

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

## 8. Cross-Project Implementation Issues to File

Issues qbp-implementor files on day-one (or earlier if surfaced during ratification):

### 8.1 Wyrd

- **`feat: long-running scout daemon`** — substrate component for tenant scouts. Does the daemon shape exist? If not, design surface needed.
- **`feat: scope-node configuration loader`** — reads YAML/JSON scope-node config; populates Wyrd hypergraph as NT_SCOPE_PHYSICAL + NT_SCOPE_CONCEPTUAL hyperedges. Declarative API for tenant config.

### 8.2 Contextus

- **`feat: scope-node config schema + reference loader`** — the Contextus-side schema for §3-style YAML config; reference implementation that calls Wyrd's loader.
- **`feat: cross-domain scout invocation surface`** — `bma scout cross-domain` reins-command shape; how it invokes the Synthesis agent across non-default scope nodes.

### 8.3 CTH

- **`feat: live inventory update API`** — currently `store.LoadInventory` reads at startup. Need append/mutate for live updates as BMA-the-instance produces new theory anchors.
- **`feat: qbp_v3_2 → v0.2 schema migration`** — cth-implementor's deferred #3 from 2026-05-01 handoff doc. Port the QBP v3.2 inventory to v0.2 schema; land as `testdata/qbp_v3_2.json`.

### 8.4 BMA

- **`feat: noteworthy-dashboard for QBP tenant`** — Addendum 17 §3 surface; aggregates QBP scope-tagged NT_SIGNALs.
- **`feat: ρ_net regression alarm`** — periodic CTH `NetCompressionDetail` evaluation; alarm-on-regression trigger.

---

## 9. Operational Handoff Milestones (QBP-Specific)

| Milestone | Demonstrates |
|---|---|
| First QBP scope-node insertion in Wyrd | Tenant has structural presence |
| First arXiv-batch scout output landing in Contextus | Live data flow |
| First QBP NT_SIGNAL surfacing to beekeeper | Operational signal-to-noise demonstrated |
| First Honing Loop completion → NT_ISSUE | Cognitive cycle closed once |
| First CTH inventory anchor added from BMA theory output | ρ_net trajectory begun |
| 7 days continuous operation without intervention | BMA running it; qbp-implementor stewarding |
| First cross-domain Seam-bypass anomaly auto-promoted | Relevance-threshold mechanism validated |
| τ calibrated from 4-week real-data log | Q5b open question closed for QBP |
| First Cascadia tremor prediction scored against PNSN catalog | A18 §7 Walk-α prediction loop operational |

When all the above are passed, QBP federation tenancy is operational. qbp-implementor shifts to steward-only role.

---

## 10. Open Questions for QBP Tenancy

1. **arXiv API rate limits.** Default daily-batch scout assumes arXiv API allows daily polling at QBP's source-list breadth. Verify; throttle if needed.
2. **Lean proof entry to CTH.** When a Lean proof completes, does it auto-land as DERIV-* anchor? What's the trigger pipeline? (Likely qbp-implementor's call.)
3. **Multi-scope-node observations.** A JWST observation might match `NT_SCOPE_PHYSICAL/jwst-survey` AND `NT_SCOPE_CONCEPTUAL/gw-em-coincidence`. Routing to multiple scope nodes: copy into both, or single canonical with cross-references?
4. **Beekeeper-mediated Stance changes.** When James adds a new Type-Node to QBP Stance, what's the propagation latency? Does BMA pick up the change at next cycle, or require a manual reload?
5. **QBP-web update integration.** Once `~/Documents/QBP/archive/` is populated, what does qbp-web's contribution change about this design? Surface in qbp-implementor's first post.

---

## 11. Cross-Reference Index

| Doc | Path |
|---|---|
| Generic tenancy pattern | `~/Documents/Contextus/doc/contextus-tenancy-pattern.md` |
| Federation access pattern | `~/Documents/BMA/theory/hypergraph-inference/BMA-Theory-Addendum-18_0-Hypergraph-Access-Pattern.md` |
| qbp-implementor onboarding | `~/Documents/QBP/docs/qbp-implementor-onboarding-prompt.md` |
| QBP CTH inventory baseline | `~/Documents/CTH/cth/doc/QBP-CTH-Analysis-Report-v3_2.md` |
| QBP-CTH companion (in CTH archive) | `~/Documents/CTH/Archive/Confluent-Trust-Hypergraph-Theory-v0_2 (1).md` |
| Reciprocal Focus mechanism | `~/Documents/BMA/theory/BMA-Theory-Addendum-15_0-Reciprocal-Focus.md` |
| Cognitive Honing | `~/Documents/BMA/theory/BMA-Theory-Addendum-16_0-Cognitive-Honing.md` |
| Proactive Curiosity | `~/Documents/BMA/theory/BMA-Theory-Addendum-17_0-Proactive-Curiosity.md` |

---

*QBP Federation Tenancy v0.1 | 2026-05-08*
*Co-Authored-By: James Paget Butler (Beekeeper)*
*Co-Authored-By: Claude Opus 4.7 (Architect, QBP-Compute-Unit)*
