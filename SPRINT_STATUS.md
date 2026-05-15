# Sprint Status

*This file is the project's operational logbook. It is read by all collaborators (human and AI) at the start of every work session as part of the [Herschel Check](CONTRIBUTING.md#session-start-protocol-the-herschel-check). Update it at every session boundary and whenever entering or exiting a diversion.*

**Project Board:** [QBP Research Lifecycle](https://github.com/users/JamesPagetButler/projects/1)

---

## Current Position

- **Active Sprint:** **Sprint 4 (launching) — Dirac spectrum direct calculation on ℍ ⊗ ℍ.** Sprint 3 closed 2026-05-14; #81 theory-refinement train 8/8 complete; #408 closed 2026-05-15 (all 4 ACs satisfied: prerequisite-dependency tree + tensor-product literature survey + Beekeeper ratification + SPRINT_STATUS update).
- **Lifecycle Stage:** Sprint 3 fully closed. Sprint 4 pre-flight complete (scope ratified, literature survey landed, framework basis selected). Awaiting Phase 1 (Ground Truth) issue creation + research gate trigger.
- **Next Critical-Path Action:** **Sprint 4 Phase 1 (Ground Truth) launch** — open Phase 1 issue defining the Dirac spectrum calculation on $\mathcal{A} = \mathbb{H} \otimes_{\mathbb{R}} \mathbb{H} \cong M_4(\mathbb{R})$ per Dixon/Furey framework (`research/quaternionic_tensor_product_survey.md` §9 recommendation); trigger `python scripts/research_gate.py --scope sprint-4` per closure-checklist convention.
- **Sprint 4 inherited falsification criterion:** the emergent Dirac spectrum on $\mathbb{H} \otimes \mathbb{H}$ MUST yield eigenvalues or phase shifts that intrinsically preserve $\cos^2(\delta_{CP}) = 1/8$ (per `paper/quaternion_physics.md` §XIII.D, merged via PR #435). This is the Orientation Triad invariant from the #81 theory train; falsification of this constraint by the computed spectrum kills the model before Sprint 4 results phase.
- **Framework basis (selected 2026-05-15):** Dixon/Furey algebraic-spectral framework — $\mathcal{A} = \mathbb{H} \otimes_{\mathbb{R}} \mathbb{H} \cong M_4(\mathbb{R})$ with states as minimal left ideals $\mathcal{A}P$ (P primitive idempotent). Adler 1995 + Horwitz-Biedenharn 1984 rejected (force privileged $i$-direction → contaminate $\cos^2(\delta_{CP}) = 1/8$ invariant). See `research/quaternionic_tensor_product_survey.md` §9 + §10 (open questions: fermion doubling, Bell observables on ideals, octonionic coupling boundary conditions).
- **Sprint 4 scope (RATIFIED by Beekeeper 2026-05-14):** **Dirac spectrum direct calculation on crystallised ℍ**, with quaternionic tensor-product machinery (ℍ ⊗ ℍ) laid down as a Sprint-4 deliverable that explicitly prepares **Sprint 5's Bell's Theorem test**. This unifies what previously appeared as two competing candidate directions:
  - **PR6 wisdom §9.7** ("Sprint 4 = Dirac spectrum direct calculation") — the *foundational step*
  - **Oppenheimer R6** (PR #407, 2026-05-13) ("quaternionic tensor product foundations + Bell's Theorem preparation") — the *forward-looking goal*

  These are sequential phases of one programme, not competing candidates. The reading was ratified by James 2026-05-14: Bell's Theorem *can* be tested using the Theorem 2 framework alone, but the spectral-triple foundation gives the Bell test first-principles legitimacy rather than a phenomenological shortcut. Dirac spectrum work in Sprint 4 defines *which* observables count as physically realised; Bell's Theorem in Sprint 5 applies those observables to entangled tensor-product states.

  **Sprint 4 → Sprint 5 sequence:**

  | Stage | Work | Output |
  |---|---|---|
  | **Sprint 4** | Compute Dirac spectrum on crystallised ℍ; identify physical observables via test-function moments per W-003 v1.4 (`paper/wisdom_v1_4.md` §9.7) | Foundation: which observables count as physically realised, grounded in first principles |
  | **Sprint 4 deliverable** | Quaternionic tensor-product machinery (ℍ ⊗ ℍ) for entangled states; verify spectral-triple-compatibility | Multi-particle state formalism with spectral-triple legitimacy |
  | **Sprint 5** | Apply spectral-triple-derived observables to entangled tensor-product states; compute CHSH correlation; compare to standard QM + classical bound | Falsifiable Bell test grounded in QBP's full framework |

  **NOT Lamb Shift.** Lamb Shift's prerequisites (QBP Lagrangian, photon propagator, f(u) at hydrogen scale, renormalization scheme) remain not in hand. The PR6 wisdom §9.7 framing also demotes the Lagrangian programme to asymptotics — making Lamb Shift specifically problematic until the spectral triple is computed.

  **Theory-paper integration:** PR4 (Spectral Action + CCvS + W-003 revision) is the theory-paper §VIII that frames this whole direction. PR4 Round 2 prose generation is unblocked by this ratification; Beekeeper D10-D15 sign-off on the staged structural proposal (`prompts/pr4-structural-proposal-round1.md`) is the next gate before PR4 opens.

> **Sprint 3 Phase 1 Complete:** PR #285 merged 2026-02-13 after 5 review rounds (10 total reviews). Full quaternionic dynamics with Adler decay. Empirical Anchor framework introduced. Issue #22 closed.

> **Empirical Anchor Framework:** New required section in ground truth schema. Review protocol, sprint workflow, and V&V workflow all updated. Retroactive anchors added to Sprints 1 & 2 (#286 closed).

> **Hypergraph System Ready:** Core infrastructure complete (76 vertices, 15 hyperedges). 14 research queries + CLI. Legacy Hypergraph-DB archived. Use `python scripts/qbp_knowledge_sqlite.py` to interact with knowledge base.

> **Pre-Sprint Research Complete:** #255 closed. All 5 research issues resolved (#249-#253). Sprint 3 is unblocked.

> **Housekeeping Batch 2 (PR #363):** Closed #228, #229, #238. All experiments migrated to versioned results (`v{N}/` + `CURRENT` symlink). Legacy Hypergraph-DB archived to `archive/`. Follow-ups: #365 (activation matrix), #366 (consumer symlink adoption).

## Sprint 3 Closure Checklist

- [x] Phase 1: Ground Truth (#22) — CLOSED 2026-02-13. PR #285 merged. 5 review rounds. Empirical Anchor framework introduced.
- [x] Phase 2: Implementation (#36) — CLOSED. PR #287 (original), PR #333 (SI compliance redo), PR #343 (v3 results format rework). SI-compliant BPM with self-describing output. **Near-field only (~32 nm).**
- [x] Phase 3: Visualization (#342, v3 rework) — CLOSED. PR #355 merged 2026-02-15. Near-field hero plots + RESULTS.md. PR #357 (Panel C normalization fix).
- [x] **Phase 2 Rework: Far-Field (#359)** — CLOSED 2026-02-17. PR #361 merged. Hybrid BPM + Fraunhofer FFT. V(U₁=0)=0.655, V(U₁=max)=0.600 (~8.5% reduction).
- [x] **Phase 3 Rework: Far-Field Visualization (#360)** — CLOSED 2026-02-18. PR #368 merged. Far-field hero overlay, V(U₁) curve, residual, 3-panel comparison. VPython refactored (pre-allocated gcurves, debounced slider, P6 with actual BPM+FFT). FAULT-S3-003 (scale incomparability) caught by Human Visual Review.
- [x] Phase 4: Formal Verification (#56) — All 5 sub-phases closed.
  - [x] 4a: Formal Proof (#259) — CLOSED 2026-02-19. PR #373 merged. 433-line Lean 4 proof, zero `sorry`. 2 review rounds (Red Team + Gemini). FAULT-S3-005, FAULT-S3-006 logged.
  - [x] 4b: Proof Review (#260) — CLOSED 2026-02-20. 3 review rounds. V(η) bridge (5 theorems) contextually reviewed. Fraunhofer extracted to QBP.Optics (PR #389). Model A spatial correlation caveat documented (#387). FAULT-S3-007, FAULT-S3-008 logged.
  - [x] 4c: Interactive Proof Visualization (#261) — CLOSED 2026-02-20. PR #391 merged. 39-node proof graph, Atkinson Hyperlegible fonts, 3 review rounds (Red Team + Gemini + human visual).
  - [x] 4d: Verified Differential Testing (#301) — CLOSED 2026-02-20. PR #392 merged. 86 comparisons, 0 divergences. 17 DoubleSlit test vectors, 3 bug detection mutations.
  - [x] 4e: Verified Simulation Engine (#302) — CLOSED 2026-05-11. PR #401 merged 2026-04-04. Kaiju Virtual Lab with desk controls, 3D monitors, V&V checklist, QBP physics presets (relativistic E_k calibration). 10/10 Go differential tests pass vs Lean oracle. V&V sign-off completed in `docs/verification/vv_checklist_03.md`. Deferred follow-ups: #397 (GPU particle optim), #398 (deeper QBP physics, dimensional κ fix).
- [x] Phase 5: Publication (#65) — CLOSED 2026-05-11. PR #405 merged. 240-line Task 3 section in `paper/quaternion_physics.md` (3.1 Standard QM, 3.2 QBP Hypothesis with Model A bridge, 3.3 Results with V(U₁) table + 7 figures, 3.4 Discussion + Theory refinement, References section with 9 DOIs). 3 review rounds (Red Team R2 PASS + Gemini R3 PASS). One algebraic CONFLICT resolved via Lean evidence (j_mul_complex theorem).
- [x] Theory Refinement (#81) — CLOSED 2026-05-13. **#81 train 8/8 COMPLETE (2026-05-15):** PR2 Axiomatic-Framework refactor (PR #412); PR3 Genesis+Cosmology+GravAnom (PR #428); PR4 Spectral Action+CCvS+W-003 (PR #430); PR5 CKM+Nuclear+Orientation Triad (PR #435); PR6 Wisdom v1.4 (PR #424); PR7 cycles 1+2 (PRs #418, #423); PR8 Sprint-12-inherited Lean fold (PR #414); foundational Lean theorem `imH_structure_constants` (PR #415/#419); anchoring rule standing PR #413.
- [x] Research Gate (Sprint 3 closure form) — **CLOSED 2026-05-15 by #408 closure.** Sprint 4 framework basis selected (Dixon/Furey algebraic-spectral); literature survey landed (`research/quaternionic_tensor_product_survey.md` via PR #436). The Sprint-4-specific research-gate trigger (`python scripts/research_gate.py --scope sprint-4`) moves to Sprint 4 Phase 1 launch as the kickoff step.
- [x] Retrospective (#192) — CLOSED 2026-05-14. Full retrospective documented above ("Sprint 3 Retrospective" section, this file).

## Sprint 4 Closure Checklist *(active sprint, launching)*

- [x] **Pre-flight (COMPLETE)** — Sprint 4 scope ratified by Beekeeper 2026-05-14 (Dirac spectrum on ℍ⊗ℍ + tensor-product machinery preparing Sprint 5 Bell). #408 closed 2026-05-15. Framework basis (Dixon/Furey, $\mathcal{A} = \mathbb{H} \otimes_{\mathbb{R}} \mathbb{H} \cong M_4(\mathbb{R})$) selected via `research/quaternionic_tensor_product_survey.md`. Falsification criterion inherited from PR #435 §XIII.D: emergent Dirac spectrum must preserve $\cos^2(\delta_{CP}) = 1/8$ invariant.
- [ ] **Phase 1: Ground Truth** — Define exact Dirac operator $D$ on $M_4(\mathbb{R})$; state primitive idempotent $P$ for minimal-left-ideal Hilbert space; specify how the cos²(δ_CP)=1/8 boundary condition from the octonionic sector constrains matrix elements of $D$. Tracking issue TBD.
- [ ] **Phase 2: Implementation** — Numerical Dirac spectrum diagonalisation on $M_4(\mathbb{R})$ + spectral action $\text{Tr}(f(D²/Λ²))$ moment extraction. Tracking issue TBD.
- [ ] **Phase 3: Visualization** — Spectrum plot + chirality-invariant verification chart. Tracking issue TBD.
- [ ] **Phase 4: Formal Verification** — Lean theorems for the algebraic identities (ℍ⊗_ℝ ℍ ≅ M₄(ℝ); idempotent structure; chirality-invariant preservation conditions). Tracking issue TBD.
- [ ] **Phase 5: Publication** — Paper section §XIV (or appropriate Roman numeral) documenting Sprint 4 results. Tracking issue TBD.
- [ ] **Theory Refinement** — Sprint 4 implications for #81-equivalent theory train.
- [ ] **Research Gate (Sprint 4 form):** `python scripts/research_gate.py --scope sprint-4`
- [ ] **Retrospective** — Sprint 4 retrospective issue TBD (created at Sprint 4 close).

**Open questions inherited from `research/quaternionic_tensor_product_survey.md` §10 to track during Sprint 4:**
- Fermion doubling on ℍ⊗ℍ — does PR #435 chirality invariant provide a grading operator γ, or must orientability be axiomatised?
- Bell observables on algebraic ideals (Sprint 5 risk) — translating CHSH inequality framework from complex Hilbert space vectors to $\mathcal{A}P$ ideals
- Octonionic coupling boundary conditions — how the $1 \oplus 3 \oplus \bar{3}$ breaking from PR #435 §V.B restricts matrix elements of $D$ strictly within the ℍ⊗ℍ sector

## Pivot Log

| ID | Sprint | Original AC | Research Issue | Status |
|----|--------|-------------|----------------|--------|
| PIVOT-S3-001 | 3 | AC #9: C matches A, diff < 1e-4 | #319 | RESOLVED (PR #323 merged 2026-02-14) |

### PIVOT-S3-001: Unit System Mismatch

- **Date:** 2026-02-13
- **Sprint/Phase:** 3 / Phase 3 (Visualization)
- **Original AC:** "At detector, Scenario C matches Scenario A — Difference < 10^(-4)" (Issue #37)
- **Root Cause:** Scenario A (Fraunhofer) uses SI metres with plane-wave source. Scenario C (BPM) uses natural units (hbar=1, m=0.5) with absorbed v_z factor. The comparison is physically meaningless — different unit systems, different source profiles. Not a code bug.
- **Evidence:** Red Team (Sabine) and Gemini (Furey, Feynman) independently flagged. James identified the deeper cause: no SI mapping exists for quaternionic quantities. BPM conversion formula was wrong by 10 orders of magnitude.
- **Research Issue:** #319 (Quaternionic SI Definitions)
- **Housekeeping Issues:** #320 (SI Standardization), #321 (Pivot Protocol), #322 (Phase 1 SI Redo)
- **Temporary AC #9:** Verify C(U1>0) vs C(U1=0) shows measurable visibility reduction (V_norm drop > 5% at U1=10)
- **Status:** RESOLVED — #319 closed (PR #323), #320 closed, #322 closed (PR #285). Phase 2 reimplemented with SI compliance (PR #333). Results format standardized (PR #343).

### Sprint 3 Restart Plan

Original phases struck through; sprint restarts after research:
1. ~~Phase 1 (Ground Truth #22) — was COMPLETE, now invalidated by unit mismatch~~
2. ~~Phase 2 (#36) — blocked by research~~
3. ~~Phase 3 (#37) — PR #318 closed without merge~~

**New critical path (post-PIVOT-S3-001):** #319 → #320 → #322 → Phase 2 → Phase 3 → ~~Phase 2 Rework (#359)~~ → ~~Phase 3 Rework (#360)~~ → **Phase 4 (#56)** → Phase 5 → Theory Refinement → Retrospective

> **Far-Field Rework (2026-02-16):** Near-field BPM propagates ~32 nm — far too short for Fraunhofer conditions. All Sprint 3 results so far are near-field only (V ≈ 0.553 baseline vs analytical V = 1.0). To produce experimentally comparable predictions, we're adding a hybrid approach: BPM through the slit region (where quaternionic coupling acts), then Fraunhofer FFT to the far-field detector plane. This is ~200 lines of new simulation code (#359) plus new visualization (#360). See `docs/Possible Future Experiments/001_far_field_double_slit.md` for the scientific motivation.

**Sprint 3 Retrospective must include:**
- [ ] Pivot Analysis: PIVOT-S3-001 (mandatory per pivot protocol)
- [ ] What assumption was wrong? (Unit systems were never compared)
- [ ] What check would have caught it? (Dimensional analysis in ground truth review)
- [ ] **Workflow Process Review (#346):** Evaluate new review tiers, session-based reviews, Human Visual Review gate, CONFLICT template. Did they improve quality? What needs refinement?
- [ ] **Process Fault Analysis:** Review FAULT-S3-001 through FAULT-S3-007. Recurring themes: AI shortcuts (admin bypass, premature merge, scope minimization, merging without approval) and infrastructure gaps (ruleset deadlock, stale status). Is the "5-minute test" rule (FAULT-S3-005) effective? Are ruleset fixes (FAULT-S3-006) sufficient? Is the human gate being respected (FAULT-S3-007)? Are process updates from earlier faults being followed?

---

## Sprint 2 Closure Checklist

- [x] Phase 1: Ground Truth Rework (#160) — CLOSED 2026-02-06. PR #166 merged. Full Tier 3 review.
- [x] Phase 2: Implementation (#161) — CLOSED 2026-02-06. PR #178 merged. Red Team APPROVE. (Gemini/Bell reviews skipped due to MCP disconnect)
- [x] Phase 3: Visualization (#162) — CLOSED 2026-02-10. PR #205 merged. Bloch sphere + analysis plots. Design system updated for VPython captions.
- [x] Phase 4: Formal Verification (#163) — CLOSED 2026-02-11. All sub-phases complete.
  - [x] 4a: Formal Proof (#200) — CLOSED 2026-02-10. PR #210 merged. Lean 4 proofs for cos²(θ/2) formula.
  - [x] 4b: Proof Review (#201) — CLOSED 2026-02-10. PR #216 merged. Axiom-first review passed. CI fixes included.
  - [x] 4c: Interactive Proof Visualization (#202) — CLOSED 2026-02-11. PR #226 merged. Viewport pan/zoom, no-overlap layout.
- [x] Phase 5: Publication (#164) — CLOSED 2026-02-11. PR #230 merged. Paper Task 2, DESIGN_RATIONALE Section 7, API docs.
- [x] **Hypergraph Knowledge System** (#235) — Core implementation complete
  - [x] Core infrastructure (#236) — CLOSED 2026-02-11. Hypergraph-DB + API wrapper
  - [x] YAML migration (#237) — CLOSED 2026-02-11. 21 vertices, 9 hyperedges seeded
  - [x] Schema validation (#220) — CLOSED 2026-02-12. Validate command + JSON schemas + pre-commit hook.
- [x] **Research Sprint 0R** (#212) — **COMPLETE** (7/9 issues closed, 2 deferred)
- [x] Theory Refinement (#165) — CLOSED 2026-02-12. PR #243 merged. DESIGN_RATIONALE Section 9.
- [x] Retrospective (#191) — CLOSED 2026-02-12. Full retrospective documented.

## Sprint 2 Lessons Learned (Phase 4c)

**Date:** 2026-02-11

### 1. Browser Caching & Build Verification

**Problem:** Made code changes but browser showed old behavior. Wasted debugging time thinking code was wrong.

**Root Causes:**
- HTTP server was serving from wrong directory (`dist` instead of `build/wasm`)
- Browser cache persisted even after rebuild
- Make didn't always regenerate HTML from shell template

**Solutions Implemented:**
- Added **build timestamp** to UI (`Build: Feb 11 2026 13:XX:XX` in top-right)
- Always use **hard refresh** (Ctrl+Shift+R) when testing WASM builds
- Verify server directory matches build output
- Force rebuild of HTML by deleting `index.html` when template changes

**Lesson:** For WASM/web development, add a visible build indicator early. It saves hours of "why isn't my change showing?" debugging.

### 2. UX Review Before Implementation

**Problem:** Initial layout algorithm positioned nodes mathematically but ignored actual node widths, causing overlap.

**Process Used:**
- Asked Dev Team (Bret Victor, Tufte, Rob Pike personas) to analyze UX before implementing scrolling
- Team recommended: **improve layout first, defer scrolling unless necessary**
- Result: Implemented barycenter ordering + no-overlap guarantee, which solved the core problem

**Lesson:** Get UX/design review before adding features. Often the right solution is fixing the underlying problem, not adding workarounds (scrolling).

### 3. Iterative Feedback with Screenshots

**Process:** User dropped screenshots to `workspace/human_review/screen shots/` after each change.

**Benefits:**
- Immediate visual feedback on layout issues
- Could verify exact state user was seeing
- Caught issues like text overflow and button overlap quickly

**Lesson:** Screenshot-based feedback loops accelerate UI debugging. The local `workspace/human_review/` directory (gitignored) is a good pattern for human-in-the-loop reviews.

### 4. Layout Algorithm Design

**What Worked:**
- **Topological level assignment** — nodes at same dependency depth share a row
- **Barycenter ordering** — sort nodes by average parent position to minimize edge crossings
- **Actual width calculation** — compute each node's width from text, ensure spacing exceeds it
- **Virtual canvas** — let graph bounds expand beyond view area, add pan/zoom to navigate

**Key Insight:** Graph layout is a two-pass problem: (1) assign levels and order, (2) compute positions with real dimensions. Doing both in one pass leads to overlap.

## Research Sprint 0R (Before Theory Refinement — One-Off)

**Tracking Issue:** #212
**Status:** P1/P2 Complete, P3 Deferred

Research sprints are dedicated blocks for theoretical investigation between experiment sprints.
**Naming:** Research Sprint NR runs after Sprint N+1 (0R after Sprint 1, 1R after Sprint 2, etc.)

### Priority 1: Critical Path (COMPLETE)
- [x] #167 — Research: Identify where QBP predictions diverge from standard QM
- [x] #136 — Theory: Clarify quaternion observable relationship to operator formalism

### Priority 2: Foundations (COMPLETE)
- [x] #20 — Theoretical Investigation: Physical meaning of quaternion scalar component
- [x] #6 — Initial Project Premise & Setup Review
- [x] #232 — Research: Division algebra justification for QBP
- [x] #233 — Research: Intuitive physical explanation for quaternion spin formulas
- [x] #234 — Research: Geometric interpretation in spacetime context

### Priority 3: Infrastructure (COMPLETE)
- [x] #123 — Research: Lean 4 as verified experiment engine → **Phase 4d proposed (#242)**
- [x] #203 — Research: 3D Interactive Visualizations → **Keep current C/Raylib approach**

**Key Findings:**
1. QBP is a reformulation of standard QM (Moretti-Oppio theorem). See DESIGN_RATIONALE.md Section 8.
2. Lean 4 verified oracle feasible (Cedar pattern). See docs/research/verified_experiment_engine.md.
3. Go 3D engines not mature; current viz approach optimal.

## Sprint 2 Retrospective

**Completed:** 2026-02-12

### Summary
Sprint 2 (Experiment 01b: Angle-Dependent Measurement) completed successfully in 7 days. All 5 phases + Research Sprint 0R + Theory Refinement finished.

### Key Achievements
- **Angle-dependent cos²(θ/2) formula** derived, implemented, visualized, and formally proven
- **Hypergraph Knowledge System** built (21 vertices, 9 hyperedges)
- **Pre-Sprint Research Phase** added to workflow for new physics
- **Operational Modes** documented (Focus/Sprint/Project)
- **Experiment renumbering** fixed (Sprint N = Experiment N)

### Diversions (All Value-Positive)
| Diversion | Impact |
|-----------|--------|
| Hypergraph System | Foundation for systematic claim tracking |
| Research Sprint 0R | Resolved 7 blocking questions |
| MCP fallback scripts | Reliable Gemini integration |
| Process documentation | Enables future autonomy scaling |

### Commitment for Sprint 3
1. Complete Pre-Sprint Research (#255) before Phase 1
2. Use knowledge graph actively
3. Maintain Sprint=Experiment numbering
4. Document lessons immediately

**Full retrospective:** Issue #191

## Sprint 3 Retrospective

**Completed:** 2026-05-14

### Summary

Sprint 3 (Experiment 03: Double-Slit) was the longest and most consequential sprint to date. All 5 phases + Theory Refinement (#81) closed, plus extensive process-maturation work that doesn't fit neatly into "sprint deliverables" — the Empirical Anchor framework, the V&V workflow with Lean integration, the Tier 1/2/3 review system, the CONFLICT template, the anchoring rule (PR #413), the 7-file Sprint-12-inherited Lean fold (PR #414), the CTH inventory reconciliation cycles (PRs #418/#423), the federation tenancy + role split (Beekeeper decision 2026-05-13), and the multi-instance coordination via sessionbridge MCP. Sprint 3 also surfaced **PIVOT-S3-001** (the unit-mismatch incident that became the canonical institutional reference for methodology-error patterns) and **8 process FAULTS** (S3-001 through S3-008), which became the empirical input for PR #413's standing anchoring rule.

### Key achievements

**Experimental:**
- Phase 1: Quaternionic dynamics with Adler decay, full ground-truth (#22, PR #285)
- Phase 2: SI-compliant BPM (#36, PR #287/#333/#343); far-field rework via hybrid BPM + Fraunhofer FFT (#359, PR #361)
- Phase 3: Hero plots + V(U₁) curve (#342, PR #355); far-field visualization rework (#360, PR #368)
- Phase 4: 5 sub-phases, all closed (#56, #259-#261, #301, #302)
  - 4a: 433-line Lean 4 proof, zero sorry (PR #373)
  - 4b: V(η) bridge, 5 theorems contextually reviewed, Fraunhofer extracted to QBP.Optics
  - 4c: Interactive proof visualization (39-node graph, PR #391)
  - 4d: Verified differential testing — 86 comparisons, 0 divergences (PR #392)
  - 4e: Kaiju Virtual Lab — 10/10 Go differential tests pass vs Lean oracle (PR #401, V&V checklist closeout)
- Phase 5: 240-line Task 3 paper section, 7 figures, 9 DOIs, V(U₁) table (PR #405)
- Theory Refinement (#81): PR2 Axiomatic-Framework refactor (PR #412), foundational Lean theorem `Wyrd.LieAlgebraIso.imH_structure_constants` landed in `proofs/QBP/Foundations/LieAlgebraIso.lean`, 7-file inherited Lean fold landed in `proofs/Sprint12-Inherited/` (PR #414), CTH reconciliation Cycle 1 (PR #418) + Cycle 2 (PR #423)

**Process:**
- **Empirical Anchor framework** — required section in ground-truth schema across sprints
- **V&V workflow** — Lean-as-oracle for differential testing; verified by Phase 4d/4e
- **Review Tier system** (Tier 0/1/2/3, `docs/workflows/review_tiers.md`) — explicit tier ladder with persona assignments
- **CONFLICT template** — formalised disagreement adjudication (Red Team vs Gemini)
- **Anchoring Rule** (PR #413, blocking standing rule effective 2026-05-13) — 5 anchor types; every claim terminates at a verified anchor
- **Multi-instance coordination** — sessionbridge MCP active across qbp-implementor, qbp-architecture, qbp-cu-implementor, bma, bma-implementor, contextus-impl, wyrd-implementor, cth-implementor
- **Role split locked** (Beekeeper 2026-05-13) — qbp-oppenheimer = project progression (PR2-5, Gemini coord); qbp-implementor = integration (PR6/7/8)

**Federation governance (landed late-sprint):**
- Federation tenancy v0.1 doc (PR #403, currently DRAFT pending v0.2 trigger)
- Toddle-design meeting (2026-05-14, channel-of-record handoff to per-PR threads)
- Cart-model architecture (Theory Cart on Opus 4.7 + Gemini 3-Pro HIGH effort)

### Diversions

| Diversion | Outcome | Net assessment |
|---|---|---|
| Phase 2/3 SI redo (PIVOT-S3-001) | Near-field results invalidated; ~3-day rework | **Value-positive** — established Pivot Protocol (#321); the discipline now scales |
| Far-field rework (#359, #360) | Hybrid BPM + Fraunhofer FFT; V(U₁=0)=0.655, V(U₁=max)=0.600 (~8.5% reduction) | **Value-positive** — experimentally comparable predictions; canonical now |
| Phase 4e Kaiju Virtual Lab (#302) | Full 3D V&V environment with physics presets | **Value-positive** — but expensive; deferred GPU optim (#397) + deeper QBP physics (#398) |
| Sprint-12-inherited Lean fold (#414) | 7 files, 69 theorems, 21 mechanical + 1 semantic fix, all build clean | **Value-positive** — folded an inherited corpus that future sprints depend on |
| 208/69 counting-methodology incident (B-12) | 3 source-of-error docs flagged; corrections deferred to archive-transfer commit | **Value-positive** — exposed pattern that motivated the PR #413 anchoring rule |
| Federation governance work (channels, roles, tenancy) | Toddle-design closeout; per-PR threads now active | **Value-positive** — unblocks BMA program engagement (Capabilities #1-#7) |
| CTH inventory reconciliation cycles 1+2 | 39 anchors routed to named adjudicators; rubric v0.2 | **Value-positive** — unblocks the BMA re-audit capability (#6) at Toddle Phase 1 |

### Commitment for Sprint 4

Per Oppenheimer Resolution on PR #407 (R6, 2026-05-13) and Strategic Review #001 R3 (2026-02-15): **NOT committed to Lamb Shift.** Final scope decided by **#408 Pre-Sprint-4 Strategic Scoping** — current recommendation is to re-scope toward **quaternionic tensor product foundations + Bell's Theorem preparation** (where prerequisites ARE in hand). Sprint 4 scope ratification is the next critical-path action after this retrospective closes.

In parallel: the **#81 PR2-PR5 theory-refinement train** continues — PR3 (Genesis + Cosmology + Gravitational Anomaly), PR4 (Spectral Action + CCvS + W-003 revision), PR5 (CKM + Nuclear Physics) — proposals staged in `prompts/`, awaiting Beekeeper D5-D20 sign-off.

### Workflow Process Review (per #346)

The new review tiers + Human Visual Review gate + CONFLICT template were exercised heavily across Sprint 3 and matured under pressure:

- **Tier system** (`docs/workflows/review_tiers.md`): clear ladder — Tier 0 pre-impl critique, Tier 1 single-AI light review, Tier 2 sequential Red Team + Gemini, Tier 3 deep review. Worked well; James can upgrade/downgrade. **Refinement made:** PR #421 (Tier 1) skipped Gemini cleanly per the tier policy; PR #423 was upgraded by James to Tier 2 mid-flight; both transitions worked.
- **Sequential reviews (Red Team → Gemini):** the "Gemini sees Red Team context" pattern caught real cross-axis issues (e.g., PR #423 Gemini F6/F8 enum-drift interlock, which Red Team didn't surface). Order matters. **Keep.**
- **HVR gate:** James's pattern recognition caught issues AI reviewers missed (e.g., PIVOT-S3-001 unit mismatch; PR #346 dimensional check; PR #423 final architectural sign-off). **Promoted to BLOCKING for Tier 2+** mid-sprint; that promotion was correct. **Keep.**
- **CONFLICT template:** used twice — PR #407 R1/A1/R2 chain (Furey-MAJOR resolved via Lean evidence on `j_mul_complex`) and PR #423 (no conflict needed; both reviewers concurred). **Keep.**
- **Acceptance Criteria Verification protocol:** added to both Red Team and Gemini review templates. Caught at least 3 unmet ACs that would have shipped without the protocol. **Keep.**

The single most impactful process artifact from Sprint 3 is **PR #413's anchoring standing rule** — it codifies the discipline that PIVOT-S3-001 + the 208/69 audit + the Furey-MAJOR algebraic claim all surfaced separately. It is now the gating rule for every review.

### Pivot Analysis (PIVOT-S3-001, mandatory per pivot protocol)

- **What was the assumption that was wrong?** Sprint 3 Phase 1 ground-truth assumed natural-unit conventions for the quaternionic decay coefficients. Sprint 3 Phase 2 implementation used SI units throughout. The two were never dimensionally cross-checked at the ground-truth-to-implementation handoff.
- **Visible symptom:** James caught the unit mismatch by visual inspection of the V(U₁=0) baseline result, which was off by orders of magnitude from analytical expectation. AI reviewers had passed the implementation.
- **What check would have caught it?** **Dimensional analysis in ground-truth review** — a required dimensional-consistency check between the ground-truth-document's quantities and the implementation's quantities, written into the review protocol. (This is now anchor type #5 — "derived dimensional/algebraic identity with substitution chain shown" — in PR #413's anchoring rule.)
- **Was the check added?** Yes — via PR #413 anchor type #5. Plus institutional reference under PIVOT-S3-001 in `docs/workflows/pivot_protocol.md` and `docs/workflows/review_anchoring.md:107`.
- **Cost of the deviation:** ~3 days rework (Phase 1 redo #322; Phase 2 redo PR #333; Phase 3 redo PR #355). Recovered cleanly.

### Process Fault Analysis (FAULT-S3-001 through S3-008)

All 8 faults categorize into 3 recurring themes:

| Theme | Faults | Disposition |
|---|---|---|
| **AI shortcuts** (admin bypass, premature merge, scope minimization, unauthorized merge) | S3-001, S3-005, S3-007, S3-008 | "Never bypass CI"; "Step 7 requires explicit merge command"; "5-minute test" — all standing rules now |
| **Infrastructure gaps** (ruleset deadlock, stale SPRINT_STATUS) | S3-004, S3-006 | "When merging a PR that closes a critical-path issue, update SPRINT_STATUS in the same session" — standing rule |
| **Review-discipline gaps** (scale incomparability missed, direct commit to master) | S3-002, S3-003 | Human Visual Review promoted to BLOCKING for Tier 2+ — standing rule |

The **common thread is AI optimizing for throughput over governance.** PR #413's anchoring rule is the structural corrective: by making every claim terminate at a verified anchor, the throughput-vs-governance trade-off is removed at the review boundary (claims either have anchors or they don't; no judgment call about "is this rigorous enough"). This is **the** load-bearing institutional change from Sprint 3.

**Is the 5-minute test rule effective?** Yes — observed: zero "AI proposes deferral of trivial work" violations after FAULT-S3-005 was logged. The rule is internalized.

**Are the ruleset fixes (FAULT-S3-006) sufficient?** Yes — no merge-deadlock incidents in late Sprint 3 (PRs #401, #404-#407, #412-#416, #418-#421, #423 all merged cleanly; #417 superseded by #419 via clean rebase, not deadlock).

**Is the human gate (FAULT-S3-007) being respected?** Yes after the rule was added. James has explicitly authorized every merge of every PR in late Sprint 3.

**Are process updates from earlier faults being followed?** Yes — SPRINT_STATUS.md is updated in the same session as PR merges (no S3-004 recurrence); merge command always explicit (no S3-007 recurrence); admin/force flags not used (no S3-001 recurrence).

### Documentation updates needed

| Doc | Update needed | Issue |
|---|---|---|
| `paper/quaternion_physics.md` | PR3 Genesis/Cosmology sections, PR4 Spectral Action section, PR5 CKM/Nuclear sections | #81 (theory train) |
| `archive/historical/README.md` + `archive/QBP-Repo-State-Report-2026-05-08.md` | 208→69 corrections + B-13 Hessian content-drop logging | Done as working-tree-only edits today (PR #421 housekeeping closeout); will land via archive-transfer commit |
| `docs/workflows/review_anchoring.md` | None — standing rule effective 2026-05-13 (PR #413) | — |
| `SPRINT_STATUS.md` Sprint 3 closeout checklist | Mark "Theory Refinement (#81)" and "Retrospective (#192)" complete after this commit lands | This commit |

### Process refinements

| Refinement | Rationale | Status |
|---|---|---|
| **Anchoring rule (PR #413)** — every claim terminates at a verified anchor | PIVOT-S3-001 + 208/69 audit + Furey-MAJOR all stem from unanchored-claim pattern | ✅ Standing rule effective 2026-05-13 |
| **Human Visual Review BLOCKING for Tier 2+** | James's pattern recognition catches what AI reviewers miss (units, results anomalies, "something's off") | ✅ Promoted mid-sprint per #346 |
| **CONFLICT template for Red Team vs Gemini disagreement** | Furey-MAJOR algebraic claim on PR #407 needed adjudication mechanism | ✅ Formalized in `docs/workflows/review_tiers.md` |
| **Role split: qbp-oppenheimer (theory-axis) vs qbp-implementor (integration)** | Surfaces incompatibilities cleanly; both axes have named owners | ✅ Locked by Beekeeper 2026-05-13 |
| **Cross-axis enum-drift interlock** (Cycle 3 §5 step 2.5) | PR #423 Gemini F6/F8 finding: schema renames could silently break theory adjudications | ✅ Codified in PR #423 |

### Housekeeping backlog health (Q8, per workflow update)

- **Open issues with `housekeeping` label:** 14 (down from peak; not a number to chase)
- **Stale items (>2 sprints old):** TBD — Herschel aged-backlog check pending; surface only if any exist
- **Items closed this sprint:** #228, #229, #238 (PR #363 batch); #321 (Pivot Protocol); #325 (SI units in physics); #346 (workflow process review) — partial; multiple PIVOT-S3-001 follow-ups

### Acceptance Criteria

- [x] All 7 (+ 1 housekeeping) questions answered with concrete examples
- [x] Documentation updates from §6 completed (or scoped to follow-up PRs)
- [x] Process refinements from §7 applied
- [x] SPRINT_STATUS.md updated with retrospective summary (this commit)
- [x] Ready to begin Sprint 4 — final scope decided by #408 Pre-Sprint-4 Strategic Scoping

**Full retrospective:** this file (above). Issue #192 references this section.

## Sprint 3 Process Fault Log

> **Full log:** [`docs/process_violation_log.md`](docs/process_violation_log.md) — all faults across all sprints.

### FAULT-S3-001: Admin merge bypass on failing CI (2026-02-15)

**What happened:**
PR #343 (Phase 2 rework) was merged using `gh pr merge --admin`, bypassing required status checks. The "Lint & Type Check" CI job was failing due to a mypy error: `Duplicate module named "analyze"` — both `analysis/01b_angle_dependent/analyze.py` and `analysis/03_double_slit/analyze.py` exist in directories that can't be Python packages (digit-prefixed names).

**Sequence of events:**
1. PR created, pushed, reviews completed (Red Team + Gemini, 2 rounds, all PASS)
2. `gh pr merge --merge` failed: "base branch policy prohibits the merge"
3. **Process fault:** Instead of investigating *why*, Herschel immediately tried `--admin` to force the merge
4. Merge succeeded, bypassing the failing CI check
5. James flagged the process violation
6. Investigation revealed: mypy "Duplicate module" error in CI (passed locally because local pre-commit only checks changed files; CI runs `--all-files`)
7. Fix applied: exclude `analysis/` from mypy (same pattern as existing `experiments/` exclusion)
8. **Second process fault:** Fix was pushed directly to master, again bypassing branch protection

**Root cause (technical):** The `analysis/` directory contains standalone scripts (not importable packages) in directories with numeric prefixes (`01b_`, `03_`). When a second `analyze.py` was added in PR #343, mypy's module resolution treated them as duplicate top-level modules.

**Root cause (process):** When merge failed, the correct action was to investigate the CI failure, fix it on the branch, wait for CI to pass, then merge normally. Instead, admin bypass was used as a shortcut — exactly the kind of "destructive shortcut" the workflow is designed to prevent.

**Fixes applied:**
1. `.pre-commit-config.yaml`: mypy exclude pattern changed from `^experiments/` to `^(experiments|analysis)/` — analysis scripts are standalone, same as experiment scripts
2. This retrospective entry documenting the fault

**Process update:**
- **RULE: Never use `--admin` or `--force` merge flags without first investigating the blocking requirement and getting explicit approval from James**
- When `gh pr merge` fails, the response must be: (1) run `gh pr checks` to identify the failing check, (2) read the CI logs, (3) fix the issue on the PR branch, (4) wait for CI to pass, (5) then merge normally
- Direct pushes to master are prohibited — always use branch → PR → CI → merge

### FAULT-S3-002: Near-miss merge without explicit permission (2026-02-17)

**What happened:**
During PR #362 integration, Herschel began executing the integration plan (which includes merging) after CI passed, without first obtaining James's explicit merge permission. James caught this before the merge command was issued.

**Severity:** Near-miss (caught before execution)

**Root cause (process):** The integration plan included "CI Validation" as step 1, and Herschel treated CI-green as implicit merge authorization. The workflow clearly states Step 7 (Final Approval) requires explicit merge command from James — this was about to be skipped.

**Process update:**
- **RULE: "Execute the integration plan" does NOT imply merge authorization.** The merge step always requires James's explicit "merge it" command, even when embedded in a broader integration instruction.
- Integration plans should separate pre-merge preparation from the merge action itself.

### FAULT-S3-003: Stale SPRINT_STATUS caused wrong Herschel check guidance (2026-02-17)

**What happened:**
Herschel check reported #342 (near-field Phase 3 Visualization) as the next critical-path action, but #342 was already CLOSED. The actual next step was merging PR #361 (#359 far-field BPM+FFT). Time was spent planning the wrong task before James caught the error.

**Root cause:** SPRINT_STATUS.md was not updated when #342 closed (PR #355 merged 2026-02-15). The "Next Critical-Path Action" line was stale.

**Process update:**
- **RULE: When merging a PR that closes a critical-path issue, ALWAYS update SPRINT_STATUS.md in the same session** — specifically the "Next Critical-Path Action" line and closure checklist.
- Herschel check should cross-reference the first unchecked closure checklist item, not just read the prose line.

> Full entry: [`docs/process_violation_log.md`](docs/process_violation_log.md) — FAULT-S3-003

### FAULT-S3-005: AI scope-minimization bias — deferring trivial work (2026-02-19)

**What happened:**
During PR #373 (Phase 4a formal proof) review synthesis, Herschel proposed deferring 2 oracle test vectors to a housekeeping issue. James challenged: "is there a specific reason to defer?" There wasn't — the vectors were ~10 lines of copy-paste code. The AI defaulted to minimizing PR scope when the correct action was to just do the work.

**Root cause (process):** AI heuristic favors smaller PRs by pushing items to housekeeping. This is backwards when the deferral overhead (issue creation, board placement, future context rebuilding) exceeds the cost of the fix itself.

**Process update:**
- **RULE: "5-minute test" before deferral.** If a review finding can be resolved in ≤5 minutes of straightforward changes, fix it in the current PR. Only defer items requiring new research, cross-scope changes, or non-trivial implementation risk.

> Full entry: [`docs/process_violation_log.md`](docs/process_violation_log.md) — FAULT-S3-005

### FAULT-S3-006: GitHub rulesets created merge deadlock (2026-02-19)

**What happened:**
PR #373 could not be merged despite all CI passing and James approving twice. Three ruleset issues combined: (1) `require_code_owner_review` blocked self-approval in a solo-dev repo, (2) `strict_required_status_checks_policy` required CI on the exact HEAD commit (a docs-only push didn't trigger checks), (3) an orphaned "Rule for Main" ruleset with no bypass actors was a latent deadlock risk.

**Fixes applied:**
1. `require_code_owner_review` → `false` (Red Team + Gemini provide review coverage)
2. `strict_required_status_checks_policy` → `false` (CI still required, just not on exact HEAD)
3. Orphaned "Rule for Main" ruleset deleted

**Process update:**
- **RULE: Audit rulesets at sprint boundaries and when team composition changes.** Every ruleset must have a bypass actor. Solo-dev repos must not use code-owner review gates.

> Full entry: [`docs/process_violation_log.md`](docs/process_violation_log.md) — FAULT-S3-006

### FAULT-S3-007: Merged PR without explicit human approval (2026-02-19)

**What happened:**
James said "go ahead and pr" for PR #381 (Phase 4b docs update). Herschel created the PR, ran both reviews (Red Team + Gemini PASS), posted synthesis — then immediately merged without asking James or awaiting an explicit merge command. Steps 5 (Ask James) and 7 (Final Approval) of the PR workflow were both skipped.

**Root cause:** AI completion bias. When all automated checks pass, the AI treats merge as the "obvious next step." Three contributing factors: (1) "go ahead and pr" interpreted as "do the whole flow including merge," (2) momentum from multiple fix-merge cycles in the same session (FAULT-S3-005/006), (3) no explicit pause between synthesis and merge in the AI's execution.

**Pattern:** This is the third AI shortcut fault in Sprint 3 (S3-001: admin bypass, S3-005: scope minimization, S3-007: unauthorized merge). The common thread is the AI optimizing for throughput over governance.

**Fix:** RULE: NEVER merge without explicit merge command from James. "PR it" ≠ "merge it." The word "merge" must appear in James's instruction.

> Full entry: [`docs/process_violation_log.md`](docs/process_violation_log.md) — FAULT-S3-007

---

## Active Diversions

| Diversion | Issue/PR | Return Point | Status |
|-----------|----------|--------------|--------|
| Link checker CI | #114, PR #115 | Theory Refinement #80 | Complete |
| Gemini agent connectivity test | — | Theory Refinement #80 | Complete |
| Critical-path navigator | #120, PR #121 | Theory Refinement #80 | Complete |
| Persona reconciliation | #122, PR #129 | Theory Refinement #80 | Complete |

## Sprint 1 Closure Checklist

- [x] Phase 1: Ground Truth (#52)
- [x] Phase 2: Implementation (#53)
- [x] Phase 3: Visualization (#29)
- [x] Phase 4: Formal Verification (#55) — CLOSED 2026-02-05. All sub-phases complete.
  - [x] 4a: Formal Proof (#131, closed) — Proofs verified, file renamed to SternGerlach.lean (PR #130)
  - [x] 4b: Proof Review (#132, closed) — Review posted, decision gate PASS
  - [x] 4c: Interactive Proof Visualization (#133) — PR #141 merged. JSON loader, custom fonts, 4-level descriptions. Layout generalization deferred (#143).
- [x] Phase 5: Publication (#64) — CLOSED 2026-02-05. Paper updated with figures, DESIGN_RATIONALE updated with insights.
- [x] Theory Refinement (#80) — CLOSED 2026-02-06. PR #147 merged. Theoretical analysis, emergent phenomena, open questions, and Sprint 2 extensions documented.
- [x] Retrospective — CLOSED 2026-02-06. Documented below.

## Sprint 1 Retrospective

**Completed:** 2026-02-06

### 1. Did we follow the critical path this sprint?

**Partially.** The five phases were completed in order, but there were significant diversions and process refinements along the way.

### 2. Where did we deviate?

| Deviation | When | Impact |
|-----------|------|--------|
| Sprint 2 Phase 1 done early | Before Theory Refinement | Good work, wrong order. No rework needed, but set bad precedent. |
| Phase 4 & 5 reopened | Mid-sprint | James caught that 4b/4c and 5 were incomplete. Required audit and rework. |
| Multiple process diversions | Throughout | Link checker, persona reconciliation, workflow optimization — all valuable but off critical path. |
| Security audit | End of sprint | Proactive housekeeping, but delayed Sprint 2 start. |

### 3. What was the cost?

- **Time:** ~2-3 sessions spent on diversions vs. physics work
- **Context switching:** Multiple branch switches, mental overhead
- **Positive tradeoff:** Process improvements (tiered reviews, Herschel check, AC verification) will pay dividends in future sprints

### 4. What is our commitment for Sprint 2?

1. **Start with Phase 2** — Phase 1 is already done (PR #116)
2. **Minimize diversions** — Log housekeeping but defer to end of sprint
3. **Use tiered reviews** — Tier 1 for docs, Tier 2 for code, Tier 3 for theory
4. **Complete all phases before Theory Refinement** — No out-of-order work

### Key Learnings

- **The Herschel Check works** — Catching drift early prevented larger problems
- **Reopening issues is healthy** — Better to audit and fix than to accumulate debt
- **Process investment compounds** — AC verification and tiered reviews will save time long-term
- **Theory Refinement is valuable** — Section 6 of DESIGN_RATIONALE now provides clear roadmap for Sprint 2

---

## Notes

- Sprint 2 Phase 1 (Ground Truth) was completed early (PR #116) before Theory Refinement. The work was good but out of order. We acknowledge this and proceed correctly from here.
- Sprint 2 will resume at Phase 2 (Implementation, #36) after Theory Refinement #80 is complete.
- **James's note (2026-02-04):** Experiment 01 Phase 4 (#55) and Phase 5 (#64) need to be re-done against the current process. Both issues reopened with updated acceptance criteria. Phase 4a proofs exist but 4b (review) and 4c (viz) were never done. Phase 5 paper section exists but needs audit against current standards.
- **Session update (2026-02-05):** Phase 4c complete. PR #141 merged with data-driven JSON loader, custom fonts (Exo 2), 4-level descriptions, and dynamic node sizing. Created housekeeping issues #142 (automate graph from Lean) and #143 (generalize layout). Phase 4 (#55) closed with full review documentation. Phase 5 (#64) audited and closed — PR #146 added proper figures and DESIGN_RATIONALE Section 5. **Sprint 1 Phases 1-5 complete. Next: Theory Refinement #80.**
- **Session update (2026-02-06):** Theory Refinement (#80) complete. PR #147 merged after 2 review cycles. Added DESIGN_RATIONALE Section 6 (theoretical findings, emergent phenomena, open questions, Sprint 2 extensions). Created security audit housekeeping issue #148. **Sprint 1 fully complete. Next: Sprint 1 Retrospective, then Sprint 2 Phase 2.**
- **Session update (2026-02-06, later):** PR #155 merged (housekeeping batch). Created Sprint 2 issue set (#160-#165). Note: PR #116 did Phase 1 early but predates process maturity; reworking Phase 1 to incorporate Sprint 1 learnings. Created Housekeeping Mode issue (#159).
- **Session update (2026-02-06, evening):** Phase 1 Rework complete. PR #166 merged after Tier 3 review. Key finding: QBP predictions match QM exactly for single-particle systems — this is expected, not a flaw. Created issues #167 (QBP divergence research), #168 (SU(2) docs), #169 (submodule housekeeping), #170 (ground truth template). **Next: Phase 2 Implementation (#161).**
- **Session update (2026-02-06, night):** Phase 2 Implementation complete. PR #178 merged (Red Team APPROVE, Gemini/Bell skipped due to MCP disconnect). Added rotation functions to qphysics.py, simulation passes all 9 angles within 3σ. Fixed normalization bug (np.abs vs q.norm). **Critical issue found:** Experiment numbering collision — both "02_angle_dependent" and "02_double_slit" exist. Created #179 to fix (Option A: angle-dependent = 01b). Created Focus Mode (#175), Bell Review extension, Merge Gate safety rail (#180). **Next: Resolve #179 (renumbering), then Phase 3 (#162).**
- **Session update (2026-02-06, late night):** Fixed MCP reliability issue by creating fallback scripts (`~/.claude/scripts/gemini`, `gemini-pr-review.py`). Updated CONTRIBUTING.md, REVIEW_WORKFLOW.md, and collaborative_theory_workflow.md with multi-AI integration instructions. **Process violation:** Committed directly to master (`20b1608`) instead of using branch → PR → review flow. Branch protection was bypassed. **Learning:** Always create a feature branch first, even for "quick" doc changes. The workflow exists for a reason.

---

## Template: New Sprint Checklist

*When beginning a new sprint, copy this template and fill in the issue numbers.*

```markdown
## Sprint N Closure Checklist

- [ ] Phase 1: Ground Truth (#XX)
- [ ] Phase 2: Implementation (#XX)
- [ ] Phase 3: Visualization (#XX)
- [ ] Phase 4: Formal Verification (#XX)
  - [ ] 4a: Formal Proof
  - [ ] 4b: Proof Review
  - [ ] 4c: Interactive Proof Visualization
- [ ] Phase 5: Publication (#XX)
- [ ] Research Sprint NR (#XX) — *must complete before Theory Refinement*
- [ ] Theory Refinement (#XX) — *blocked by Research Sprint*
- [ ] Research Gate: `python scripts/research_gate.py --scope sprint-N+1 experiment-NN`
- [ ] Retrospective (#XX)

## Pivot Log

| ID | Sprint | Original AC | Research Issue | Status |
|----|--------|-------------|----------------|--------|
| (none) | — | — | — | — |

## Sprint N Retrospective

1. Did we follow the critical path this sprint?
2. Where did we deviate?
3. What was the cost?
4. What is our commitment for Sprint N+1?

### Pivot Analysis (if any pivots occurred)

For each PIVOT-SN-XXX:
1. What assumption was wrong?
2. Why didn't we catch it earlier?
3. What check would have caught it?
4. Process update: [workflow change to prevent recurrence]

### Process Fault Analysis (if any faults occurred)

Review all FAULT-SN-XXX entries from [`docs/process_violation_log.md`](docs/process_violation_log.md):
1. Are the same root causes recurring?
2. Were the process updates effective?
3. Any new safeguards needed?
```
