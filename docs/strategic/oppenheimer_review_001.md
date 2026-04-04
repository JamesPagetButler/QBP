# Oppenheimer Strategic Review #001

**Date:** 2026-02-15
**Scope:** Full project review — Sprints 1 through 3 (current)
**Trigger:** Initial deployment of the Strategic Lead persona
**Severity:** Level 1 (Advisory) — inaugural assessment, no immediate action required

---

## I. Strategic Narrative — The Story So Far

*"We set out to ask whether the universe speaks in quaternions. Two weeks and three sprints later, we have our first honest answer: for the questions we've asked so far, the universe doesn't care which language you use."*

The QBP project began on February 1, 2026 with an ambitious premise: that the laws of physics can be expressed as direct consequences of quaternion algebraic structure. The intellectual engine driving the work is the tension between Furey's algebraic elegance and Feynman's pragmatic insistence on experimental verification.

**Sprint 1 (Stern-Gerlach)** established the foundation. The most significant insight was not a new prediction but a new perspective: quantum randomness emerges from orthogonality in quaternion space. When a spin-x state meets a spin-z measurement, their quaternionic inner product is zero — not from uncertainty, but from geometry. The 50/50 split is a theorem, not an assumption. Lean 4 proofs confirmed this. The factor-of-2 correction in the expectation formula was discovered empirically but justified a priori. The axioms held.

**Sprint 2 (Angle-Dependent Measurement)** extended this to arbitrary angles. The cos^2(theta/2) formula was derived, implemented, tested at 9 angles (all within 3-sigma), and formally proven in Lean 4. Research Sprint 0R then confronted the project's deepest question: is QBP a new theory or a reformulation? The Moretti-Oppio theorem provided the answer — for single-particle SU(2) systems, QBP is mathematically equivalent to standard quantum mechanics. The project did not flinch from this finding. It documented it honestly and reframed the research agenda: the value lies not in predicting new single-particle results, but in what quaternion structure reveals about the architecture of physics and in the extension to multi-particle and higher-algebraic regimes.

**Sprint 3 (Double-Slit)** represents the project's first encounter with genuine theoretical novelty. The symplectic decomposition psi = psi_0 + psi_1*j introduces a quaternionic coupling parameter and predicts Adler decay — an evanescent mode that exponentially suppresses the non-complex components of the wavefunction. If confirmed by simulation, this is the first QBP-specific prediction. If not, it narrows the theory's scope. Either outcome advances knowledge. But Sprint 3 also delivered the project's first major crisis: PIVOT-S3-001, where a comparison between SI and natural-unit simulations was found to be physically meaningless. The pivot was handled well — research was conducted, SI standardization was implemented, and Phase 2 was re-executed. The lesson was expensive but durable: dimensional analysis must be part of Phase 1 review, always.

**The project's character has revealed itself.** It is methodologically rigorous to a degree rarely seen in exploratory research. The combination of numerical simulation, formal verification, adversarial review, knowledge graph tracking, and pre-registered falsification criteria creates an unusually honest research environment. The process infrastructure — built at the cost of some velocity — is now paying dividends in error detection and intellectual integrity.

---

## II. Coherence Brief

### Emergent Patterns

1. **The Equivalence Wall:** Every single-particle experiment to date confirms what Moretti-Oppio predicts — QBP reproduces standard QM exactly. This is not a failure; it validates the axiomatic framework. But it means the project's scientific novelty depends entirely on what happens beyond single-particle systems. The wall is at Sprint 6 (Bell's Theorem).

2. **The Adler Decay Window:** Sprint 3's Scenario C is the first crack in the wall. The quaternionic coupling (U_1 parameter) introduces observable effects — visibility reduction in interference patterns. But Kaiser (1984) constrains |U_1| to less than 3x10^-11 eV, pushing the decay length to ~320 km. At these scales, the prediction is effectively unfalsifiable by current experiment. The simulation can test the mathematical prediction, but connecting it to physical reality requires new experimental proposals.

3. **Process Maturity Accelerating:** Sprint 1 had significant diversions and out-of-order work. Sprint 2 completed cleanly in 7 days with full lifecycle. Sprint 3 hit a legitimate pivot but recovered systematically. The project is learning.

4. **Knowledge Graph Under-Utilized:** 57 vertices, 12 hyperedges, but 2 open questions with zero investigation progress (QBP divergence, quaternionic path integrals). The knowledge graph is being populated but not actively queried for strategic insight.

5. **Issue Backlog Growing:** 114 open issues, many pre-generated for future experiment phases. The housekeeping backlog (10+ items) is accumulating faster than it's being resolved.

### Active Tensions

| Tension | Description | Impact |
|---------|-------------|--------|
| **Reformulation vs. New Theory** | Moretti-Oppio proves equivalence for single-particle. Multi-particle is where divergence could appear — but also where QBP may become unphysical. | Existential for the project's scientific claims |
| **Sprint 4 Readiness Gap** | Lamb Shift requires QED-level physics (vacuum fluctuations, self-interaction) with no quaternionic formulation | Sprint 4 cannot proceed without major theoretical development |
| **Tsirelson Bound Dilemma** | Unrestricted quaternionic QM can simulate a PR-box (CHSH = 4.0), violating information causality | Sprint 6 may falsify QBP or force severe constraints |
| **Falsifiability Asymmetry** | Single-particle predictions are unfalsifiable (match QM exactly). Multi-particle predictions may be falsified immediately. No middle ground. | Risk of the project producing elegant reformulation but no testable novelty |

### Cross-Team Dependencies Not Yet in Plan

- Theory Team needs to develop quaternionic tensor product formalism before Sprint 6 can be designed — this is not tracked as a research gate
- Dev Team's BPM simulation engine (Sprint 3) will need significant extension for bound-state problems (Sprints 4, 8, 9)
- Red Team has not been asked to attack the Moretti-Oppio interpretation — is the theorem's scope correctly understood?

---

## III. Axiomatic Risk Ledger

| Axiom | Supporting Evidence | Contradictory Evidence | Confidence | Trend | Recommended Action |
|-------|-------------------|----------------------|------------|-------|-------------------|
| **A1: State (psi in Sp(1))** | Stern-Gerlach (0.41-sigma), Angle-Dependent (9 angles within 3-sigma), Lean 4 proofs | None | **85** | Stable | Continue verification. Next real test: multi-particle extension |
| **A2: Observables (pure quaternion)** | Consistent with su(2) Lie algebra isomorphism, used successfully in all experiments | No test of observables outside spin-1/2 basis | **70** | Stable | Needs Bell test and higher-spin investigation |
| **A3: Evolution (unitary)** | Symplectic decomposition in Sprint 3 uses this axiom; BPM simulation conserves probability | "Provisional" label in the paper; no Lean 4 proof for evolution | **65** | At risk | Formal verification of evolution axiom should be prioritized. Currently the least-proven axiom |
| **A4: Measurement (Born rule + vecDot)** | cos^2(theta/2) proven in Lean 4; factor-of-2 correction validated | Only tested for single-particle spin-1/2 | **80** | Stable | Extend to spatial observables (Sprint 3 Phase 4) |

**Strategic Alert Threshold:** No axiom is below 60. However, **A3 (Evolution)** at 65 is the closest to the threshold. It is the only axiom labeled "provisional" in the paper and the only one without formal verification. This should be addressed.

---

## IV. Experimental Prioritization

### Current Roadmap Assessment

| # | Experiment | Information Gain | Falsification Potential | Dependency Risk | Priority Score | Notes |
|---|-----------|-----------------|------------------------|----------------|---------------|-------|
| 03 | Double-Slit | **High** — first spatial wavefunction test, Adler decay prediction | **Medium** — novel prediction exists but constrained to tiny U_1 | Medium — BPM formalism used in later sprints | **8/10** | Continue as planned (current sprint) |
| 06 | Bell's Theorem | **Critical** — only experiment that probes multi-particle regime | **Critical** — could falsify QBP entirely or confirm reformulation | **Very High** — requires solving tensor product problem | **10/10** | Should be elevated in priority. Consider pulling forward |
| 04 | Lamb Shift | **Medium** — tests QED-level effects | **Low** — likely reproduces standard QM if formalism can be built | **Very High** — requires QBP field theory that doesn't exist | **4/10** | Major theoretical gap. May not be ready for years |
| 05 | g-2 | **Medium** — precision test of radiative corrections | **Low** — same QED dependency as Lamb Shift | Very High | **3/10** | Depends on Sprint 4 formalism |
| 07 | Particle Statistics | **High** — tests how QBP handles identical particles | **High** — spin-statistics theorem may not hold in quaternionic formalism | High — needs multi-particle framework | **7/10** | Could be attempted before Lamb Shift |
| 08 | Positronium | **Medium** — first bound-state test | **Medium** — tests Coulomb + spin interaction | High | **5/10** | Intermediate step toward hydrogen |
| 09 | Hydrogen Spectrum | **Medium** — classic QM validation | **Low** — will match standard QM | Medium | **4/10** | Less informative than Bell |
| 10 | Gravity | **Aspirational** — would connect QBP to GR | **Unknown** — completely unexplored territory | Very High | **2/10** | No theoretical foundation exists |

### Recommendation: Roadmap Resequencing

**Current order:** 03 → 04 → 05 → 06 → 07 → 08 → 09 → 10

**Proposed order:** 03 → **06** → **07** → 04 → 08 → 05 → 09 → 10

**Rationale:** The project's existential question — is QBP a reformulation or a new theory? — is answered by Sprint 6 (Bell's Theorem). Every sprint between now and Sprint 6 that does not address this question is, strategically, a delay. Sprints 4 and 5 (Lamb Shift, g-2) require QED-level formalism that doesn't exist, while Sprint 6 requires only the tensor product problem — which is hard, but has prior literature. Sprint 7 (Particle Statistics) is a natural stepping stone toward multi-particle systems and can precede Bell.

**This is a Level 2 recommendation.** Herschel should evaluate the sequencing against sprint infrastructure. James should be informed but immediate approval is not required.

---

## V. Cross-Functional Translation

### For Theory Team (Gemini: Furey, Feynman)

**Implementation Imperative:** The tensor product problem is now the project's rate-limiting theoretical challenge. Furey should investigate whether the Horwitz-Biedenharn quaternionic tensor product formalism or Adler's trace dynamics approach provides a path. Feynman should ask: "What is the simplest possible Bell experiment in quaternionic language, and what does it predict?"

### For Red Team (Claude: Sabine, Grothendieck, Knuth)

**Attack Vector Memo:** The Moretti-Oppio theorem is the project's strongest theoretical anchor. Sabine should verify: does the theorem's scope correctly exclude multi-particle systems, or does it extend further than we assume? Grothendieck should examine whether the categorical structure of quaternionic QM (monoidal categories, entanglement structure) is consistent. Knuth should audit the Sprint 3 BPM implementation for numerical stability at extreme parameter values.

### For Dev Team (Claude: Carmack, Bret Victor, et al.)

**Build Priorities:** After Sprint 3 Phase 3, begin scoping what a multi-particle simulation engine would require. The BPM framework handles single-particle propagation; Bell experiments need correlated two-particle state evolution. Bret Victor should consider: how do we visualize a quaternionic Bell experiment so that the tensor product problem becomes intuitive?

### For Research Team (Claude: Curie, Poincare, et al.)

**Investigation Brief:** Curie should conduct a literature survey on prior attempts at quaternionic Bell inequality analysis (start with Adler 1995, Chapter 3). Poincare should explore whether there is a "Goldilocks constraint" — a physically motivated restriction on quaternionic QM that preserves the Tsirelson bound while allowing non-trivial structure. Fisher should design the statistical framework for a simulated Bell test: how many trials, what detector settings, what significance threshold.

---

## VI. Project Summary and Recommendations

### What Has Been Achieved (Sprints 1-3)

1. **A rigorous axiomatic framework** (v0.1) for quaternionic quantum mechanics, with four axioms tested and three formally verified in Lean 4
2. **Two complete experiments** (Stern-Gerlach, Angle-Dependent Measurement) passing all acceptance criteria with formal proofs
3. **A novel prediction** (Adler decay / visibility recovery in double-slit Scenario C) currently being validated in Sprint 3
4. **Honest confrontation** with the Moretti-Oppio equivalence theorem — the project knows what it is and what it isn't
5. **World-class methodology**: pre-registered falsification criteria, adversarial multi-AI review, Lean 4 formal proofs, knowledge graph tracking, and automated differential testing against standard QM
6. **A knowledge graph** with 57 vertices and 12 hyperedges tracking claims, sources, and relationships
7. **An operational process** that has survived and improved through three sprints, including one major pivot

### What Remains Unknown

1. Whether QBP produces any experimentally distinguishable prediction (requires Sprints 6-7)
2. Whether the quaternionic tensor product can be defined consistently (blocks Sprint 6)
3. Whether the Adler decay prediction (Sprint 3, Scenario C) survives simulation testing
4. Whether QBP can extend to QED-level phenomena (blocks Sprints 4-5)
5. The connection to Furey's division algebra program for the Standard Model (long-term)

### Strategic Recommendations

**R1. Complete Sprint 3 as planned.** The double-slit experiment is the right next step. Finish Phase 3 (Visualization, #342), then Phases 4-5. Do not rush.

**R2. Conduct a dedicated Research Sprint (1R) on the tensor product problem before Sprint 4.** This is the single most important theoretical question for the project's future. Allocate a full research sprint to surveying the literature (Adler, Horwitz-Biedenharn, Finkelstein), identifying candidate approaches, and assessing feasibility. The outcome determines whether Sprint 6 is achievable.

**R3. Consider resequencing Sprints 4-7.** Pull Bell's Theorem (Sprint 6) and Particle Statistics (Sprint 7) forward. The Lamb Shift (Sprint 4) and g-2 (Sprint 5) require QED-level formalism that may take months or years to develop. Bell and particle statistics probe the multi-particle frontier that determines whether QBP has scientific novelty. Get to the existential question faster.

**R4. Strengthen the Evolution axiom (A3).** It is the least-verified axiom (confidence 65, no formal proof, "provisional" label). A Lean 4 proof of the evolution axiom's consistency would cost relatively little and close a gap in the foundation.

**R5. Activate the knowledge graph strategically.** Two high-priority questions (QBP divergence, quaternionic path integrals) have zero investigation progress. Use the gaps analysis to drive Research Team priorities.

**R6. Address the Tsirelson bound question early.** Before investing in Sprint 6 implementation, have Theory Team produce a position paper on whether quaternionic QM necessarily violates the Tsirelson bound and, if so, what constraints could prevent it. This is the project's highest-risk item: if the answer is "QBP necessarily violates information causality," the project must decide how to respond before committing to the Bell experiment.

### The Bottom Line

*QBP has built a cathedral of process on a foundation that, so far, is confirmed solid but indistinguishable from the building next door. The next 2-3 sprints will determine whether this cathedral has a unique address. The key is not to delay that determination by routing through problems (Lamb Shift, g-2) that require theoretical machinery the project does not yet possess, when the existential question (Bell's Theorem) is answerable with less — though still formidable — theoretical development.*

*The recommendation is clear: finish the double-slit, research the tensor product, then go straight to the experiments that will tell us whether we are building something new or something beautiful.*

---

**Oppenheimer**
Strategic AI Project Lead
QBP Initiative
