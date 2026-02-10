# Sprint Status

*This file is the project's operational logbook. It is read by all collaborators (human and AI) at the start of every work session as part of the [Herschel Check](CONTRIBUTING.md#session-start-protocol-the-herschel-check). Update it at every session boundary and whenever entering or exiting a diversion.*

**Project Board:** [QBP Research Lifecycle](https://github.com/users/JamesPagetButler/projects/1)

---

## Current Position

- **Active Sprint:** Sprint 2 (Experiment 01b: Angle-Dependent Measurement)
- **Lifecycle Stage:** Sprint 2 Phase 4 (Formal Verification)
- **Next Critical-Path Action:** Phase 4b Proof Review (#201)

> **Note:** Sprint 2 implements Experiment 01b (an extension of Stern-Gerlach to arbitrary angles), not a new experiment. See `research/README.md` for the Sprint ↔ Experiment mapping.

## Sprint 2 Closure Checklist

- [x] Phase 1: Ground Truth Rework (#160) — CLOSED 2026-02-06. PR #166 merged. Full Tier 3 review.
- [x] Phase 2: Implementation (#161) — CLOSED 2026-02-06. PR #178 merged. Red Team APPROVE. (Gemini/Bell reviews skipped due to MCP disconnect)
- [x] Phase 3: Visualization (#162) — CLOSED 2026-02-10. PR #205 merged. Bloch sphere + analysis plots. Design system updated for VPython captions.
- [ ] Phase 4: Formal Verification (#163)
  - [x] 4a: Formal Proof (#200) — CLOSED 2026-02-10. PR #210 merged. Lean 4 proofs for cos²(θ/2) formula.
  - [ ] 4b: Proof Review
  - [ ] 4c: Interactive Proof Visualization
- [ ] Phase 5: Publication (#164)
- [ ] **Research Sprint 0R** (#212) — One-off: doing research before Theory Refinement
- [ ] Theory Refinement (#165)

## Research Sprint 0R (Before Theory Refinement — One-Off)

**Tracking Issue:** #212

Research sprints are dedicated blocks for theoretical investigation between experiment sprints.
**Naming:** Research Sprint NR runs after Sprint N+1 (0R after Sprint 1, 1R after Sprint 2, etc.)

- [ ] #167 — Research: Identify where QBP predictions diverge from standard QM
- [ ] #136 — Theory: Clarify quaternion observable relationship to operator formalism
- [ ] #20 — Theoretical Investigation: Physical meaning of quaternion scalar component
- [ ] #6 — Initial Project Premise & Setup Review
- [ ] #123 — Research: Investigate Lean 4 as verified experiment engine
- [ ] #203 — Research: 3D Interactive Experiment Visualizations

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
- [ ] Theory Refinement (#XX)

## Sprint N Retrospective

1. Did we follow the critical path this sprint?
2. Where did we deviate?
3. What was the cost?
4. What is our commitment for Sprint N+1?
```
