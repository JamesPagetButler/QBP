# Research Sprint 0R: Plan

**Sprint:** 0R (Post-Sprint 2, Pre-Theory Refinement)
**Status:** In Progress
**Tracking Issue:** #212

## Executive Summary

Research Sprint 0R addresses foundational theoretical questions that emerged during Sprints 1-2. The central question is: **Is QBP a reformulation of QM or a distinct theory with falsifiable predictions?**

## Dependency Analysis

Despite priority labels, dependencies determine execution order:

```
#6 (Premise Review)
  ├── #136 (Observable Formalism) ─┐
  └── #20 (Scalar Component)       │
                                   ▼
                    #232 (Division Algebra Justification)
                                   │
                     ┌─────────────┼─────────────┐
                     ▼             ▼             ▼
              #233 (Intuitive)  #234 (Geometric)  #167 (QBP Divergence)
```

## Execution Order

### Phase 1: Foundations (Unblocks everything)

| Order | Issue | Title | Output |
|-------|-------|-------|--------|
| 1.1 | #6 | Initial Project Premise Review | Premise validation document |
| 1.2 | #136 | Observable → Operator Formalism | DESIGN_RATIONALE update |
| 1.3 | #20 | Scalar Component Meaning | Literature review + position statement |

### Phase 2: Core Theory

| Order | Issue | Title | Output |
|-------|-------|-------|--------|
| 2.1 | #232 | Division Algebra Justification | Why quaternions (not ℂ, not 𝕆) |

### Phase 3: Synthesis (Can parallelize)

| Order | Issue | Title | Output |
|-------|-------|-------|--------|
| 3.1 | #233 | Intuitive Physical Explanation | Undergraduate-accessible writeup |
| 3.2 | #234 | Geometric/Spacetime Interpretation | Fibre bundle analysis |
| 3.3 | #167 | QBP Divergence from QM | **Critical deliverable** |

### Phase 4: Infrastructure (Independent)

| Order | Issue | Title | Output |
|-------|-------|-------|--------|
| 4.1 | #123 | Lean 4 as Experiment Engine | Feasibility assessment |
| 4.2 | #203 | 3D Interactive Visualizations | Tech stack recommendation |

## Research Methodology

### Tools
- **Knowledge Base:** `python scripts/qbp_knowledge.py` — capture all findings
- **Literature:** Web search, arXiv, Furey papers, Adler's quaternionic QM
- **Gemini Theory Team:** Furey + Feynman personas for review

### Per-Issue Process
1. Read existing DESIGN_RATIONALE sections
2. Literature search (if needed)
3. Draft findings
4. Add to knowledge base as Claims/Concepts
5. Update DESIGN_RATIONALE.md
6. Close issue with summary

### Knowledge Base Integration

Each research finding should be captured:
```bash
# Add new concepts discovered
python scripts/qbp_knowledge.py add concept <id> "<term>" --definition "..."

# Add claims with evidence
python scripts/qbp_knowledge.py add claim <id> "<statement>" --status proposed

# Link evidence chains
python scripts/qbp_knowledge.py link evidence <claim-id> <source-ids...>
```

## Exit Criteria

- [ ] All P1 issues resolved (#167, #136)
- [ ] P2 foundation issues resolved (#6, #20, #232, #233, #234)
- [ ] Key findings documented in DESIGN_RATIONALE.md
- [ ] Knowledge base updated with new concepts/claims
- [ ] Clear answer to: "Where does QBP diverge from QM?"

## Key Questions to Answer

1. **Why quaternions?** What do they provide that complex numbers don't?
2. **Observable formalism:** How do pure quaternions relate to Hermitian operators?
3. **Scalar component:** What does Re(ψ) ≠ 0 mean physically?
4. **Half-angle:** Why does θ/2 appear? Physical intuition?
5. **Divergence:** Where might QBP differ from standard QM?

---

*Plan created: 2026-02-11*
