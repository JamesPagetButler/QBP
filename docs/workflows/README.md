# QBP Workflows

This directory contains workflow documentation for the QBP project.

## Available Workflows

### [Collaborative Theory Workflow](collaborative_theory_workflow.md)

Used for Phase 1 (Ground Truth) and Phase 4 (Formal Proof) work.

**Process:**
1. **Parallel Exploration** - Claude and Gemini independently produce theory documents
2. **Bell's Evaluation** - Critical analysis comparing both approaches
3. **Human Review** - Guidance and approval to proceed
4. **Claude Synthesis** - Integration of best elements from both
5. **Standard Review** - Red Team + Gemini review of final PR

**Why this workflow?**
- Leverages Gemini's structural clarity + Claude's explanatory depth
- Bell catches issues before PR stage
- Produces more rigorous, insightful theory documents

---

## Workflow Assignment by Phase

| Phase | Workflow | Primary Agent |
|-------|----------|---------------|
| Phase 1: Ground Truth | Collaborative | Claude + Gemini → Claude synthesizes |
| Phase 2: Implementation | Single-agent | Gemini |
| Phase 3: Visualization | Single-agent | Claude |
| Phase 4: Formal Proof | Collaborative | Claude + Gemini → Claude synthesizes |
| Phase 5: Publication | Single-agent | Claude |

---

## Personas

| Persona | Role |
|---------|------|
| **Sabine** | Experimentalist - statistical rigor, methodology |
| **Grothendieck** | Mathematician - proofs, logical structure |
| **Knuth** | Computer Scientist - algorithms, code quality |
| **Der Depperte** | Writer & Communicator - clarity, accessibility, wonder |
| **Bell** | Theory Evaluator - understanding vs. pattern-matching (also Expert Panel member) |

> **Full persona registry:** See [docs/personas/README.md](../personas/README.md) for all 14 personas.
