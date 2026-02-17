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

### [Parallel Sub-Agent Workflow](parallel_subagent_workflow.md)

Five-phase execution model using Claude's parallel sub-agents:
1. Explore (parallel) → 2. Contract (serial) → 3. Build (parallel) → 4. Run (serial) → 5. Review (serial)

### [Results Versioning Protocol](results_versioning.md)

Protocol for managing experiment result files across sprint rework cycles. Uses versioned subdirectories (`v1/`, `v2/`, ...) with `CURRENT` symlinks for consumer discovery.

### [Claude-Gemini Communication](claude_gemini_communication.md)

Prescriptive patterns for Claude-Gemini collaboration: pre-implementation critique, structured debate, session-based reviews, human tie-breaking, and interactive questions.

### [Review Tiers](review_tiers.md)

Tiered review system (L0-L3) with BLOCKING criteria, human visual review gates, and CONFLICT resolution templates.

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
