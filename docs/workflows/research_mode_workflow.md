# Research Mode Workflow

*A workflow for conducting systematic research during Research Sprints.*

---

## Overview

Research Mode enables structured investigation of scientific questions, literature review, and theoretical exploration. Unlike Sprint Mode (which produces code, proofs, and visualizations), Research Mode produces **knowledge graph entries** and **synthesis documents** that inform future work.

**Key insight:** Research is not just reading — it's the systematic transformation of information into structured, reusable knowledge.

---

## When to Use Research Mode

Research Mode is appropriate when:
- Starting a Research Sprint (e.g., 0R, 1R)
- Investigating questions raised by experimental work
- Exploring new domains before implementation
- Building foundational understanding for future sprints

Research Mode is NOT appropriate when:
- Implementing known solutions (use Sprint Mode)
- Fixing bugs or cleanup (use Housekeeping Mode)
- The question has a clear, known answer

---

## Triggering Research Mode: The Research Gate

Research Mode is formally triggered by the **Research Gate** checkpoint script. After every sprint's Theory Refinement, run:

```bash
python scripts/research_gate.py --scope sprint-N+1 experiment-NN
```

| Verdict | Action |
|---------|--------|
| **PASS** (exit 0) | Proceed directly to Sprint N+1 Phase 1 — no research needed |
| **BLOCK** (exit 1) | Enter Research Mode to resolve scoped weak claims and research gaps |

**What the gate checks:**
- **Weak claims** tagged with the next sprint's scope (claims lacking evidence chains)
- **Research gaps** tagged with the next sprint's scope (open questions without investigations)

When the gate returns BLOCK, the scoped findings become the starting research questions for Research Mode.

**Manual trigger:** James can always invoke Research Mode manually regardless of gate output — the gate is a safety net, not a straitjacket. The Sprint 3 Pre-Sprint Research (#255) was triggered manually before the gate existed.

**After research completes:** Re-run the gate to confirm PASS before proceeding to Phase 1.

---

## Research Scope Modes

### Broad Research (Systematic Review)

For landscape mapping and meta-analysis:

**Use when:**
- Starting a new research area
- Need comprehensive coverage of prior work
- Identifying gaps in the field
- Synthesizing across multiple sources

**Method:** [PRISMA-style](https://www.prisma-statement.org/) systematic review
1. Define research question
2. Establish inclusion/exclusion criteria
3. Search multiple sources
4. Screen and select relevant works
5. Extract and synthesize findings
6. Document in knowledge graph

**Deliverables:**
- Knowledge graph entries for each source
- Synthesis document with findings
- Gap analysis identifying open questions

### Focused Research (Targeted Investigation)

For deep dives on specific questions:

**Use when:**
- Specific question raised by an issue
- Resolving a contradiction or ambiguity
- Following a citation chain
- Understanding a specific technique

**Method:** Depth-first investigation
1. Start with the specific question
2. Follow references until resolved
3. Document key findings with quotes
4. Link to existing knowledge graph entries

**Deliverables:**
- Knowledge graph entries for new sources
- Answer document with evidence
- Links to related entries

---

## Research Methodology by Discipline

### Physics

**Core framework:** Hypothesis → Prediction → Test → Refine

Based on [Lakatos's methodology](https://en.wikipedia.org/wiki/Imre_Lakatos): research programmes have a "hard core" of assumptions protected by a "protective belt" of auxiliary hypotheses. Anomalies don't immediately falsify the core — they prompt refinement of the belt.

**QBP application:**
- Hard core: Quaternion state representation, measurement postulates
- Protective belt: Specific formulas, implementation details
- Research goal: Identify where QBP diverges from standard QM

### Mathematics

**Core framework:** Axiom → Theorem → Proof → Generalization

**Principles:**
- First-principles reasoning (axiom-first, not simulation-fitted)
- Rigor over intuition (proofs must be formal)
- Generalization (seek broader patterns)

**QBP application:**
- Verify axioms are self-consistent
- Prove theorems without relying on simulation results
- Look for connections to established mathematics

### Chemistry

**Core framework:** Structure → Mechanism → Kinetics → Thermodynamics

**Principles:**
- Atomic/molecular structure determines behavior
- Reaction mechanisms explain transformations
- Energy landscapes govern feasibility

**QBP application:**
- How does quaternion formalism represent molecular states?
- Can QBP predict chemical reaction outcomes?
- Connection to quantum chemistry methods

### Optics

**Core framework:** Wave → Interference → Polarization → Detection

**Principles:**
- Wave phenomena underlie optical behavior
- Polarization is deeply connected to spin
- Measurement devices have their own physics

**QBP application:**
- Quaternions naturally represent polarization states
- Connection to Jones calculus
- Optical experiments as QBP test cases

### Engineering

**Core framework:** Requirements → Design → Implementation → Verification → Validation

**Key distinction:**
- **Verification:** Did we build the thing right? (internal consistency)
- **Validation:** Did we build the right thing? (matches real world)

Based on [computational science best practices](https://royalsocietypublishing.org/doi/10.1098/rsta.2020.0409):
- Version control all artifacts
- Document all parameters
- Automate reproduction

**QBP application:**
- Simulation verification against analytical solutions
- Validation against experimental data
- Reproducibility of all results

### Software

**Core framework:** Specify → Implement → Test → Refactor

**Principles:**
- [Ten Simple Rules for Reproducible Computational Research](https://pmc.ncbi.nlm.nih.gov/articles/PMC3812051/)
- Code is documentation
- Tests encode requirements

**QBP application:**
- All simulations version-controlled
- Ground truth documents specify expected results
- CI enforces reproducibility

---

## Research Team Personas

See `TEAMS.md` for full persona details. Research Mode activates:

| Persona | Role | When to Invoke |
|---------|------|----------------|
| **Curie** | Literature Surveyor | Systematic reviews, source discovery |
| **Poincaré** | Hypothesis Generator | Novel directions, creative synthesis |
| **Fisher** | Experimental Designer | Statistical rigor, test design |
| **Faraday** | Cross-Domain Synthesizer | Connecting disciplines |
| **Otlet** | Knowledge Architect | Structuring findings, graph design |

---

## Knowledge Graph System

Research produces entries in a structured knowledge graph. See `knowledge/README.md` for the full schema.

### Entity Types

| Type | Description | Example |
|------|-------------|---------|
| `Source` | Paper, book, or document | arXiv:2208.02334 |
| `Concept` | Scientific idea or term | "Quaternion state representation" |
| `Claim` | Assertion made by a source | "QBP matches QM for single-particle systems" |
| `Evidence` | Data supporting a claim | Simulation results, proofs |
| `Question` | Open research question | "Where does QBP diverge from QM?" |

### Relationships

| Relationship | Description |
|--------------|-------------|
| `cites` | Source → Source |
| `defines` | Source → Concept |
| `asserts` | Source → Claim |
| `supports` | Evidence → Claim |
| `contradicts` | Evidence → Claim |
| `raises` | Claim → Question |
| `answers` | Evidence → Question |

### Entry Format

Each entry is a YAML file in `knowledge/`:

```yaml
id: source-arxiv-2208-02334
type: Source
category: paper
metadata:
  title: "Knowledge Graph-Based Systematic Literature Review Automation"
  authors:
    - name: "Nada Sahlab"
    - name: "Hesham Kahoul"
  url: https://arxiv.org/abs/2208.02334
  date: 2022-07-06

quotes:
  - id: q1
    text: "with the massive availability of publications at a rapid growing rate..."
    location: "Abstract"
    relevance: "Motivation for automated literature review"

tags:
  - knowledge-graph
  - systematic-review

relationships:
  - type: defines
    target: concept-knowledge-graph  # Add when concept exists
```

---

## Research Sprint Workflow

### Phase 1: Question Formulation

1. Identify research questions from issues or gaps
2. Classify as broad (systematic) or focused (targeted)
3. Define scope and success criteria
4. Create tracking issue

### Phase 2: Source Discovery

1. Search relevant databases (arXiv, journals, textbooks)
2. Follow citation chains
3. Create knowledge graph entries for each source
4. Tag with relevant concepts

### Phase 3: Extraction

1. Read sources with specific questions in mind
2. Extract quotes with precise locations
3. Identify claims and evidence
4. Note contradictions and gaps

### Phase 4: Synthesis

1. Connect entries via relationships
2. Identify patterns across sources
3. Write synthesis document
4. Update concept definitions

### Phase 5: Integration

1. Link findings to QBP codebase
2. Create issues for action items
3. Update relevant documentation
4. Close research question (or document why it remains open)

---

## Deliverables

Every Research Sprint produces:

1. **Knowledge graph entries** — Structured YAML in `knowledge/`
2. **Synthesis document** — Narrative summary in `research/`
3. **Issue updates** — Answers to questions, new questions raised
4. **Action items** — Issues for implementation work

---

## Quality Criteria

### For Sources
- Peer-reviewed or established authority
- Properly cited with URL/DOI
- Quotes are exact with locations

### For Claims
- Clearly stated
- Evidence linked
- Contradicting evidence noted

### For Synthesis
- Covers all sources
- Identifies patterns
- Acknowledges gaps
- Actionable conclusions

---

## Research Mode vs Sprint Mode

| Aspect | Research Mode | Sprint Mode |
|--------|---------------|-------------|
| **Goal** | Understand | Implement |
| **Output** | Knowledge graph, synthesis docs | Code, proofs, visualizations |
| **Success** | Questions answered | Acceptance criteria met |
| **Personas** | Research Team | Theory/Red/Dev Teams |
| **Duration** | Variable | 5 phases + Theory Refinement |

---

## Integration with Herschel

Research Mode integrates with the existing Herschel project coordination system.

### Session-Start Check

At the start of every session, Herschel reads `SPRINT_STATUS.md` to understand current lifecycle position. For Research Sprints:

1. **Check Research Sprint status** — Is a Research Sprint active (0R, 1R, etc.)?
2. **Identify current phase** — Which research phase is in progress?
3. **Review knowledge graph state** — Are there pending entries or open questions?
4. **Verify alignment** — Does planned work align with research goals?

### Critical Path Audit

When research is on the critical path, the Critical Path Audit should:

1. **Track Research Sprint issues** — Ensure tracking issues exist for each research question
2. **Verify knowledge graph entries** — Check that sources and findings are being documented
3. **Monitor question status** — Flag open questions blocking downstream work

### SPRINT_STATUS.md Updates

For Research Sprints, `SPRINT_STATUS.md` should include:

```markdown
## Research Sprint 0R: [Topic]

**Status:** In Progress / Complete
**Current Phase:** Question Formulation / Discovery / Extraction / Synthesis / Integration

### Research Questions
- [ ] Question 1 (tracking issue #XXX)
- [ ] Question 2 (tracking issue #XXX)

### Knowledge Graph Entries Added
- sources: N new entries
- concepts: N new entries
- claims: N new entries
```

---

## Philosophy: Structure Supports Thinking

> "It is through science that we prove, but through intuition that we discover." — Henri Poincaré

This framework exists to **support** creative scientific thinking, not replace it. The structure provides:

- **Traceability** — Know where ideas came from
- **Reproducibility** — Others can follow your path
- **Collaboration** — Shared vocabulary and format

But the structure should never become bureaucratic overhead. If you have an insight while shaving, write it down! The knowledge graph captures serendipity too — just tag it appropriately.

**Signs the process is working:**
- Discoveries get documented and built upon
- Questions get answered (or refined into better questions)
- New connections emerge from structured data

**Signs to course-correct:**
- More time on forms than thinking
- Entries become rote rather than insightful
- Questions stay open indefinitely without progress

---

## Issue Lifecycle

Research issues follow a structured lifecycle integrated with the project board.

### Issue Types

| Type | Example | Sprint field |
|------|---------|-------------|
| **Pre-sprint research** | Blocking questions before Phase 1 | Research Sprint NR |
| **Open research** | Polychromatic beams, charge scale | House Keeping (with `type: research` label) |
| **Theory Refinement** | Post-experiment analysis | Sprint N (the sprint it belongs to) |

### Creation Checklist

Follow the **[Research Issue Creation Checklist](../../CONTRIBUTING.md#research-issue-creation-checklist)** in CONTRIBUTING.md. Every research issue needs: title convention, body with research question and AC, `type: research` label, board placement, Sprint = "House Keeping" (or Research Sprint NR if blocking), Status = "Todo".

### Triage

Research issues in the backlog need periodic triage so they don't rot:

| Signal | Meaning | Action |
|--------|---------|--------|
| **Blocking next sprint** | Research Gate identifies this as required | Move to Research Sprint NR, work immediately |
| **Informs upcoming experiment** | Not blocking, but would improve next sprint quality | Surface during sprint retrospective |
| **Open curiosity** | Interesting but no experiment depends on it | Keep in backlog, revisit during housekeeping mode |

**Triage trigger:** During each sprint retrospective, scan research backlog and ask: "Does any open research item block or significantly inform the next sprint?" If yes, promote to Research Sprint NR.

### Completion

Same rules as any issue:
- PR with `Closes #X` (or manual close if no code change needed)
- AC verification in review
- Research conclusions documented in knowledge graph

---

## References

- [Lakatos: Methodology of Scientific Research Programmes](https://en.wikipedia.org/wiki/Imre_Lakatos)
- [PRISMA 2020 Statement](https://www.prisma-statement.org/)
- [Reliability and Reproducibility in Computational Science](https://royalsocietypublishing.org/doi/10.1098/rsta.2020.0409)
- [Ten Simple Rules for Reproducible Computational Research](https://pmc.ncbi.nlm.nih.gov/articles/PMC3812051/)
- [Research Graph in JSON-LD](https://dl.acm.org/doi/10.1145/3041021.3053052)
- [Knowledge Graph-Based Systematic Literature Review](https://arxiv.org/abs/2208.02334)
