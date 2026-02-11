# QBP Knowledge Graph

This directory contains structured knowledge entries produced during Research Sprints.

---

## Purpose

The knowledge graph captures:
- **Sources** — Papers, books, and documents reviewed
- **Concepts** — Scientific ideas and terms defined
- **Claims** — Assertions made with supporting evidence
- **Questions** — Open research questions and their status
- **Relationships** — How entries connect to each other

---

## Directory Structure

```
knowledge/
├── README.md           # This file
├── sources/            # Source entries (papers, books)
├── concepts/           # Concept definitions
├── claims/             # Claims with evidence
├── questions/          # Open research questions
└── index.yaml          # Master index of all entries
```

---

## Schema

### Source Entry

```yaml
# sources/arxiv-2208-02334.yaml
id: source-arxiv-2208-02334
type: Source
category: paper  # paper, book, website, internal

metadata:
  title: "Knowledge Graph-Based Systematic Literature Review Automation"
  authors:
    - name: "Author Name"
      affiliation: "Institution"
  date: 2022-07-06
  url: https://arxiv.org/abs/2208.02334
  doi: null
  venue: "arXiv preprint"

abstract: |
  Brief summary of the source content.

quotes:
  - id: q1
    text: "Exact quote from the source"
    location: "Section 2.1, paragraph 3"
    page: 4
    relevance: "Why this quote matters to QBP"

  - id: q2
    text: "Another important quote"
    location: "Conclusion"
    relevance: "Key finding"

tags:
  - knowledge-graph
  - systematic-review
  - automation

relationships:
  - type: cites
    target: source-other-paper
  - type: defines
    target: concept-knowledge-graph
  - type: asserts
    target: claim-kg-enables-synthesis

notes: |
  Free-form notes about this source.

added_by: claude
added_date: 2026-02-10
research_sprint: 0R
```

### Concept Entry

```yaml
# concepts/quaternion-state.yaml
id: concept-quaternion-state
type: Concept

term: "Quaternion State Representation"
aliases:
  - "quaternion state"
  - "QBP state"

definition: |
  In QBP, a spin-1/2 quantum state is represented as a pure unit quaternion
  ψ with real part zero and |ψ| = 1. The space of such quaternions is
  isomorphic to S², the Bloch sphere.

formal_definition: |
  ψ ∈ ℍ such that Re(ψ) = 0 and |ψ|² = 1

sources:
  - source-qbp-paper
  - source-hamilton-1843

related_concepts:
  - concept-bloch-sphere
  - concept-pauli-algebra

tags:
  - quantum-mechanics
  - quaternions
  - foundations

added_by: claude
added_date: 2026-02-10
```

### Claim Entry

```yaml
# claims/qbp-matches-qm-single-particle.yaml
id: claim-qbp-matches-qm-single-particle
type: Claim

statement: |
  QBP predictions match standard quantum mechanics exactly for
  single-particle spin-1/2 systems.

context: |
  This is expected because quaternions (ℍ) are isomorphic to the
  Pauli algebra underlying SU(2).

evidence:
  - type: proof
    source: source-qbp-stern-gerlach-proof
    description: "Lean 4 proofs verify P(+) = cos²(θ/2)"
    strength: strong

  - type: simulation
    source: source-qbp-angle-dependent-sim
    description: "Monte Carlo simulation matches theory within 3σ"
    strength: supporting

counterevidence: []

status: established  # proposed, supported, established, contested, refuted

implications:
  - "Single-particle experiments validate QBP but don't distinguish it from QM"
  - "Must look to multi-particle systems for novel predictions"

tags:
  - validation
  - single-particle
  - experiment-01b

added_by: claude
added_date: 2026-02-10
```

### Question Entry

```yaml
# questions/qbp-divergence.yaml
id: question-qbp-divergence
type: Question

question: "Where do QBP predictions diverge from standard quantum mechanics?"

context: |
  QBP matches QM for single-particle systems by construction (quaternion
  isomorphism to Pauli algebra). Novel predictions, if any, must emerge
  in multi-particle systems or specific experimental regimes.

status: open  # open, partially-answered, answered, superseded

priority: high

related_issues:
  - 167  # GitHub issue number

investigation:
  - date: 2026-02-10
    finding: "Single-particle match is mathematically necessary"
    source: source-qbp-proof-review

  - date: null
    finding: null
    source: null

potential_approaches:
  - "Analyze Bell inequality predictions"
  - "Investigate multi-particle entanglement"
  - "Look for octonion extensions"

tags:
  - novel-predictions
  - foundations
  - high-priority

added_by: claude
added_date: 2026-02-10
research_sprint: 0R
```

---

## Relationships

Entries connect via typed relationships:

| Relationship | From | To | Meaning |
|--------------|------|-----|---------|
| `cites` | Source | Source | A cites B in its references |
| `defines` | Source | Concept | Source introduces/defines concept |
| `asserts` | Source | Claim | Source makes this claim |
| `supports` | Evidence | Claim | Evidence supports the claim |
| `contradicts` | Evidence | Claim | Evidence contradicts the claim |
| `raises` | Claim/Source | Question | This raises the question |
| `answers` | Evidence | Question | This provides an answer |
| `related_to` | Any | Any | General semantic relationship |
| `supersedes` | Entry | Entry | New entry replaces old |

---

## Quotes

Quotes are first-class entities within source entries:

```yaml
quotes:
  - id: q1                    # Unique within this source
    text: "Exact quote"       # Verbatim from source
    location: "Section 2.1"   # Where in the source
    page: 4                   # Page number if applicable
    relevance: "Why it matters"  # Connection to QBP
```

**Quote guidelines:**
- Use exact text (copy-paste when possible)
- Include enough context to understand meaning
- Specify precise location for verification
- Explain relevance to QBP research

---

## Tags

Common tags for categorization:

**Disciplines:**
- `physics`, `mathematics`, `chemistry`, `optics`, `engineering`, `software`

**Topics:**
- `quaternions`, `quantum-mechanics`, `spin`, `measurement`, `entanglement`

**Status:**
- `foundations`, `validation`, `novel-predictions`, `open-question`

**Priority:**
- `high-priority`, `low-priority`, `blocking`

---

## Usage

### Adding an Entry

1. Create YAML file in appropriate subdirectory
2. Follow schema for entry type
3. Add relationships to existing entries
4. Update `index.yaml` with new entry
5. Commit with descriptive message

### Querying the Graph

Simple queries via grep:
```bash
# Find all sources about quaternions
grep -l "quaternions" knowledge/sources/*.yaml

# Find claims with strong evidence
grep -l "strength: strong" knowledge/claims/*.yaml

# Find open questions
grep -l "status: open" knowledge/questions/*.yaml
```

For complex queries, use the (future) knowledge graph tooling.

### Validation

All entries should:
- Have unique IDs
- Follow the schema
- Include required fields
- Reference existing entries correctly

---

## Integration with Research Sprints

| Sprint Phase | Knowledge Graph Activity |
|--------------|--------------------------|
| Question Formulation | Create/update Question entries |
| Source Discovery | Create Source entries |
| Extraction | Add quotes, link concepts |
| Synthesis | Create Claim entries, add relationships |
| Integration | Link to issues, update index |

---

## Future Enhancements

- [ ] JSON-LD export for semantic web compatibility
- [ ] SQLite index for efficient querying
- [ ] Visualization of graph structure
- [ ] Automated validation of schema
- [ ] Integration with Lean 4 proofs
