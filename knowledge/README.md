# QBP Hypergraph Knowledge System

This directory contains the QBP research knowledge base, stored as a native hypergraph using Hypergraph-DB.

---

## Quick Start

```bash
# Install dependencies
pip install -r scripts/requirements-knowledge.txt

# View summary
python scripts/qbp_knowledge.py summary

# Find research gaps
python scripts/qbp_knowledge.py query gaps

# Visualize
python scripts/qbp_knowledge.py viz --output graph.png

# Open interactive web visualization
python scripts/qbp_knowledge.py viz --web
```

---

## Architecture

**Data Store:** `knowledge/qbp.hgdb` — Hypergraph-DB native format
**API:** `scripts/qbp_knowledge.py` — Python wrapper with CLI
**Analysis:** HyperNetX for advanced queries

---

## Data Model

### Vertices (Entities)

| Type | Required Fields | Description |
|------|-----------------|-------------|
| **Source** | type, title | Papers, books, internal docs |
| **Concept** | type, term | Scientific ideas and definitions |
| **Claim** | type, statement | Assertions with evidence |
| **Question** | type, question | Open research questions |
| **Proof** | type, lean_file | Formal Lean 4 proofs |

### Hyperedges (N-ary Relationships)

| Type | Min Members | Description |
|------|-------------|-------------|
| **evidence_chain** | 3 | Claim + 2+ supporting sources |
| **equivalence** | 2 | Mathematically equivalent structures |
| **theory_axioms** | 3 | Axioms that define a theory |
| **research_cluster** | 2 | Related questions forming a theme |
| **proof_link** | 2 | Claim linked to Lean 4 proof |
| **emergence** | 2 | Concepts yielding emergent property |
| **investigation** | 2 | Question + investigation sources |

---

## Python API

```python
from scripts.qbp_knowledge import QBPKnowledge

# Load or create knowledge base
kb = QBPKnowledge("knowledge/qbp.hgdb")

# Add vertices
kb.add_source("furey-2016", "Standard Model from an Algebra?",
              authors=["Cohl Furey"], tags=["octonions"])
kb.add_concept("octonion-algebra", "Octonion Algebra",
               definition="8-dimensional non-associative division algebra")
kb.add_claim("octonion-generations", "Octonions accommodate 3 generations",
             status="proposed", confidence_tier=2)
kb.add_question("octonion-physics", "What physics do octonions predict?",
                status="open", priority="high")

# Add hyperedges
kb.add_evidence_chain("claim:octonion-generations",
                      ["source:furey-2016", "source:other-paper"],
                      confidence_tier=2)
kb.add_proof_link("claim:cosine-squared", "proof:lean-angle",
                  theorem="measurement_probability_formula")

# Research queries
weak = kb.find_weak_claims()       # Claims with < 2 evidence sources
unproven = kb.find_unproven_claims()  # Claims without proof_link
gaps = kb.find_research_gaps()     # Open questions without investigation
bridges = kb.find_bridge_concepts()  # Concepts in multiple hyperedges

# Trace evidence for a claim
evidence = kb.trace_evidence("claim:qbp-cosine-squared")

# Coverage report
report = kb.coverage_report()

# Save
kb.save()
```

---

## CLI Reference

```bash
# Summary
python scripts/qbp_knowledge.py summary

# Queries
python scripts/qbp_knowledge.py query weak-claims
python scripts/qbp_knowledge.py query unproven
python scripts/qbp_knowledge.py query gaps
python scripts/qbp_knowledge.py query bridges

# Information
python scripts/qbp_knowledge.py info claim:qbp-cosine-squared
python scripts/qbp_knowledge.py evidence claim:qbp-cosine-squared
python scripts/qbp_knowledge.py report

# Visualization
python scripts/qbp_knowledge.py viz --output graph.png
python scripts/qbp_knowledge.py viz --web --port 8080
```

---

## Research Workflow Integration

| Research Phase | Knowledge System Activity |
|----------------|---------------------------|
| Question Formulation | Add Question vertices |
| Source Discovery | Add Source vertices |
| Concept Extraction | Add Concept vertices, link to sources |
| Claim Formation | Add Claim vertices with evidence_chain |
| Formal Verification | Add Proof vertices, create proof_link |
| Gap Analysis | Run `query gaps` to find uninvestigated questions |

---

## Files

```
knowledge/
├── README.md           # This file
├── qbp.hgdb           # Hypergraph database (Hypergraph-DB format)
├── sources/           # Legacy YAML (deprecated)
├── concepts/          # Legacy YAML (deprecated)
├── claims/            # Legacy YAML (deprecated)
├── questions/         # Legacy YAML (deprecated)
└── index.yaml         # Legacy index (deprecated)
```

---

## Migration from YAML

The system has migrated from YAML files to Hypergraph-DB. Legacy YAML files are preserved for reference but no longer used.

To migrate additional YAML entries:
```python
from scripts.qbp_knowledge import QBPKnowledge
import yaml

kb = QBPKnowledge("knowledge/qbp.hgdb")

with open("knowledge/sources/example.yaml") as f:
    data = yaml.safe_load(f)

kb.add_source(data["id"], data["metadata"]["title"], **data)
kb.save()
```

---

## References

- [Hypergraph-DB Documentation](https://imoonlab.github.io/Hypergraph-DB/)
- [HyperNetX Documentation](https://hypernetx.readthedocs.io/)
- [QBP Hypergraph Design Plan](../docs/plans/hypergraph_knowledge_system.md)
