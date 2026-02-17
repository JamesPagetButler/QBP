# QBP Hypergraph Knowledge System

This directory contains the QBP research knowledge base, stored as a SQLite hypergraph database.

---

## Quick Start

```bash
# Install dependencies
pip install -r scripts/requirements-knowledge.txt

# View summary
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db summary

# Query concepts by tag
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db query --type Concept --tag foundations

# Find research gaps
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db gaps

# Export to HIF format
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db export --format hif --output qbp.hif.json
```

---

## Architecture

```
knowledge/qbp.db (SQLite)     ← Source of truth
    ↓
qbp_knowledge_sqlite.py       ← API + SQL queries
    ↓
├── HIF export                ← Interchange format (HyperNetX, XGI compatible)
├── HyperNetX                 ← Mathematical analysis
└── D3.js                     ← Interactive visualization
```

### Why SQLite?

| Feature | SQLite | Hypergraph-DB (old) |
|---------|--------|---------------------|
| Querying | SQL (fast, flexible) | Python loops |
| Concurrent access | Yes | No |
| ACID transactions | Yes | No |
| Browser tools | DB Browser, etc. | None |
| Standard format | Yes | Pickle binary |

---

## Data Model

### Schema

```sql
-- Vertices table (nodes)
CREATE TABLE vertices (
    id TEXT PRIMARY KEY,        -- e.g., "concept:quaternion-state"
    type TEXT NOT NULL,         -- Source, Concept, Claim, Question, Proof
    data JSON NOT NULL,         -- All attributes as JSON
    created_at TIMESTAMP
);

-- Hyperedges table
CREATE TABLE hyperedges (
    id TEXT PRIMARY KEY,        -- e.g., "e0_evidence_chain"
    type TEXT NOT NULL,         -- evidence_chain, proof_link, etc.
    data JSON NOT NULL,         -- Edge attributes as JSON
    created_at TIMESTAMP
);

-- Incidences (vertex-edge membership) — the hypergraph structure
CREATE TABLE incidences (
    vertex_id TEXT NOT NULL,
    edge_id TEXT NOT NULL,
    position INTEGER DEFAULT 0,
    PRIMARY KEY (vertex_id, edge_id)
);
```

### Vertex Types

| Type | Required Fields | Description |
|------|-----------------|-------------|
| **Source** | title | Papers, books, internal docs |
| **Concept** | term | Scientific ideas and definitions |
| **Claim** | statement | Assertions with evidence |
| **Question** | question | Open research questions |
| **Proof** | lean_file | Formal Lean 4 proofs |

### Hyperedge Types

| Type | Min Members | Description |
|------|-------------|-------------|
| **evidence_chain** | 2 | Claim + supporting sources |
| **equivalence** | 2 | Mathematically equivalent structures |
| **theory_axioms** | 2 | Axioms that define a theory |
| **research_cluster** | 2 | Related questions forming a theme |
| **proof_link** | 2 | Claim linked to Lean 4 proof |
| **emergence** | 2 | Concepts yielding emergent property |
| **investigation** | 2 | Question + investigation sources |

---

## Python API

```python
from scripts.qbp_knowledge_sqlite import QBPKnowledgeSQLite

# Open database
kb = QBPKnowledgeSQLite("knowledge/qbp.db")

# Add vertices
kb.add_source("furey-2016", "Standard Model from an Algebra?",
              authors=["Cohl Furey"], tags=["octonions"])
kb.add_concept("octonion-algebra", "Octonion Algebra",
               definition="8-dimensional non-associative division algebra")
kb.add_claim("octonion-generations", "Octonions accommodate 3 generations",
             status="proposed", confidence_tier=2)

# Add hyperedges
kb.add_evidence_chain("claim:octonion-generations",
                      ["source:furey-2016", "source:other"],
                      confidence_tier=2)
kb.add_proof_link("claim:cosine-squared", "proof:angle-dependent",
                  theorem="prob_up_angle_cos_sq")

# SQL-powered research queries
weak = kb.find_weak_claims()          # Claims with no evidence
unproven = kb.find_unproven_claims()  # Claims without proof_link
gaps = kb.find_research_gaps()        # Open questions uninvestigated
bridges = kb.find_bridge_concepts()   # Concepts in 3+ hyperedges

# Query with filters
concepts = kb.query_vertices(vertex_type="Concept", tag="foundations")
claims = kb.query_vertices(search="quaternion")

# Trace evidence
evidence = kb.trace_evidence("claim:cosine-squared-formula")

# Export
kb.export_hif("output.hif.json")      # HIF interchange format
H = kb.to_hypernetx()                 # HyperNetX for analysis
```

---

## CLI Reference

```bash
# Summary
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db summary

# Query vertices
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db query --type Concept
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db query --tag foundations
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db query --search quaternion

# Research queries
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db weak-claims
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db unproven
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db gaps
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db bridges

# Export
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db export --format hif --output qbp.hif.json
```

---

## Visualization

```bash
# Generate interactive visualization
python scripts/qbp_knowledge_sqlite.py --db knowledge/qbp.db visualize
```

---

## Files

```
knowledge/
├── README.md               # This file
├── qbp.db                  # SQLite hypergraph database (source of truth)
└── schemas/                # JSON validation schemas
```

> **Legacy files** (Hypergraph-DB, YAML, migration scripts) have been moved to `archive/hypergraph-db/`.

---

## Interchange Format (HIF)

The database exports to [HIF (Hypergraph Interchange Format)](https://github.com/HIF-org/HIF-standard), enabling interoperability with:

- [HyperNetX](https://hypernetx.readthedocs.io/) — Mathematical analysis
- [XGI](https://xgi.readthedocs.io/) — Higher-order network analysis
- [Hypergraphx](https://hypergraphx.readthedocs.io/) — Hypergraph algorithms

```json
{
  "network-type": "undirected",
  "metadata": { "name": "QBP Knowledge Hypergraph" },
  "nodes": [
    { "node": "concept:quaternion-state", "attrs": { "type": "Concept", ... } }
  ],
  "edges": [
    { "edge": "e0_evidence_chain", "attrs": { "type": "evidence_chain", ... } }
  ],
  "incidences": [
    { "node": "concept:quaternion-state", "edge": "e0_evidence_chain" }
  ]
}
```

---

## References

- [HIF Standard](https://github.com/HIF-org/HIF-standard) — Hypergraph Interchange Format
- [HyperNetX Documentation](https://hypernetx.readthedocs.io/)
- [SQLite JSON Functions](https://www.sqlite.org/json1.html)
- [QBP Hypergraph Design Plan](../docs/plans/hypergraph_knowledge_system.md)
