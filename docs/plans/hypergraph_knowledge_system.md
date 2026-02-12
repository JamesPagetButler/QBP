# QBP Hypergraph Knowledge System: Redesign Plan

**Status:** Draft
**Date:** 2026-02-11
**Goal:** Enable effective research to illuminate insights and progress theories rigorously

---

## Executive Summary

Redesign the QBP knowledge graph as a native hypergraph system using **Hypergraph-DB** as the core data store. This enables n-ary relationships that mirror the structure of physics theories, evidence chains, and research questions—unlocking pattern discovery and rigorous theory development.

---

## Tool Comparison

| Tool | Strengths | Weaknesses | Fit for QBP |
|------|-----------|------------|-------------|
| **[Hypergraph-DB](https://github.com/iMoonLab/Hypergraph-DB)** | Lightweight, built-in D3 visualization, HIF export, simple API, fast (1M vertices in <7s) | Less analysis depth than EasyHypergraph | **Best fit** — storage + visualization focus |
| **[EasyHypergraph](https://www.nature.com/articles/s41599-025-05180-5)** | Powerful analysis, hypergraph neural networks, integrated with EasyGraph | Overkill for knowledge graphs, ML-focused | Future option for pattern discovery |
| **[HyperNetX](https://github.com/pnnl/HyperNetX)** | Mature, good math/analysis, Matplotlib viz | Storage not primary focus | Analysis companion |

**Decision:** Use **Hypergraph-DB** as primary store, with HyperNetX for advanced analysis when needed.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    QBP Hypergraph Knowledge System              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│  │   Research   │    │   Formal     │    │  Experiment  │      │
│  │   Sprints    │───▶│   Proofs     │◀───│  Results     │      │
│  │  (Discovery) │    │   (Lean 4)   │    │  (Python)    │      │
│  └──────┬───────┘    └──────┬───────┘    └──────┬───────┘      │
│         │                   │                   │               │
│         ▼                   ▼                   ▼               │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   Hypergraph-DB                          │   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐    │   │
│  │  │ Sources │  │Concepts │  │ Claims  │  │Questions│    │   │
│  │  │(vertices)│ │(vertices)│ │(vertices)│ │(vertices)│   │   │
│  │  └────┬────┘  └────┬────┘  └────┬────┘  └────┬────┘    │   │
│  │       │            │            │            │          │   │
│  │       └────────────┴─────┬──────┴────────────┘          │   │
│  │                          │                               │   │
│  │              ┌───────────┴───────────┐                  │   │
│  │              │     Hyperedges        │                  │   │
│  │              │  (n-ary relations)    │                  │   │
│  │              └───────────────────────┘                  │   │
│  │                                                          │   │
│  │  Types: evidence_chain | equivalence | theory_axioms    │   │
│  │         emergence | research_cluster | proof_link       │   │
│  └─────────────────────────────────────────────────────────┘   │
│         │                   │                   │               │
│         ▼                   ▼                   ▼               │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│  │ Visualization│    │   Export     │    │   Query      │      │
│  │  (D3/Web)    │    │  (HIF/JSON)  │    │    API       │      │
│  └──────────────┘    └──────────────┘    └──────────────┘      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Data Model

### Vertices (Entities)

```python
# Each knowledge entry becomes a vertex
hg.add_v("source:arxiv-2208-02334", {
    "type": "Source",
    "category": "paper",
    "title": "Knowledge Graph-Based Systematic Literature Review",
    "authors": ["Sahlab", "Kahoul", "Jazdi", "Weyrich"],
    "date": "2022-07-06",
    "url": "https://arxiv.org/abs/2208.02334",
    "tags": ["knowledge-graph", "systematic-review"],
    "research_sprint": "0R",
    "added_date": "2026-02-10"
})

hg.add_v("claim:qbp-cosine-squared", {
    "type": "Claim",
    "statement": "P(+) = cos²(θ/2) for spin measurement at angle θ",
    "status": "established",
    "confidence_tier": 3,
    "tags": ["measurement", "spin", "validated"]
})

hg.add_v("concept:quaternion-state", {
    "type": "Concept",
    "term": "Quaternion State Representation",
    "definition": "Pure unit quaternion ψ with Re(ψ)=0, |ψ|=1",
    "formal_definition": "ψ ∈ ℍ : Re(ψ) = 0, |ψ|² = 1"
})

hg.add_v("question:qbp-divergence", {
    "type": "Question",
    "question": "Where do QBP predictions diverge from standard QM?",
    "status": "open",
    "priority": "high"
})
```

### Hyperedges (N-ary Relationships)

```python
# Evidence chain: claim + all supporting sources
hg.add_e(
    ("claim:qbp-cosine-squared", "proof:lean-angle-dep", "sim:monte-carlo-01b", "source:qm-textbook"),
    {
        "type": "evidence_chain",
        "confidence_tier": 3,
        "established_date": "2026-02-10",
        "description": "Multi-source evidence for cos²(θ/2) formula"
    }
)

# Mathematical equivalence class
hg.add_e(
    ("concept:quaternion-state", "concept:pauli-algebra", "concept:bloch-sphere", "concept:su2-group"),
    {
        "type": "equivalence",
        "description": "Isomorphic representations of spin-1/2 state space",
        "isomorphism_proven": True,
        "proof_ref": "proof:quaternion-pauli-iso"
    }
)

# Theory axioms (the set that defines QBP)
hg.add_e(
    ("axiom:quaternionic-states", "axiom:quaternionic-observables", "axiom:quaternionic-evolution", "postulate:measurement-rule"),
    {
        "type": "theory_axioms",
        "theory": "QBP",
        "completeness": "sufficient for single-particle",
        "open_questions": ["multi-particle extension", "entanglement formalism"]
    }
)

# Research cluster (questions that form a theme)
hg.add_e(
    ("question:qbp-divergence", "question:octonion-extension", "question:bell-prediction", "concept:multipartite-entanglement"),
    {
        "type": "research_cluster",
        "theme": "Novel QBP Predictions",
        "priority": "high",
        "target_sprint": "1R"
    }
)

# Proof-claim link (formal verification)
hg.add_e(
    ("claim:qbp-cosine-squared", "proof:lean-angle-dep", "theorem:measurement-probability-formula"),
    {
        "type": "proof_link",
        "lean_file": "proofs/QBP/AngleDependent.lean",
        "theorem_line": 142,
        "verification_status": "verified",
        "no_sorry": True
    }
)

# Emergence (phenomenon arises from combination)
hg.add_e(
    ("concept:quaternion-rotation", "concept:half-angle-formula", "concept:su2-double-cover"),
    {
        "type": "emergence",
        "emergent_property": "Spinor sign flip under 2π rotation",
        "physical_significance": "Distinguishes fermions from bosons"
    }
)
```

---

## Hyperedge Types

| Type | Arity | Purpose | Example |
|------|-------|---------|---------|
| `evidence_chain` | 3+ | Claim + all supporting evidence | cos²(θ/2) + Lean proof + simulation + QM derivation |
| `equivalence` | 2+ | Mathematically equivalent structures | Quaternions ≅ Pauli ≅ Bloch sphere |
| `theory_axioms` | 3+ | Axioms that define a theory | QBP's three axioms + measurement postulate |
| `research_cluster` | 3+ | Related questions forming a theme | Divergence + octonions + Bell predictions |
| `proof_link` | 2-3 | Claim + formal proof + theorem | Claim linked to Lean 4 theorem |
| `emergence` | 3+ | Concepts that together yield emergent property | Rotation + half-angle → spinor behavior |
| `review_consensus` | 3+ | Multiple reviewers agree | Red Team + Gemini + James approve |
| `investigation` | 3+ | Question + investigation sources | Question + background findings |

---

## Query Patterns for Research

### 1. Find Weakly-Supported Claims
```python
# Claims with fewer than 2 evidence sources
weak_claims = [v for v in hg.all_v
               if hg.v(v).get("type") == "Claim"
               and not any(hg.e(e).get("type") == "evidence_chain"
                          and v in e and len(e) >= 3
                          for e in hg.nbr_e_of_v(v))]
```

### 2. Find Unproven Claims
```python
# Claims without proof_link hyperedge
unproven = [v for v in hg.all_v
            if hg.v(v).get("type") == "Claim"
            and not any(hg.e(e).get("type") == "proof_link"
                       for e in hg.nbr_e_of_v(v))]
```

### 3. Find Bridge Concepts
```python
# Concepts connecting multiple research clusters
bridges = [(v, hg.degree_v(v)) for v in hg.all_v
           if hg.v(v).get("type") == "Concept"
           and hg.degree_v(v) >= 3]
```

### 4. Trace Evidence Provenance
```python
def trace_claim_evidence(hg, claim_id):
    """Find all evidence supporting a claim."""
    evidence = []
    for edge_id in hg.nbr_e_of_v(claim_id):
        edge_data = hg.e(edge_id)
        if edge_data.get("type") == "evidence_chain":
            members = hg.nbr_v_of_e(edge_id) - {claim_id}
            evidence.append({
                "edge": edge_id,
                "sources": list(members),
                "confidence": edge_data.get("confidence_tier")
            })
    return evidence
```

### 5. Find Research Gaps
```python
# Open questions with no investigation hyperedges
gaps = [v for v in hg.all_v
        if hg.v(v).get("type") == "Question"
        and hg.v(v).get("status") == "open"
        and hg.degree_v(v) <= 1]  # Only in tag clusters, no investigation
```

---

## Migration Plan

### Phase 1: Schema & Tooling (Week 1)
1. Install Hypergraph-DB: `pip install hypergraph-db`
2. Create `scripts/qbp_knowledge.py` — main interface
3. Define vertex schemas (Source, Concept, Claim, Question, Proof)
4. Define hyperedge types with validation
5. Build YAML → Hypergraph-DB migration script

### Phase 2: Data Migration (Week 1-2)
1. Migrate existing entries (2 entries currently)
2. Infer hyperedges from existing relationships
3. Add proof links for existing Lean theorems
4. Validate data integrity

### Phase 3: Integration (Week 2)
1. Connect to Lean 4 proofs (auto-extract theorem references)
2. Connect to experiment results (Python simulations)
3. Build visualization dashboard
4. Create CLI for common operations

### Phase 4: Research Sprint Integration (Week 3+)
1. Use during Research Sprint 0R
2. Capture sources, concepts, claims as vertices
3. Build evidence chains as research progresses
4. Refine based on actual usage

---

## Issue Cleanup

### Current Issues (#220-225)

| Issue | Current Focus | New Direction | Action |
|-------|---------------|---------------|--------|
| #220: YAML validation | Validate YAML schema | Validate Hypergraph-DB entries | **Repurpose** → Schema validation for vertices/hyperedges |
| #221: Index auto-gen | Generate index.yaml | Database handles indexing | **Close** → Superseded by Hypergraph-DB |
| #222: Visualization | Foam/custom D3 | Hypergraph-DB built-in viz | **Repurpose** → Customize visualization, add exports |
| #223: JSON-LD export | Semantic web | HIF export (hypergraph standard) | **Repurpose** → HIF + optional JSON-LD |
| #224: SQLite index | Query efficiency | Hypergraph-DB native queries | **Close** → Superseded by Hypergraph-DB |
| #225: Lean 4 integration | Link proofs to claims | proof_link hyperedges | **Keep** → Critical for rigor |

### New Issues to Create

1. **Hypergraph-DB integration** — Core setup and migration
2. **Hyperedge type definitions** — Formalize the type system
3. **Research query library** — Pre-built queries for common patterns
4. **Evidence chain inference** — Auto-detect multi-source evidence
5. **Visualization customization** — QBP-specific styling and exports

---

## Success Metrics

### Research Effectiveness
- [ ] Can answer "What evidence supports claim X?" in one query
- [ ] Can find all unproven claims
- [ ] Can visualize theory structure
- [ ] Can trace from experiment → claim → proof

### Theory Rigor
- [ ] Every established claim has evidence_chain hyperedge
- [ ] Every formally-proven claim has proof_link hyperedge
- [ ] Equivalence classes are explicit (not implied)
- [ ] Research gaps are visible

### Insight Discovery
- [ ] Can identify bridge concepts connecting research themes
- [ ] Can find emergent properties from concept combinations
- [ ] Visualization reveals patterns not obvious in text

---

## Example: Complete Research Flow

```python
from qbp_knowledge import QBPKnowledge

# Initialize
kb = QBPKnowledge("knowledge/qbp.hgdb")

# During Research Sprint 0R: Add source
kb.add_source("furey-2016", {
    "title": "Standard Model Physics from an Algebra?",
    "authors": ["Cohl Furey"],
    "url": "https://arxiv.org/abs/1611.09182",
    "tags": ["division-algebras", "octonions", "standard-model"]
})

# Extract concept
kb.add_concept("octonion-algebra", {
    "term": "Octonion Algebra",
    "definition": "8-dimensional non-associative division algebra",
    "properties": ["non-associative", "alternative", "normed"]
})

# Make claim with evidence chain
kb.add_claim_with_evidence(
    claim_id="claim:octonion-generations",
    statement="Octonion algebra naturally accommodates 3 generations",
    evidence=["furey-2016", "furey-2018", "source:dixon-algebra"],
    confidence_tier=2  # Supported but not proven
)

# Link to research question
kb.link_to_question("claim:octonion-generations", "question:qbp-divergence")

# Visualize the growing knowledge structure
kb.visualize()

# Query: What's our strongest evidence for divergence?
divergence_evidence = kb.query_evidence_for("question:qbp-divergence")
```

---

## Appendix: Hypergraph-DB Quick Reference

```python
from hyperdb import HypergraphDB

hg = HypergraphDB()

# Vertices
hg.add_v(id, attributes)        # Add vertex
hg.v(id)                        # Get vertex attributes
hg.all_v                        # All vertex IDs
hg.num_v                        # Vertex count

# Hyperedges
hg.add_e(tuple_of_ids, attrs)   # Add hyperedge
hg.e(edge_id)                   # Get edge attributes
hg.all_e                        # All edge IDs
hg.num_e                        # Edge count

# Navigation
hg.nbr_v_of_e(edge_id)          # Vertices in edge
hg.nbr_e_of_v(vertex_id)        # Edges containing vertex
hg.nbr_v(vertex_id)             # Neighbor vertices
hg.degree_v(vertex_id)          # Vertex degree
hg.degree_e(edge_id)            # Edge degree (# vertices)

# Persistence
hg.save("file.hgdb")            # Save to file
hg = HypergraphDB(storage_file="file.hgdb")  # Load
hg.save_as_hif("file.json")     # Export HIF format

# Visualization
hg.draw()                       # Open in browser
hg.draw(port=8888)              # Custom port
```

---

## References

- [Hypergraph-DB Documentation](https://imoonlab.github.io/Hypergraph-DB/)
- [EasyHypergraph Paper](https://www.nature.com/articles/s41599-025-05180-5) — Analysis capabilities
- [HIF Format](https://arxiv.org/html/2507.11520) — Interoperability standard
- [HyperNetX](https://github.com/pnnl/HyperNetX) — Analysis library
- [Awesome Hypergraph Network](https://github.com/gzcsudo/Awesome-Hypergraph-Network) — Resource collection
