#!/usr/bin/env python3
"""
QBP Hypergraph Knowledge System

Native hypergraph-based knowledge management for the Quaternion-Based Physics project.
Enables n-ary relationships for evidence chains, equivalence classes, and theory structures.

Usage:
    from qbp_knowledge import QBPKnowledge

    kb = QBPKnowledge("knowledge/qbp.hgdb")
    kb.add_source("furey-2016", {...})
    kb.add_claim_with_evidence("claim-id", "statement", ["source1", "source2"], tier=3)
    kb.visualize()

CLI:
    python scripts/qbp_knowledge.py --help
    python scripts/qbp_knowledge.py query weak-claims
    python scripts/qbp_knowledge.py viz --output graph.html
"""

import argparse
import json
import sys
from dataclasses import dataclass, field
from datetime import date
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union

# Core dependency
from hyperdb import HypergraphDB

# Optional analysis (HyperNetX)
try:
    import hypernetx as hnx
    HNX_AVAILABLE = True
except ImportError:
    HNX_AVAILABLE = False

# Optional visualization
try:
    import matplotlib.pyplot as plt
    MPL_AVAILABLE = True
except ImportError:
    MPL_AVAILABLE = False


# =============================================================================
# Vertex Type Definitions
# =============================================================================

VERTEX_TYPES = {
    "Source": {
        "required": ["type", "title"],
        "optional": ["category", "authors", "date", "url", "doi", "venue", "tags",
                     "abstract", "quotes", "key_insights", "research_sprint", "added_date", "added_by"],
        "categories": ["paper", "book", "website", "internal", "proof", "simulation"]
    },
    "Concept": {
        "required": ["type", "term"],
        "optional": ["definition", "formal_definition", "aliases", "tags",
                     "sources", "related_concepts", "added_date", "added_by"],
    },
    "Claim": {
        "required": ["type", "statement"],
        "optional": ["context", "status", "confidence_tier", "tags", "implications",
                     "added_date", "added_by"],
        "statuses": ["proposed", "supported", "established", "contested", "refuted"]
    },
    "Question": {
        "required": ["type", "question"],
        "optional": ["context", "status", "priority", "tags", "related_issues",
                     "investigation_approaches", "success_criteria", "added_date", "added_by"],
        "statuses": ["open", "partially-answered", "answered", "superseded"],
        "priorities": ["high", "medium", "low"]
    },
    "Proof": {
        "required": ["type", "lean_file"],
        "optional": ["theorems", "verified", "no_sorry", "tags", "added_date", "added_by"],
    }
}


# =============================================================================
# Hyperedge Type Definitions
# =============================================================================

HYPEREDGE_TYPES = {
    "evidence_chain": {
        "description": "Claim + all supporting evidence sources",
        "min_members": 3,  # 1 claim + at least 2 evidence sources
        "required_vertex_types": {"Claim": 1},  # Exactly 1 claim
        "properties": ["confidence_tier", "established_date", "description"]
    },
    "equivalence": {
        "description": "Mathematically equivalent structures",
        "min_members": 2,
        "required_vertex_types": {"Concept": 2},  # At least 2 concepts
        "properties": ["description", "isomorphism_proven", "proof_ref"]
    },
    "theory_axioms": {
        "description": "Axioms that together define a theory",
        "min_members": 3,
        "properties": ["theory", "completeness", "open_questions"]
    },
    "research_cluster": {
        "description": "Related questions forming a research theme",
        "min_members": 2,
        "required_vertex_types": {"Question": 1},  # At least 1 question
        "properties": ["theme", "priority", "target_sprint"]
    },
    "proof_link": {
        "description": "Claim linked to formal Lean 4 proof",
        "min_members": 2,
        "max_members": 3,
        "required_vertex_types": {"Claim": 1, "Proof": 1},
        "properties": ["theorem", "theorem_line", "verification_status"]
    },
    "emergence": {
        "description": "Concepts that together yield emergent property",
        "min_members": 2,
        "required_vertex_types": {"Concept": 2},
        "properties": ["emergent_property", "physical_significance"]
    },
    "review_consensus": {
        "description": "Multiple reviewers agree on assessment",
        "min_members": 2,
        "properties": ["verdict", "review_date", "reviewers"]
    },
    "investigation": {
        "description": "Question + investigation sources",
        "min_members": 2,
        "required_vertex_types": {"Question": 1},
        "properties": ["findings", "status"]
    }
}


# =============================================================================
# QBP Knowledge System
# =============================================================================

class QBPKnowledge:
    """
    Hypergraph-based knowledge management for QBP research.

    Uses Hypergraph-DB as the core data store with optional HyperNetX
    for advanced analysis.
    """

    def __init__(self, storage_path: Optional[str] = None):
        """
        Initialize the knowledge system.

        Args:
            storage_path: Path to .hgdb file. If exists, loads it.
        """
        self.storage_path = Path(storage_path) if storage_path else None

        if self.storage_path and self.storage_path.exists():
            self.hg = HypergraphDB(storage_file=str(self.storage_path))
        else:
            self.hg = HypergraphDB()

        self._hnx_cache = None

    # -------------------------------------------------------------------------
    # Vertex Operations
    # -------------------------------------------------------------------------

    def add_vertex(self, vertex_id: str, vertex_type: str, attributes: Dict[str, Any]) -> str:
        """
        Add a vertex with validation.

        Args:
            vertex_id: Unique identifier (e.g., "source:furey-2016")
            vertex_type: One of Source, Concept, Claim, Question, Proof
            attributes: Vertex properties

        Returns:
            The vertex ID
        """
        if vertex_type not in VERTEX_TYPES:
            raise ValueError(f"Invalid vertex type: {vertex_type}. Must be one of {list(VERTEX_TYPES.keys())}")

        schema = VERTEX_TYPES[vertex_type]
        attrs = {"type": vertex_type, **attributes}

        # Validate required fields
        for req in schema["required"]:
            if req not in attrs:
                raise ValueError(f"Missing required field '{req}' for {vertex_type}")

        # Add metadata
        if "added_date" not in attrs:
            attrs["added_date"] = str(date.today())

        self.hg.add_v(vertex_id, attrs)
        self._hnx_cache = None
        return vertex_id

    def add_source(self, source_id: str, title: str, **kwargs) -> str:
        """Add a Source vertex."""
        if not source_id.startswith("source:"):
            source_id = f"source:{source_id}"
        return self.add_vertex(source_id, "Source", {"title": title, **kwargs})

    def add_concept(self, concept_id: str, term: str, **kwargs) -> str:
        """Add a Concept vertex."""
        if not concept_id.startswith("concept:"):
            concept_id = f"concept:{concept_id}"
        return self.add_vertex(concept_id, "Concept", {"term": term, **kwargs})

    def add_claim(self, claim_id: str, statement: str, **kwargs) -> str:
        """Add a Claim vertex."""
        if not claim_id.startswith("claim:"):
            claim_id = f"claim:{claim_id}"
        return self.add_vertex(claim_id, "Claim", {"statement": statement, **kwargs})

    def add_question(self, question_id: str, question: str, **kwargs) -> str:
        """Add a Question vertex."""
        if not question_id.startswith("question:"):
            question_id = f"question:{question_id}"
        return self.add_vertex(question_id, "Question", {"question": question, **kwargs})

    def add_proof(self, proof_id: str, lean_file: str, **kwargs) -> str:
        """Add a Proof vertex."""
        if not proof_id.startswith("proof:"):
            proof_id = f"proof:{proof_id}"
        return self.add_vertex(proof_id, "Proof", {"lean_file": lean_file, **kwargs})

    def get_vertex(self, vertex_id: str) -> Optional[Dict[str, Any]]:
        """Get vertex attributes."""
        try:
            return self.hg.v(vertex_id)
        except:
            return None

    def get_vertices_by_type(self, vertex_type: str) -> List[str]:
        """Get all vertex IDs of a given type."""
        return [v for v in self.hg.all_v if self.hg.v(v).get("type") == vertex_type]

    # -------------------------------------------------------------------------
    # Hyperedge Operations
    # -------------------------------------------------------------------------

    def add_hyperedge(self, members: Tuple[str, ...], edge_type: str,
                      properties: Optional[Dict[str, Any]] = None) -> Tuple[str, ...]:
        """
        Add a hyperedge with validation.

        Args:
            members: Tuple of vertex IDs in this hyperedge
            edge_type: One of the defined hyperedge types
            properties: Edge properties

        Returns:
            The hyperedge (tuple of members)
        """
        if edge_type not in HYPEREDGE_TYPES:
            raise ValueError(f"Invalid hyperedge type: {edge_type}. Must be one of {list(HYPEREDGE_TYPES.keys())}")

        schema = HYPEREDGE_TYPES[edge_type]
        props = {"type": edge_type, **(properties or {})}

        # Validate member count
        if len(members) < schema.get("min_members", 2):
            raise ValueError(f"{edge_type} requires at least {schema['min_members']} members")
        if "max_members" in schema and len(members) > schema["max_members"]:
            raise ValueError(f"{edge_type} allows at most {schema['max_members']} members")

        # Validate required vertex types
        if "required_vertex_types" in schema:
            type_counts = {}
            for member in members:
                v_data = self.get_vertex(member)
                if v_data:
                    v_type = v_data.get("type")
                    type_counts[v_type] = type_counts.get(v_type, 0) + 1

            for req_type, min_count in schema["required_vertex_types"].items():
                if type_counts.get(req_type, 0) < min_count:
                    raise ValueError(f"{edge_type} requires at least {min_count} {req_type} vertex(es)")

        # Add metadata
        if "created_date" not in props:
            props["created_date"] = str(date.today())

        self.hg.add_e(members, props)
        self._hnx_cache = None
        return members

    def add_evidence_chain(self, claim_id: str, evidence_ids: List[str],
                           confidence_tier: int = 2, **kwargs) -> Tuple[str, ...]:
        """
        Add an evidence chain hyperedge.

        Args:
            claim_id: The claim being supported
            evidence_ids: List of source/proof IDs providing evidence
            confidence_tier: 1=weak, 2=moderate, 3=strong
        """
        members = tuple([claim_id] + evidence_ids)
        return self.add_hyperedge(members, "evidence_chain", {
            "confidence_tier": confidence_tier,
            **kwargs
        })

    def add_equivalence(self, concept_ids: List[str], description: str = "",
                        **kwargs) -> Tuple[str, ...]:
        """Add an equivalence class hyperedge."""
        return self.add_hyperedge(tuple(concept_ids), "equivalence", {
            "description": description,
            **kwargs
        })

    def add_proof_link(self, claim_id: str, proof_id: str, theorem: str,
                       **kwargs) -> Tuple[str, ...]:
        """Add a proof link hyperedge."""
        return self.add_hyperedge((claim_id, proof_id), "proof_link", {
            "theorem": theorem,
            **kwargs
        })

    def add_research_cluster(self, member_ids: List[str], theme: str,
                             **kwargs) -> Tuple[str, ...]:
        """Add a research cluster hyperedge."""
        return self.add_hyperedge(tuple(member_ids), "research_cluster", {
            "theme": theme,
            **kwargs
        })

    def add_theory_axioms(self, axiom_ids: List[str], theory: str,
                          **kwargs) -> Tuple[str, ...]:
        """Add a theory axioms hyperedge."""
        return self.add_hyperedge(tuple(axiom_ids), "theory_axioms", {
            "theory": theory,
            **kwargs
        })

    def get_hyperedge(self, members: Tuple[str, ...]) -> Optional[Dict[str, Any]]:
        """Get hyperedge properties."""
        try:
            return self.hg.e(members)
        except:
            return None

    def get_hyperedges_by_type(self, edge_type: str) -> List[Tuple[str, ...]]:
        """Get all hyperedges of a given type."""
        result = []
        for e in self.hg.all_e:
            try:
                props = self.hg.e(e)
                if props and props.get("type") == edge_type:
                    result.append(e)
            except:
                pass
        return result

    def get_hyperedges_containing(self, vertex_id: str) -> List[Tuple[str, ...]]:
        """Get all hyperedges containing a vertex."""
        try:
            return list(self.hg.nbr_e_of_v(vertex_id))
        except:
            return []

    # -------------------------------------------------------------------------
    # Research Queries
    # -------------------------------------------------------------------------

    def find_weak_claims(self) -> List[Dict[str, Any]]:
        """Find claims with fewer than 2 evidence sources."""
        weak = []
        for claim_id in self.get_vertices_by_type("Claim"):
            evidence_chains = [e for e in self.get_hyperedges_containing(claim_id)
                              if self.get_hyperedge(e).get("type") == "evidence_chain"]

            if not evidence_chains:
                weak.append({
                    "claim_id": claim_id,
                    "claim": self.get_vertex(claim_id),
                    "evidence_count": 0,
                    "reason": "no evidence chain"
                })
            else:
                for chain in evidence_chains:
                    if len(chain) < 3:  # claim + at least 2 sources
                        weak.append({
                            "claim_id": claim_id,
                            "claim": self.get_vertex(claim_id),
                            "evidence_count": len(chain) - 1,
                            "reason": "insufficient evidence"
                        })
        return weak

    def find_unproven_claims(self) -> List[Dict[str, Any]]:
        """Find claims without proof_link hyperedges."""
        unproven = []
        for claim_id in self.get_vertices_by_type("Claim"):
            proof_links = [e for e in self.get_hyperedges_containing(claim_id)
                          if self.get_hyperedge(e).get("type") == "proof_link"]
            if not proof_links:
                unproven.append({
                    "claim_id": claim_id,
                    "claim": self.get_vertex(claim_id)
                })
        return unproven

    def find_research_gaps(self) -> List[Dict[str, Any]]:
        """Find open questions with no investigation hyperedges."""
        gaps = []
        for q_id in self.get_vertices_by_type("Question"):
            q_data = self.get_vertex(q_id)
            if q_data.get("status") != "open":
                continue

            investigations = [e for e in self.get_hyperedges_containing(q_id)
                             if self.get_hyperedge(e).get("type") == "investigation"]
            if not investigations:
                gaps.append({
                    "question_id": q_id,
                    "question": q_data,
                    "reason": "no investigation hyperedge"
                })
        return gaps

    def find_bridge_concepts(self, min_degree: int = 3) -> List[Dict[str, Any]]:
        """Find concepts that appear in multiple hyperedges."""
        bridges = []
        for c_id in self.get_vertices_by_type("Concept"):
            edges = self.get_hyperedges_containing(c_id)
            if len(edges) >= min_degree:
                bridges.append({
                    "concept_id": c_id,
                    "concept": self.get_vertex(c_id),
                    "degree": len(edges),
                    "edge_types": [self.get_hyperedge(e).get("type") for e in edges]
                })
        return sorted(bridges, key=lambda x: x["degree"], reverse=True)

    def trace_evidence(self, claim_id: str) -> Dict[str, Any]:
        """Trace all evidence supporting a claim."""
        claim_data = self.get_vertex(claim_id)
        evidence_chains = [e for e in self.get_hyperedges_containing(claim_id)
                          if self.get_hyperedge(e).get("type") == "evidence_chain"]
        proof_links = [e for e in self.get_hyperedges_containing(claim_id)
                      if self.get_hyperedge(e).get("type") == "proof_link"]

        return {
            "claim_id": claim_id,
            "statement": claim_data.get("statement") if claim_data else None,
            "evidence_chains": [
                {
                    "members": list(e),
                    "properties": self.get_hyperedge(e),
                    "sources": [m for m in e if m != claim_id]
                }
                for e in evidence_chains
            ],
            "proof_links": [
                {
                    "members": list(e),
                    "properties": self.get_hyperedge(e)
                }
                for e in proof_links
            ],
            "has_formal_proof": len(proof_links) > 0,
            "evidence_count": sum(len(e) - 1 for e in evidence_chains)
        }

    def coverage_report(self) -> Dict[str, Any]:
        """Generate a coverage report."""
        claims = self.get_vertices_by_type("Claim")
        questions = self.get_vertices_by_type("Question")

        claims_with_evidence = sum(1 for c in claims
                                   if any(self.get_hyperedge(e).get("type") == "evidence_chain"
                                         for e in self.get_hyperedges_containing(c)))
        claims_with_proof = sum(1 for c in claims
                               if any(self.get_hyperedge(e).get("type") == "proof_link"
                                     for e in self.get_hyperedges_containing(c)))
        open_questions = sum(1 for q in questions
                            if self.get_vertex(q).get("status") == "open")

        return {
            "vertices": {
                "total": self.hg.num_v,
                "sources": len(self.get_vertices_by_type("Source")),
                "concepts": len(self.get_vertices_by_type("Concept")),
                "claims": len(claims),
                "questions": len(questions),
                "proofs": len(self.get_vertices_by_type("Proof"))
            },
            "hyperedges": {
                "total": self.hg.num_e,
                "by_type": {
                    etype: len(self.get_hyperedges_by_type(etype))
                    for etype in HYPEREDGE_TYPES.keys()
                }
            },
            "coverage": {
                "claims_with_evidence": claims_with_evidence,
                "claims_with_evidence_pct": (claims_with_evidence / len(claims) * 100) if claims else 0,
                "claims_with_proof": claims_with_proof,
                "claims_with_proof_pct": (claims_with_proof / len(claims) * 100) if claims else 0,
                "open_questions": open_questions
            }
        }

    # -------------------------------------------------------------------------
    # Persistence
    # -------------------------------------------------------------------------

    def save(self, path: Optional[str] = None):
        """Save the hypergraph to disk."""
        save_path = path or self.storage_path
        if save_path:
            self.hg.save(str(save_path))
            print(f"Saved to {save_path}")
        else:
            raise ValueError("No storage path specified")

    def export_hif(self, path: str):
        """Export to Hypergraph Interchange Format."""
        self.hg.save_as_hif(path)
        print(f"Exported HIF to {path}")

    # -------------------------------------------------------------------------
    # Visualization
    # -------------------------------------------------------------------------

    def visualize_web(self, port: int = 8088):
        """Open interactive visualization in browser (default port 8088)."""
        self.hg.draw(port=port)

    def visualize_matplotlib(self, output_path: Optional[str] = None,
                             title: str = "QBP Knowledge Hypergraph"):
        """Generate static visualization using HyperNetX."""
        if not HNX_AVAILABLE or not MPL_AVAILABLE:
            print("Requires: pip install hypernetx matplotlib")
            return

        # Convert to HyperNetX format
        edges = {}
        for e in self.hg.all_e:
            props = self.hg.e(e)
            edge_label = f"{props.get('type', 'unknown')}:{len(e)}"
            edges[edge_label] = set(e)

        if not edges:
            print("No hyperedges to visualize")
            return

        H = hnx.Hypergraph(edges)

        fig, ax = plt.subplots(figsize=(14, 10))
        hnx.draw(H, ax=ax, with_edge_labels=True, with_node_labels=True)
        ax.set_title(title)

        if output_path:
            plt.savefig(output_path, dpi=150, bbox_inches='tight')
            print(f"Saved to {output_path}")
        else:
            plt.show()

    def to_hypernetx(self) -> 'hnx.Hypergraph':
        """Convert to HyperNetX Hypergraph for analysis."""
        if not HNX_AVAILABLE:
            raise ImportError("Requires: pip install hypernetx")

        edges = {}
        for e in self.hg.all_e:
            edges[e] = set(e)
        return hnx.Hypergraph(edges)

    # -------------------------------------------------------------------------
    # Summary
    # -------------------------------------------------------------------------

    def summary(self) -> str:
        """Generate text summary."""
        report = self.coverage_report()
        lines = [
            "# QBP Knowledge Hypergraph Summary",
            "",
            "## Vertices",
            f"- Total: {report['vertices']['total']}",
            f"- Sources: {report['vertices']['sources']}",
            f"- Concepts: {report['vertices']['concepts']}",
            f"- Claims: {report['vertices']['claims']}",
            f"- Questions: {report['vertices']['questions']}",
            f"- Proofs: {report['vertices']['proofs']}",
            "",
            "## Hyperedges",
            f"- Total: {report['hyperedges']['total']}",
        ]
        for etype, count in report['hyperedges']['by_type'].items():
            if count > 0:
                lines.append(f"- {etype}: {count}")

        lines.extend([
            "",
            "## Coverage",
            f"- Claims with evidence: {report['coverage']['claims_with_evidence']} ({report['coverage']['claims_with_evidence_pct']:.1f}%)",
            f"- Claims with formal proof: {report['coverage']['claims_with_proof']} ({report['coverage']['claims_with_proof_pct']:.1f}%)",
            f"- Open questions: {report['coverage']['open_questions']}",
        ])

        return "\n".join(lines)


# =============================================================================
# CLI
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="QBP Hypergraph Knowledge System",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python qbp_knowledge.py summary
  python qbp_knowledge.py query weak-claims
  python qbp_knowledge.py query unproven
  python qbp_knowledge.py query gaps
  python qbp_knowledge.py viz --web
  python qbp_knowledge.py viz --output graph.png
  python qbp_knowledge.py report
        """
    )

    parser.add_argument('--db', type=str, default='knowledge/qbp.hgdb',
                        help='Path to hypergraph database')

    subparsers = parser.add_subparsers(dest='command', help='Commands')

    # Summary
    subparsers.add_parser('summary', help='Show summary of knowledge graph')

    # Query
    query_parser = subparsers.add_parser('query', help='Run research queries')
    query_parser.add_argument('query_type',
                              choices=['weak-claims', 'unproven', 'gaps', 'bridges'],
                              help='Type of query')

    # Visualization
    viz_parser = subparsers.add_parser('viz', help='Visualize the hypergraph')
    viz_parser.add_argument('--web', action='store_true', help='Open web visualization')
    viz_parser.add_argument('--output', type=str, help='Save to file')
    viz_parser.add_argument('--port', type=int, default=8088, help='Port for web viz (default 8088 to avoid conflict with proof viz on 8080)')

    # Report
    subparsers.add_parser('report', help='Generate coverage report')

    # Info
    info_parser = subparsers.add_parser('info', help='Get info about a vertex')
    info_parser.add_argument('vertex_id', help='Vertex ID')

    # Evidence
    evidence_parser = subparsers.add_parser('evidence', help='Trace evidence for a claim')
    evidence_parser.add_argument('claim_id', help='Claim ID')

    args = parser.parse_args()

    # Load knowledge base
    db_path = Path(args.db)
    if db_path.exists():
        kb = QBPKnowledge(str(db_path))
    else:
        kb = QBPKnowledge()
        print(f"Note: Database {db_path} not found. Using empty graph.")

    # Execute command
    if args.command == 'summary':
        print(kb.summary())

    elif args.command == 'query':
        if args.query_type == 'weak-claims':
            results = kb.find_weak_claims()
            if results:
                print(f"Found {len(results)} weak claims:")
                for r in results:
                    print(f"  - {r['claim_id']}: {r['reason']}")
            else:
                print("No weak claims found.")

        elif args.query_type == 'unproven':
            results = kb.find_unproven_claims()
            if results:
                print(f"Found {len(results)} unproven claims:")
                for r in results:
                    print(f"  - {r['claim_id']}")
            else:
                print("All claims have formal proofs.")

        elif args.query_type == 'gaps':
            results = kb.find_research_gaps()
            if results:
                print(f"Found {len(results)} research gaps:")
                for r in results:
                    q = r['question'].get('question', '')[:60]
                    print(f"  - {r['question_id']}: {q}...")
            else:
                print("No research gaps found.")

        elif args.query_type == 'bridges':
            results = kb.find_bridge_concepts()
            if results:
                print(f"Found {len(results)} bridge concepts:")
                for r in results:
                    print(f"  - {r['concept_id']}: degree {r['degree']}")
            else:
                print("No bridge concepts found.")

    elif args.command == 'viz':
        if args.web:
            kb.visualize_web(port=args.port)
        else:
            kb.visualize_matplotlib(output_path=args.output)

    elif args.command == 'report':
        report = kb.coverage_report()
        print(json.dumps(report, indent=2))

    elif args.command == 'info':
        data = kb.get_vertex(args.vertex_id)
        if data:
            print(json.dumps(data, indent=2))
        else:
            print(f"Vertex not found: {args.vertex_id}")

    elif args.command == 'evidence':
        result = kb.trace_evidence(args.claim_id)
        print(json.dumps(result, indent=2, default=str))

    else:
        parser.print_help()


if __name__ == '__main__':
    main()
