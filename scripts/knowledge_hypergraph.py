#!/usr/bin/env python3
"""
QBP Knowledge Hypergraph

Extends the YAML-based knowledge graph with hypergraph capabilities using HyperNetX.
Enables n-ary relationship modeling for deeper theoretical understanding.

Usage:
    python scripts/knowledge_hypergraph.py              # Load and visualize
    python scripts/knowledge_hypergraph.py --demo       # Run with demo data
    python scripts/knowledge_hypergraph.py --analyze    # Show analysis
"""

import argparse
import sys
from pathlib import Path
from typing import Dict, List, Set, Any, Optional
from dataclasses import dataclass, field
import yaml

# Check for HyperNetX
try:
    import hypernetx as hnx
    HNX_AVAILABLE = True
except ImportError:
    HNX_AVAILABLE = False
    print("Warning: hypernetx not installed. Run: pip install hypernetx")

try:
    import matplotlib.pyplot as plt
    MPL_AVAILABLE = True
except ImportError:
    MPL_AVAILABLE = False


@dataclass
class KnowledgeEntry:
    """Represents a single knowledge graph entry."""
    id: str
    type: str  # Source, Concept, Claim, Question
    data: Dict[str, Any]
    file_path: Optional[Path] = None

    @property
    def tags(self) -> List[str]:
        return self.data.get('tags', [])

    @property
    def relationships(self) -> List[Dict]:
        return self.data.get('relationships', [])

    @property
    def title(self) -> str:
        """Get display title for this entry."""
        if self.type == 'Source':
            return self.data.get('metadata', {}).get('title', self.id)
        elif self.type == 'Question':
            return self.data.get('question', self.id)[:50]
        elif self.type == 'Claim':
            return self.data.get('statement', self.id)[:50]
        elif self.type == 'Concept':
            return self.data.get('term', self.id)
        return self.id


@dataclass
class Hyperedge:
    """Represents an n-ary relationship."""
    id: str
    type: str  # evidence, equivalence, emergence, tag_cluster, etc.
    members: Set[str]
    properties: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self):
        if isinstance(self.members, list):
            self.members = set(self.members)


class KnowledgeHypergraph:
    """
    Hypergraph adapter for QBP knowledge graph.

    Loads YAML entries and constructs a hypergraph with:
    - Binary relationships as 2-edges
    - Inferred n-ary relationships (evidence chains, tag clusters, etc.)
    - Explicit hyperedges from 'hyperedges' field in YAML
    """

    def __init__(self, knowledge_dir: Path):
        self.knowledge_dir = Path(knowledge_dir)
        self.entries: Dict[str, KnowledgeEntry] = {}
        self.hyperedges: Dict[str, Hyperedge] = {}
        self._hnx_graph: Optional['hnx.Hypergraph'] = None

    def load(self) -> 'KnowledgeHypergraph':
        """Load all YAML entries from knowledge directory."""
        for subdir in ['sources', 'concepts', 'claims', 'questions']:
            dir_path = self.knowledge_dir / subdir
            if not dir_path.exists():
                continue
            for yaml_file in dir_path.glob('*.yaml'):
                self._load_entry(yaml_file)

        # Build hyperedges after loading all entries
        self._build_hyperedges()
        return self

    def _load_entry(self, file_path: Path):
        """Load a single YAML entry."""
        try:
            with open(file_path, 'r') as f:
                data = yaml.safe_load(f)

            if data and 'id' in data:
                entry = KnowledgeEntry(
                    id=data['id'],
                    type=data.get('type', 'Unknown'),
                    data=data,
                    file_path=file_path
                )
                self.entries[entry.id] = entry
        except Exception as e:
            print(f"Warning: Failed to load {file_path}: {e}")

    def _build_hyperedges(self):
        """Build hyperedges from loaded entries."""
        # 1. Binary relationships as 2-edges
        for entry_id, entry in self.entries.items():
            for rel in entry.relationships:
                target = rel.get('target')
                rel_type = rel.get('type', 'related')
                if target:
                    edge_id = f"rel:{entry_id}->{target}"
                    self.hyperedges[edge_id] = Hyperedge(
                        id=edge_id,
                        type=f"binary:{rel_type}",
                        members={entry_id, target},
                        properties={'relationship_type': rel_type}
                    )

        # 2. Tag clusters (entries sharing same tag form a hyperedge)
        tag_members: Dict[str, Set[str]] = {}
        for entry_id, entry in self.entries.items():
            for tag in entry.tags:
                if tag not in tag_members:
                    tag_members[tag] = set()
                tag_members[tag].add(entry_id)

        for tag, members in tag_members.items():
            if len(members) >= 2:  # Only create hyperedge if 2+ members
                edge_id = f"tag:{tag}"
                self.hyperedges[edge_id] = Hyperedge(
                    id=edge_id,
                    type="tag_cluster",
                    members=members,
                    properties={'tag': tag}
                )

        # 3. Evidence chains (for Claims with multiple evidence sources)
        for entry_id, entry in self.entries.items():
            if entry.type == 'Claim':
                evidence = entry.data.get('evidence', [])
                if len(evidence) >= 2:
                    members = {entry_id}
                    for ev in evidence:
                        if 'source' in ev:
                            members.add(ev['source'])
                    edge_id = f"evidence:{entry_id}"
                    self.hyperedges[edge_id] = Hyperedge(
                        id=edge_id,
                        type="multi_source_evidence",
                        members=members,
                        properties={'claim': entry_id, 'evidence_count': len(evidence)}
                    )

        # 4. Question investigation groups
        for entry_id, entry in self.entries.items():
            if entry.type == 'Question':
                # Background sources
                background = entry.data.get('background', [])
                if len(background) >= 2:
                    members = {entry_id}
                    for bg in background:
                        if 'source' in bg:
                            members.add(bg['source'])
                    edge_id = f"investigation:{entry_id}"
                    self.hyperedges[edge_id] = Hyperedge(
                        id=edge_id,
                        type="investigation_context",
                        members=members,
                        properties={'question': entry_id}
                    )

        # 5. Explicit hyperedges from YAML (if present)
        for entry_id, entry in self.entries.items():
            explicit_edges = entry.data.get('hyperedges', [])
            for he in explicit_edges:
                edge_id = he.get('id', f"explicit:{entry_id}:{len(self.hyperedges)}")
                members = set(he.get('members', []))
                members.add(entry_id)  # Include the entry itself
                self.hyperedges[edge_id] = Hyperedge(
                    id=edge_id,
                    type=he.get('type', 'explicit'),
                    members=members,
                    properties=he.get('properties', {})
                )

    def add_hyperedge(self, edge_id: str, edge_type: str, members: Set[str],
                      properties: Optional[Dict] = None):
        """Manually add a hyperedge."""
        self.hyperedges[edge_id] = Hyperedge(
            id=edge_id,
            type=edge_type,
            members=members,
            properties=properties or {}
        )
        self._hnx_graph = None  # Invalidate cache

    def to_hypernetx(self) -> 'hnx.Hypergraph':
        """Convert to HyperNetX Hypergraph for analysis."""
        if not HNX_AVAILABLE:
            raise ImportError("hypernetx is required. Install with: pip install hypernetx")

        if self._hnx_graph is not None:
            return self._hnx_graph

        # Build edge dictionary for HyperNetX
        edges = {}
        for edge_id, hyperedge in self.hyperedges.items():
            edges[edge_id] = hyperedge.members

        self._hnx_graph = hnx.Hypergraph(edges)
        return self._hnx_graph

    def visualize(self, output_path: Optional[Path] = None,
                  title: str = "QBP Knowledge Hypergraph",
                  figsize: tuple = (14, 10)):
        """Visualize the hypergraph."""
        if not HNX_AVAILABLE or not MPL_AVAILABLE:
            print("Visualization requires: pip install hypernetx matplotlib")
            return

        H = self.to_hypernetx()

        if len(H.edges) == 0:
            print("No hyperedges to visualize.")
            return

        fig, ax = plt.subplots(figsize=figsize)

        # Color edges by type
        edge_colors = {}
        type_colors = {
            'tag_cluster': '#3498db',
            'multi_source_evidence': '#2ecc71',
            'investigation_context': '#9b59b6',
            'binary:cites': '#e74c3c',
            'binary:supports': '#f39c12',
            'binary:defines': '#1abc9c',
            'explicit': '#34495e',
        }

        for edge_id, hyperedge in self.hyperedges.items():
            edge_colors[edge_id] = type_colors.get(hyperedge.type, '#95a5a6')

        hnx.draw(H, ax=ax,
                 edges_kwargs={'facecolors': [edge_colors.get(e, '#95a5a6') for e in H.edges]},
                 with_edge_labels=True,
                 with_node_labels=True)

        ax.set_title(title, fontsize=14, fontweight='bold')

        # Add legend
        from matplotlib.patches import Patch
        legend_elements = [Patch(facecolor=color, label=etype.replace('binary:', ''))
                          for etype, color in type_colors.items()
                          if any(he.type == etype for he in self.hyperedges.values())]
        if legend_elements:
            ax.legend(handles=legend_elements, loc='upper left', fontsize=8)

        plt.tight_layout()

        if output_path:
            plt.savefig(output_path, dpi=150, bbox_inches='tight')
            print(f"Saved visualization to {output_path}")
        else:
            plt.show()

    def analyze(self) -> Dict[str, Any]:
        """Analyze the hypergraph structure."""
        H = self.to_hypernetx()

        analysis = {
            'node_count': len(H.nodes),
            'edge_count': len(H.edges),
            'edge_types': {},
            'node_degrees': {},
            'largest_edges': [],
            'most_connected_nodes': [],
        }

        # Count edge types
        for he in self.hyperedges.values():
            etype = he.type
            analysis['edge_types'][etype] = analysis['edge_types'].get(etype, 0) + 1

        # Node degrees
        for node in H.nodes:
            analysis['node_degrees'][node] = H.degree(node)

        # Top 5 largest edges
        sorted_edges = sorted(self.hyperedges.items(),
                             key=lambda x: len(x[1].members), reverse=True)
        analysis['largest_edges'] = [
            {'id': e[0], 'type': e[1].type, 'size': len(e[1].members)}
            for e in sorted_edges[:5]
        ]

        # Top 5 most connected nodes
        sorted_nodes = sorted(analysis['node_degrees'].items(),
                             key=lambda x: x[1], reverse=True)
        analysis['most_connected_nodes'] = [
            {'id': n[0], 'degree': n[1]} for n in sorted_nodes[:5]
        ]

        return analysis

    def query_by_node(self, node_id: str) -> Dict[str, Any]:
        """Find all hyperedges containing a node."""
        result = {
            'node': node_id,
            'entry': self.entries.get(node_id),
            'hyperedges': []
        }

        for edge_id, hyperedge in self.hyperedges.items():
            if node_id in hyperedge.members:
                result['hyperedges'].append({
                    'id': edge_id,
                    'type': hyperedge.type,
                    'members': list(hyperedge.members),
                    'properties': hyperedge.properties
                })

        return result

    def query_by_type(self, edge_type: str) -> List[Hyperedge]:
        """Find all hyperedges of a given type."""
        return [he for he in self.hyperedges.values() if he.type == edge_type]

    def find_bridges(self) -> List[str]:
        """Find nodes that connect otherwise disconnected hyperedges."""
        bridges = []
        for node in self.entries.keys():
            edges_containing = [eid for eid, he in self.hyperedges.items()
                               if node in he.members]
            if len(edges_containing) >= 2:
                bridges.append(node)
        return bridges

    def export_summary(self) -> str:
        """Export a text summary of the hypergraph."""
        lines = ["# QBP Knowledge Hypergraph Summary\n"]

        lines.append(f"## Statistics\n")
        lines.append(f"- Entries: {len(self.entries)}")
        lines.append(f"- Hyperedges: {len(self.hyperedges)}\n")

        lines.append("## Entries by Type\n")
        type_counts = {}
        for entry in self.entries.values():
            type_counts[entry.type] = type_counts.get(entry.type, 0) + 1
        for etype, count in sorted(type_counts.items()):
            lines.append(f"- {etype}: {count}")

        lines.append("\n## Hyperedges by Type\n")
        edge_type_counts = {}
        for he in self.hyperedges.values():
            edge_type_counts[he.type] = edge_type_counts.get(he.type, 0) + 1
        for etype, count in sorted(edge_type_counts.items()):
            lines.append(f"- {etype}: {count}")

        lines.append("\n## Hyperedge Details\n")
        for edge_id, he in self.hyperedges.items():
            lines.append(f"### {edge_id}")
            lines.append(f"- Type: {he.type}")
            lines.append(f"- Members ({len(he.members)}): {', '.join(sorted(he.members))}")
            if he.properties:
                lines.append(f"- Properties: {he.properties}")
            lines.append("")

        return "\n".join(lines)


def create_demo_hypergraph() -> KnowledgeHypergraph:
    """Create a demo hypergraph with sample QBP data."""
    # Create a mock knowledge directory structure
    kg = KnowledgeHypergraph(Path("/tmp/qbp-demo"))

    # Add sample entries directly (simulating loaded YAML)
    entries = [
        KnowledgeEntry("claim-cosine-squared", "Claim", {
            'statement': "P(+) = cos²(θ/2) for spin measurement at angle θ",
            'tags': ['quantum-mechanics', 'spin', 'measurement', 'validated'],
            'evidence': [
                {'source': 'proof-lean-angle', 'strength': 'strong'},
                {'source': 'sim-monte-carlo-01b', 'strength': 'supporting'},
                {'source': 'derivation-standard-qm', 'strength': 'supporting'}
            ]
        }),
        KnowledgeEntry("claim-qbp-matches-qm", "Claim", {
            'statement': "QBP matches standard QM for single-particle systems",
            'tags': ['quantum-mechanics', 'validation', 'single-particle'],
        }),
        KnowledgeEntry("concept-quaternion-state", "Concept", {
            'term': "Quaternion State Representation",
            'tags': ['quaternions', 'quantum-mechanics', 'foundations'],
            'relationships': [
                {'type': 'equivalent_to', 'target': 'concept-pauli-algebra'},
                {'type': 'equivalent_to', 'target': 'concept-bloch-sphere'}
            ]
        }),
        KnowledgeEntry("concept-pauli-algebra", "Concept", {
            'term': "Pauli Algebra",
            'tags': ['quantum-mechanics', 'algebra', 'foundations'],
        }),
        KnowledgeEntry("concept-bloch-sphere", "Concept", {
            'term': "Bloch Sphere",
            'tags': ['quantum-mechanics', 'geometry', 'visualization'],
        }),
        KnowledgeEntry("concept-half-angle", "Concept", {
            'term': "Half-Angle Formula",
            'tags': ['quaternions', 'rotation', 'spin'],
        }),
        KnowledgeEntry("question-divergence", "Question", {
            'question': "Where do QBP predictions diverge from standard QM?",
            'tags': ['foundations', 'novel-predictions', 'high-priority'],
            'background': [
                {'source': 'proof-lean-angle', 'finding': 'Single-particle match proven'},
                {'source': 'review-theory-sprint1', 'finding': 'Entanglement may differ'},
            ]
        }),
        KnowledgeEntry("question-octonion", "Question", {
            'question': "Can octonion extensions yield novel predictions?",
            'tags': ['foundations', 'novel-predictions', 'octonions'],
        }),
        KnowledgeEntry("proof-lean-angle", "Source", {
            'metadata': {'title': "Lean 4 Proof: Angle-Dependent Measurement"},
            'tags': ['proof', 'lean4', 'formal-verification', 'validated'],
        }),
        KnowledgeEntry("sim-monte-carlo-01b", "Source", {
            'metadata': {'title': "Monte Carlo Simulation: Experiment 01b"},
            'tags': ['simulation', 'validation', 'experiment-01b'],
        }),
        KnowledgeEntry("derivation-standard-qm", "Source", {
            'metadata': {'title': "Standard QM Derivation of cos²(θ/2)"},
            'tags': ['quantum-mechanics', 'derivation', 'textbook'],
        }),
        KnowledgeEntry("review-theory-sprint1", "Source", {
            'metadata': {'title': "Theory Refinement: Sprint 1 Review"},
            'tags': ['review', 'sprint-1', 'foundations'],
        }),
        KnowledgeEntry("axiom-states", "Concept", {
            'term': "Axiom 1: Quaternionic States",
            'tags': ['axiom', 'qbp', 'foundations'],
        }),
        KnowledgeEntry("axiom-observables", "Concept", {
            'term': "Axiom 2: Quaternionic Observables",
            'tags': ['axiom', 'qbp', 'foundations'],
        }),
        KnowledgeEntry("axiom-evolution", "Concept", {
            'term': "Axiom 3: Quaternionic Evolution",
            'tags': ['axiom', 'qbp', 'foundations'],
        }),
    ]

    for entry in entries:
        kg.entries[entry.id] = entry

    # Build hyperedges from the entries
    kg._build_hyperedges()

    # Add explicit n-ary hyperedges for demo
    kg.add_hyperedge(
        "equiv:spin-representations",
        "equivalence_class",
        {"concept-quaternion-state", "concept-pauli-algebra", "concept-bloch-sphere"},
        {"description": "Equivalent mathematical representations of spin-1/2"}
    )

    kg.add_hyperedge(
        "axioms:qbp-foundation",
        "theory_axioms",
        {"axiom-states", "axiom-observables", "axiom-evolution"},
        {"description": "The three axioms that define QBP"}
    )

    kg.add_hyperedge(
        "research:divergence-investigation",
        "research_cluster",
        {"question-divergence", "question-octonion", "concept-quaternion-state",
         "claim-qbp-matches-qm"},
        {"description": "Core research questions about QBP uniqueness"}
    )

    return kg


def main():
    parser = argparse.ArgumentParser(description="QBP Knowledge Hypergraph")
    parser.add_argument('--demo', action='store_true', help='Run with demo data')
    parser.add_argument('--analyze', action='store_true', help='Show analysis')
    parser.add_argument('--output', type=str, help='Save visualization to file')
    parser.add_argument('--summary', action='store_true', help='Print text summary')
    parser.add_argument('--query', type=str, help='Query node by ID')
    parser.add_argument('--knowledge-dir', type=str,
                        default='knowledge',
                        help='Path to knowledge directory')

    args = parser.parse_args()

    # Load or create hypergraph
    if args.demo:
        print("Loading demo hypergraph...")
        kg = create_demo_hypergraph()
    else:
        knowledge_dir = Path(args.knowledge_dir)
        if not knowledge_dir.exists():
            # Try relative to script location
            script_dir = Path(__file__).parent.parent
            knowledge_dir = script_dir / 'knowledge'

        print(f"Loading knowledge graph from {knowledge_dir}...")
        kg = KnowledgeHypergraph(knowledge_dir).load()

    print(f"Loaded {len(kg.entries)} entries, {len(kg.hyperedges)} hyperedges")

    # Handle commands
    if args.query:
        result = kg.query_by_node(args.query)
        print(f"\nNode: {args.query}")
        if result['entry']:
            print(f"Type: {result['entry'].type}")
            print(f"Title: {result['entry'].title}")
        print(f"\nHyperedges containing this node:")
        for he in result['hyperedges']:
            print(f"  - {he['id']} ({he['type']})")
            print(f"    Members: {', '.join(he['members'])}")

    if args.analyze:
        analysis = kg.analyze()
        print("\n=== Hypergraph Analysis ===")
        print(f"Nodes: {analysis['node_count']}")
        print(f"Hyperedges: {analysis['edge_count']}")
        print("\nEdge types:")
        for etype, count in analysis['edge_types'].items():
            print(f"  - {etype}: {count}")
        print("\nMost connected nodes:")
        for node in analysis['most_connected_nodes']:
            print(f"  - {node['id']}: degree {node['degree']}")
        print("\nLargest hyperedges:")
        for edge in analysis['largest_edges']:
            print(f"  - {edge['id']} ({edge['type']}): {edge['size']} members")

    if args.summary:
        print(kg.export_summary())

    if args.output or (not args.analyze and not args.summary and not args.query):
        output_path = Path(args.output) if args.output else None
        if HNX_AVAILABLE and MPL_AVAILABLE:
            kg.visualize(output_path=output_path,
                        title="QBP Knowledge Hypergraph" + (" (Demo)" if args.demo else ""))
        else:
            print("\nTo visualize, install: pip install hypernetx matplotlib")
            print("\nText summary instead:")
            print(kg.export_summary())


if __name__ == '__main__':
    main()
