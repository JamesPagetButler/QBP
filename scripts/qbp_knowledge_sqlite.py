#!/usr/bin/env python3
"""
QBP Hypergraph Knowledge System - SQLite Backend

SQLite-based hypergraph storage with full querying capabilities.
Replaces Hypergraph-DB's pickle format with a proper database.

Schema:
  - vertices: id (PK), type, data (JSON)
  - hyperedges: id (PK), type, data (JSON)
  - incidences: vertex_id (FK), edge_id (FK) - the hypergraph structure

Benefits over Hypergraph-DB:
  - SQL querying
  - ACID transactions
  - Concurrent access
  - Standard tooling (DB Browser, etc.)
  - HIF-compatible structure

Usage:
    from qbp_knowledge_sqlite import QBPKnowledgeSQLite

    kb = QBPKnowledgeSQLite("knowledge/qbp.db")
    kb.add_concept("quaternion-state", "Quaternion State", definition="...")
    kb.query_vertices(type="Concept", tag="foundations")
"""

import json
import sqlite3
import sys
from contextlib import contextmanager
from datetime import date
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union, cast

# =============================================================================
# Schema Definitions (same as before, for validation)
# =============================================================================

VERTEX_TYPES = {
    "Source": {
        "required": ["title"],
        "optional": [
            "category",
            "authors",
            "date",
            "url",
            "doi",
            "venue",
            "tags",
            "abstract",
            "key_insights",
            "research_sprint",
            "added_date",
            "added_by",
        ],
    },
    "Concept": {
        "required": ["term"],
        "optional": [
            "definition",
            "formal_definition",
            "aliases",
            "tags",
            "added_date",
            "added_by",
        ],
    },
    "Claim": {
        "required": ["statement"],
        "optional": [
            "context",
            "status",
            "confidence_tier",
            "tags",
            "implications",
            "added_date",
            "added_by",
        ],
    },
    "Question": {
        "required": ["question"],
        "optional": [
            "context",
            "status",
            "priority",
            "tags",
            "related_issues",
            "investigation_approaches",
            "success_criteria",
            "added_date",
            "added_by",
        ],
    },
    "Proof": {
        "required": ["lean_file"],
        "optional": [
            "theorems",
            "verified",
            "no_sorry",
            "tags",
            "added_date",
            "added_by",
        ],
    },
}

HYPEREDGE_TYPES: Dict[str, Dict[str, Any]] = {
    "evidence_chain": {"min_members": 2, "description": "Claim + supporting evidence"},
    "equivalence": {
        "min_members": 2,
        "description": "Mathematically equivalent structures",
    },
    "theory_axioms": {"min_members": 2, "description": "Axioms defining a theory"},
    "research_cluster": {"min_members": 2, "description": "Related research questions"},
    "proof_link": {"min_members": 2, "description": "Claim linked to formal proof"},
    "emergence": {
        "min_members": 2,
        "description": "Concepts yielding emergent property",
    },
    "review_consensus": {"min_members": 2, "description": "Multi-reviewer agreement"},
    "investigation": {
        "min_members": 2,
        "description": "Question + investigation sources",
    },
}


# =============================================================================
# SQLite Hypergraph Database
# =============================================================================


class QBPKnowledgeSQLite:
    """
    SQLite-backed hypergraph knowledge base.

    Uses three tables:
    - vertices: stores nodes with JSON attributes
    - hyperedges: stores edges with JSON attributes
    - incidences: links vertices to edges (the hypergraph structure)
    """

    SCHEMA_VERSION = 1

    def __init__(self, db_path: str = "knowledge/qbp.db", read_only: bool = False):
        """Initialize or open the database."""
        self.db_path = Path(db_path)
        self.read_only = read_only

        if not read_only:
            self.db_path.parent.mkdir(parents=True, exist_ok=True)
            self._init_schema()

    @contextmanager
    def _connection(self):
        """Context manager for database connections."""
        if self.read_only:
            # Open in read-only mode via URI
            conn = sqlite3.connect(f"file:{self.db_path}?mode=ro", uri=True)
        else:
            conn = sqlite3.connect(str(self.db_path))
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA foreign_keys = ON")
        try:
            yield conn
            if not self.read_only:
                conn.commit()
        except Exception:
            if not self.read_only:
                conn.rollback()
            raise
        finally:
            conn.close()

    def _init_schema(self):
        """Create tables if they don't exist."""
        with self._connection() as conn:
            conn.executescript(
                """
                -- Metadata table for schema versioning
                CREATE TABLE IF NOT EXISTS metadata (
                    key TEXT PRIMARY KEY,
                    value TEXT
                );

                -- Vertices table (nodes)
                CREATE TABLE IF NOT EXISTS vertices (
                    id TEXT PRIMARY KEY,
                    type TEXT NOT NULL,
                    data JSON NOT NULL,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );

                -- Index for type queries
                CREATE INDEX IF NOT EXISTS idx_vertices_type ON vertices(type);

                -- Hyperedges table
                CREATE TABLE IF NOT EXISTS hyperedges (
                    id TEXT PRIMARY KEY,
                    type TEXT NOT NULL,
                    data JSON NOT NULL,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                );

                -- Index for type queries
                CREATE INDEX IF NOT EXISTS idx_hyperedges_type ON hyperedges(type);

                -- Incidences table (vertex-edge membership)
                CREATE TABLE IF NOT EXISTS incidences (
                    vertex_id TEXT NOT NULL,
                    edge_id TEXT NOT NULL,
                    position INTEGER DEFAULT 0,  -- Order within the edge
                    PRIMARY KEY (vertex_id, edge_id),
                    FOREIGN KEY (vertex_id) REFERENCES vertices(id) ON DELETE CASCADE,
                    FOREIGN KEY (edge_id) REFERENCES hyperedges(id) ON DELETE CASCADE
                );

                -- Indexes for efficient lookups
                CREATE INDEX IF NOT EXISTS idx_incidences_vertex ON incidences(vertex_id);
                CREATE INDEX IF NOT EXISTS idx_incidences_edge ON incidences(edge_id);
            """
            )

            # Set schema version
            conn.execute(
                "INSERT OR REPLACE INTO metadata (key, value) VALUES (?, ?)",
                ("schema_version", str(self.SCHEMA_VERSION)),
            )

    # -------------------------------------------------------------------------
    # Vertex Operations
    # -------------------------------------------------------------------------

    def add_vertex(
        self,
        vertex_id: str,
        vertex_type: str,
        attributes: Dict[str, Any],
        skip_if_exists: bool = True,
    ) -> str:
        """
        Add a vertex with validation.

        Args:
            vertex_id: Unique vertex identifier
            vertex_type: One of the defined vertex types
            attributes: Vertex properties
            skip_if_exists: If True, return existing ID without modification (idempotent).
                           If False, update existing vertex with new data.

        Returns:
            The vertex ID (existing or new)
        """
        if vertex_type not in VERTEX_TYPES:
            raise ValueError(f"Invalid vertex type: {vertex_type}")

        # Check for existing vertex (idempotency)
        with self._connection() as conn:
            existing = conn.execute(
                "SELECT id FROM vertices WHERE id = ?", (vertex_id,)
            ).fetchone()
            if existing and skip_if_exists:
                return vertex_id  # Already exists, return without modification

        # Validate required fields
        schema = VERTEX_TYPES[vertex_type]
        for req in schema["required"]:
            if req not in attributes:
                raise ValueError(f"Missing required field '{req}' for {vertex_type}")

        # Add metadata
        data = {"type": vertex_type, **attributes}
        if "added_date" not in data:
            data["added_date"] = str(date.today())

        with self._connection() as conn:
            conn.execute(
                "INSERT OR REPLACE INTO vertices (id, type, data) VALUES (?, ?, ?)",
                (vertex_id, vertex_type, json.dumps(data)),
            )

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
        return self.add_vertex(
            question_id, "Question", {"question": question, **kwargs}
        )

    def add_proof(self, proof_id: str, lean_file: str, **kwargs) -> str:
        """Add a Proof vertex."""
        if not proof_id.startswith("proof:"):
            proof_id = f"proof:{proof_id}"
        return self.add_vertex(proof_id, "Proof", {"lean_file": lean_file, **kwargs})

    def get_vertex(self, vertex_id: str) -> Optional[Dict[str, Any]]:
        """Get vertex by ID."""
        with self._connection() as conn:
            row = conn.execute(
                "SELECT data FROM vertices WHERE id = ?", (vertex_id,)
            ).fetchone()
            return json.loads(row["data"]) if row else None

    def get_vertices_by_type(self, vertex_type: str) -> List[str]:
        """Get all vertex IDs of a given type."""
        with self._connection() as conn:
            rows = conn.execute(
                "SELECT id FROM vertices WHERE type = ?", (vertex_type,)
            ).fetchall()
            return [row["id"] for row in rows]

    def query_vertices(
        self,
        vertex_type: Optional[str] = None,
        tag: Optional[str] = None,
        search: Optional[str] = None,
    ) -> List[Dict[str, Any]]:
        """
        Query vertices with filters.

        Args:
            vertex_type: Filter by type (Source, Concept, etc.)
            tag: Filter by tag (searches in tags array)
            search: Full-text search in data
        """
        query = "SELECT id, data FROM vertices WHERE 1=1"
        params = []

        if vertex_type:
            query += " AND type = ?"
            params.append(vertex_type)

        if tag:
            query += " AND json_extract(data, '$.tags') LIKE ?"
            params.append(f'%"{tag}"%')

        if search:
            query += " AND data LIKE ?"
            params.append(f"%{search}%")

        with self._connection() as conn:
            rows = conn.execute(query, params).fetchall()
            return [{"id": row["id"], **json.loads(row["data"])} for row in rows]

    def delete_vertex(self, vertex_id: str) -> bool:
        """Delete a vertex (cascades to incidences)."""
        with self._connection() as conn:
            cursor = conn.execute("DELETE FROM vertices WHERE id = ?", (vertex_id,))
            return cursor.rowcount > 0

    # -------------------------------------------------------------------------
    # Hyperedge Operations
    # -------------------------------------------------------------------------

    def add_hyperedge(
        self,
        edge_id: str,
        edge_type: str,
        members: List[str],
        attributes: Dict[str, Any] = None,
        skip_if_exists: bool = True,
    ) -> str:
        """
        Add a hyperedge connecting multiple vertices.

        Args:
            edge_id: Unique edge identifier
            edge_type: One of the defined hyperedge types
            members: List of vertex IDs in this edge
            attributes: Edge properties
            skip_if_exists: If True, return existing ID without modification (idempotent).
                           If False, update existing edge with new data.

        Returns:
            The edge ID (existing or new)
        """
        if edge_type not in HYPEREDGE_TYPES:
            raise ValueError(f"Invalid hyperedge type: {edge_type}")

        schema = HYPEREDGE_TYPES[edge_type]
        if len(members) < schema.get("min_members", 2):
            raise ValueError(
                f"{edge_type} requires at least {schema['min_members']} members"
            )

        # Check for existing edge (idempotency)
        with self._connection() as conn:
            existing = conn.execute(
                "SELECT id FROM hyperedges WHERE id = ?", (edge_id,)
            ).fetchone()
            if existing and skip_if_exists:
                return edge_id  # Already exists, return without modification

        data = {"type": edge_type, **(attributes or {})}
        if "created_date" not in data:
            data["created_date"] = str(date.today())

        with self._connection() as conn:
            # Insert edge
            conn.execute(
                "INSERT OR REPLACE INTO hyperedges (id, type, data) VALUES (?, ?, ?)",
                (edge_id, edge_type, json.dumps(data)),
            )

            # Clear existing incidences for this edge (in case of update)
            conn.execute("DELETE FROM incidences WHERE edge_id = ?", (edge_id,))

            # Insert incidences
            for i, vertex_id in enumerate(members):
                conn.execute(
                    "INSERT INTO incidences (vertex_id, edge_id, position) VALUES (?, ?, ?)",
                    (vertex_id, edge_id, i),
                )

        return edge_id

    def add_evidence_chain(
        self, claim_id: str, evidence_ids: List[str], confidence_tier: int = 2, **kwargs
    ) -> str:
        """Add an evidence chain hyperedge."""
        edge_id = f"ev_{claim_id.replace(':', '_')}_{len(evidence_ids)}"
        members = [claim_id] + evidence_ids
        return self.add_hyperedge(
            edge_id,
            "evidence_chain",
            members,
            {"confidence_tier": confidence_tier, **kwargs},
        )

    def add_proof_link(
        self, claim_id: str, proof_id: str, theorem: str, **kwargs
    ) -> str:
        """Add a proof link hyperedge."""
        edge_id = f"pl_{claim_id.replace(':', '_')}_{proof_id.replace(':', '_')}"
        return self.add_hyperedge(
            edge_id, "proof_link", [claim_id, proof_id], {"theorem": theorem, **kwargs}
        )

    def add_equivalence(
        self, concept_ids: List[str], description: str = "", **kwargs
    ) -> str:
        """Add an equivalence hyperedge."""
        edge_id = f"eq_{len(concept_ids)}_{hash(tuple(concept_ids)) % 10000}"
        return self.add_hyperedge(
            edge_id, "equivalence", concept_ids, {"description": description, **kwargs}
        )

    def get_hyperedge(self, edge_id: str) -> Optional[Dict[str, Any]]:
        """Get hyperedge by ID, including members."""
        with self._connection() as conn:
            row = conn.execute(
                "SELECT data FROM hyperedges WHERE id = ?", (edge_id,)
            ).fetchone()

            if not row:
                return None

            data = json.loads(row["data"])

            # Get members
            members = conn.execute(
                "SELECT vertex_id FROM incidences WHERE edge_id = ? ORDER BY position",
                (edge_id,),
            ).fetchall()
            data["members"] = [m["vertex_id"] for m in members]

            return data

    def get_edges_containing(self, vertex_id: str) -> List[Dict[str, Any]]:
        """Get all hyperedges containing a vertex."""
        with self._connection() as conn:
            rows = conn.execute(
                """
                SELECT h.id, h.data
                FROM hyperedges h
                JOIN incidences i ON h.id = i.edge_id
                WHERE i.vertex_id = ?
            """,
                (vertex_id,),
            ).fetchall()

            results = []
            for row in rows:
                data = json.loads(row["data"])
                data["id"] = row["id"]
                # Get all members
                members = conn.execute(
                    "SELECT vertex_id FROM incidences WHERE edge_id = ? ORDER BY position",
                    (row["id"],),
                ).fetchall()
                data["members"] = [m["vertex_id"] for m in members]
                results.append(data)

            return results

    def get_hyperedges_by_type(self, edge_type: str) -> List[Dict[str, Any]]:
        """Get all hyperedges of a given type."""
        with self._connection() as conn:
            rows = conn.execute(
                "SELECT id, data FROM hyperedges WHERE type = ?", (edge_type,)
            ).fetchall()

            results = []
            for row in rows:
                data = json.loads(row["data"])
                data["id"] = row["id"]
                members = conn.execute(
                    "SELECT vertex_id FROM incidences WHERE edge_id = ? ORDER BY position",
                    (row["id"],),
                ).fetchall()
                data["members"] = [m["vertex_id"] for m in members]
                results.append(data)

            return results

    # -------------------------------------------------------------------------
    # Research Queries (SQL-powered!)
    # -------------------------------------------------------------------------

    def find_weak_claims(self) -> List[Dict[str, Any]]:
        """Find claims with no evidence chain or fewer than 2 evidence sources."""
        with self._connection() as conn:
            # Claims without any evidence_chain edges
            rows = conn.execute(
                """
                SELECT v.id, v.data
                FROM vertices v
                WHERE v.type = 'Claim'
                AND v.id NOT IN (
                    SELECT DISTINCT i.vertex_id
                    FROM incidences i
                    JOIN hyperedges h ON i.edge_id = h.id
                    WHERE h.type = 'evidence_chain'
                )
            """
            ).fetchall()

            return [
                {
                    "id": row["id"],
                    **json.loads(row["data"]),
                    "reason": "no evidence chain",
                }
                for row in rows
            ]

    def find_unproven_claims(self) -> List[Dict[str, Any]]:
        """Find claims without proof_link hyperedges."""
        with self._connection() as conn:
            rows = conn.execute(
                """
                SELECT v.id, v.data
                FROM vertices v
                WHERE v.type = 'Claim'
                AND v.id NOT IN (
                    SELECT DISTINCT i.vertex_id
                    FROM incidences i
                    JOIN hyperedges h ON i.edge_id = h.id
                    WHERE h.type = 'proof_link'
                )
            """
            ).fetchall()

            return [{"id": row["id"], **json.loads(row["data"])} for row in rows]

    def find_research_gaps(self) -> List[Dict[str, Any]]:
        """Find open questions with no investigation hyperedges."""
        with self._connection() as conn:
            rows = conn.execute(
                """
                SELECT v.id, v.data
                FROM vertices v
                WHERE v.type = 'Question'
                AND json_extract(v.data, '$.status') = 'open'
                AND v.id NOT IN (
                    SELECT DISTINCT i.vertex_id
                    FROM incidences i
                    JOIN hyperedges h ON i.edge_id = h.id
                    WHERE h.type = 'investigation'
                )
            """
            ).fetchall()

            return [
                {
                    "id": row["id"],
                    **json.loads(row["data"]),
                    "reason": "no investigation",
                }
                for row in rows
            ]

    def find_bridge_concepts(self, min_degree: int = 3) -> List[Dict[str, Any]]:
        """Find concepts that appear in multiple hyperedges."""
        with self._connection() as conn:
            rows = conn.execute(
                """
                SELECT v.id, v.data, COUNT(DISTINCT i.edge_id) as degree
                FROM vertices v
                JOIN incidences i ON v.id = i.vertex_id
                WHERE v.type = 'Concept'
                GROUP BY v.id
                HAVING degree >= ?
                ORDER BY degree DESC
            """,
                (min_degree,),
            ).fetchall()

            return [
                {"id": row["id"], **json.loads(row["data"]), "degree": row["degree"]}
                for row in rows
            ]

    def trace_evidence(self, claim_id: str) -> Dict[str, Any]:
        """Trace all evidence supporting a claim."""
        claim = self.get_vertex(claim_id)
        if not claim:
            return {"error": f"Claim not found: {claim_id}"}

        edges = self.get_edges_containing(claim_id)
        evidence_chains = [e for e in edges if e.get("type") == "evidence_chain"]
        proof_links = [e for e in edges if e.get("type") == "proof_link"]

        return {
            "claim_id": claim_id,
            "statement": claim.get("statement"),
            "evidence_chains": evidence_chains,
            "proof_links": proof_links,
            "has_formal_proof": len(proof_links) > 0,
            "total_evidence_sources": sum(
                len(e["members"]) - 1 for e in evidence_chains
            ),
        }

    # -------------------------------------------------------------------------
    # Statistics & Summary
    # -------------------------------------------------------------------------

    def summary(self) -> Dict[str, Any]:
        """Get database statistics."""
        with self._connection() as conn:
            vertex_counts = conn.execute(
                """
                SELECT type, COUNT(*) as count FROM vertices GROUP BY type
            """
            ).fetchall()

            edge_counts = conn.execute(
                """
                SELECT type, COUNT(*) as count FROM hyperedges GROUP BY type
            """
            ).fetchall()

            total_vertices = conn.execute("SELECT COUNT(*) FROM vertices").fetchone()[0]
            total_edges = conn.execute("SELECT COUNT(*) FROM hyperedges").fetchone()[0]
            total_incidences = conn.execute(
                "SELECT COUNT(*) FROM incidences"
            ).fetchone()[0]

        return {
            "vertices": {
                "total": total_vertices,
                "by_type": {row["type"]: row["count"] for row in vertex_counts},
            },
            "hyperedges": {
                "total": total_edges,
                "by_type": {row["type"]: row["count"] for row in edge_counts},
            },
            "incidences": total_incidences,
            "db_path": str(self.db_path),
        }

    # -------------------------------------------------------------------------
    # Validation
    # -------------------------------------------------------------------------

    def validate(self) -> Dict[str, Any]:
        """
        Validate the entire knowledge base for integrity issues.

        Returns:
            {
                "valid": bool,
                "errors": [...],
                "warnings": [...],
                "stats": {...}
            }
        """
        errors: List[str] = []
        warnings: List[str] = []

        with self._connection() as conn:
            # 1. Validate vertex schemas
            for row in conn.execute("SELECT id, type, data FROM vertices"):
                v_id = row["id"]
                v_type = row["type"]
                data = json.loads(row["data"])

                # Check type is valid
                if v_type not in VERTEX_TYPES:
                    errors.append(f"Vertex {v_id}: invalid type '{v_type}'")
                    continue

                # Check required fields
                schema = VERTEX_TYPES[v_type]
                for req in schema["required"]:
                    if req not in data:
                        errors.append(f"Vertex {v_id}: missing required field '{req}'")

                # Check ID prefix convention
                expected_prefix = v_type.lower() + ":"
                if not v_id.startswith(expected_prefix):
                    warnings.append(
                        f"Vertex {v_id}: ID should start with '{expected_prefix}'"
                    )

            # 2. Validate hyperedge schemas
            for row in conn.execute("SELECT id, type, data FROM hyperedges"):
                e_id = row["id"]
                e_type = row["type"]

                # Check type is valid
                if e_type not in HYPEREDGE_TYPES:
                    errors.append(f"Hyperedge {e_id}: invalid type '{e_type}'")
                    continue

                # Check minimum members
                schema = HYPEREDGE_TYPES[e_type]
                member_count = conn.execute(
                    "SELECT COUNT(*) FROM incidences WHERE edge_id = ?", (e_id,)
                ).fetchone()[0]

                min_members = schema.get("min_members", 2)
                if member_count < min_members:
                    errors.append(
                        f"Hyperedge {e_id}: has {member_count} members, "
                        f"requires at least {min_members}"
                    )

            # 3. Check referential integrity (dangling references)
            # Note: SQLite FOREIGN KEYs should prevent this, but check anyway
            dangling = conn.execute(
                """
                SELECT i.vertex_id, i.edge_id
                FROM incidences i
                LEFT JOIN vertices v ON i.vertex_id = v.id
                WHERE v.id IS NULL
                """
            ).fetchall()
            for row in dangling:
                errors.append(
                    f"Dangling reference: vertex '{row['vertex_id']}' "
                    f"in edge '{row['edge_id']}' does not exist"
                )

            # 4. Check for orphan vertices (not in any hyperedge)
            orphans = conn.execute(
                """
                SELECT v.id FROM vertices v
                LEFT JOIN incidences i ON v.id = i.vertex_id
                WHERE i.edge_id IS NULL
                """
            ).fetchall()
            for row in orphans:
                warnings.append(f"Orphan vertex: {row['id']} is not in any hyperedge")

            # 5. Check for empty hyperedges
            empty_edges = conn.execute(
                """
                SELECT e.id FROM hyperedges e
                LEFT JOIN incidences i ON e.id = i.edge_id
                WHERE i.vertex_id IS NULL
                """
            ).fetchall()
            for row in empty_edges:
                errors.append(f"Empty hyperedge: {row['id']} has no members")

            # Stats
            total_vertices = conn.execute("SELECT COUNT(*) FROM vertices").fetchone()[0]
            total_edges = conn.execute("SELECT COUNT(*) FROM hyperedges").fetchone()[0]

        return {
            "valid": len(errors) == 0,
            "errors": errors,
            "warnings": warnings,
            "stats": {
                "vertices": total_vertices,
                "hyperedges": total_edges,
                "error_count": len(errors),
                "warning_count": len(warnings),
            },
        }

    # -------------------------------------------------------------------------
    # Export (HIF and HyperNetX)
    # -------------------------------------------------------------------------

    def export_hif(self, output_path: str) -> str:
        """Export to Hypergraph Interchange Format (HIF)."""
        nodes: List[Dict[str, Any]] = []
        edges: List[Dict[str, Any]] = []
        incidences: List[Dict[str, str]] = []

        with self._connection() as conn:
            # Export vertices
            for row in conn.execute("SELECT id, data FROM vertices"):
                nodes.append({"node": row["id"], "attrs": json.loads(row["data"])})

            # Export edges and incidences
            for row in conn.execute("SELECT id, data FROM hyperedges"):
                edges.append({"edge": row["id"], "attrs": json.loads(row["data"])})

            for row in conn.execute("SELECT vertex_id, edge_id FROM incidences"):
                incidences.append({"node": row["vertex_id"], "edge": row["edge_id"]})

        hif: Dict[str, Any] = {
            "network-type": "undirected",
            "metadata": {
                "name": "QBP Knowledge Hypergraph",
                "exported_from": "qbp_knowledge_sqlite",
                "export_date": str(date.today()),
            },
            "nodes": nodes,
            "edges": edges,
            "incidences": incidences,
        }

        with open(output_path, "w") as f:
            json.dump(hif, f, indent=2)

        return output_path

    def to_hypernetx(self):
        """Convert to HyperNetX Hypergraph for analysis."""
        try:
            import hypernetx as hnx
        except ImportError:
            raise ImportError("Requires: pip install hypernetx")

        edges = {}
        with self._connection() as conn:
            for row in conn.execute("SELECT id FROM hyperedges"):
                edge_id = row["id"]
                members = conn.execute(
                    "SELECT vertex_id FROM incidences WHERE edge_id = ?", (edge_id,)
                ).fetchall()
                edges[edge_id] = set(m["vertex_id"] for m in members)

        return hnx.Hypergraph(edges)

    # -------------------------------------------------------------------------
    # Import from Hypergraph-DB
    # -------------------------------------------------------------------------

    def suggest_updates(self, file_paths: List[str]) -> List[Dict[str, str]]:
        """
        Suggest knowledge graph updates based on changed files.

        Analyzes file types and paths to identify potential impacts:
        - .lean files → proof vertices, proof_link edges
        - research/*_expected_results.md → claim vertices
        - src/qphysics.py → concept/claim consistency
        - paper/*.md → source vertices
        - analysis/ → evidence chain updates
        """
        suggestions: List[Dict[str, str]] = []

        for fp in file_paths:
            path = Path(fp)
            name = path.name
            parts = path.parts

            if name.endswith(".lean"):
                suggestions.append(
                    {
                        "file": fp,
                        "type": "proof",
                        "action": f"Run `scan-proofs --apply` to sync Proof vertex for {name}",
                        "impact": "May affect proof_link hyperedges",
                    }
                )
            elif "research" in parts and "expected_results" in name:
                suggestions.append(
                    {
                        "file": fp,
                        "type": "claim",
                        "action": "Review claims derived from this ground truth",
                        "impact": "Claims may need updating if predictions changed",
                    }
                )
            elif name == "qphysics.py":
                suggestions.append(
                    {
                        "file": fp,
                        "type": "concept",
                        "action": "Verify axiom implementations match knowledge graph",
                        "impact": "Core physics changes affect all downstream claims",
                    }
                )
            elif "paper" in parts and name.endswith(".md"):
                suggestions.append(
                    {
                        "file": fp,
                        "type": "source",
                        "action": "Check if Source vertices need updating",
                        "impact": "Design rationale changes may affect claim context",
                    }
                )
            elif "analysis" in parts:
                suggestions.append(
                    {
                        "file": fp,
                        "type": "evidence",
                        "action": "Verify evidence chains include this analysis",
                        "impact": "New analysis may strengthen or weaken claims",
                    }
                )
            elif "viz" in parts or "theme" in name:
                suggestions.append(
                    {
                        "file": fp,
                        "type": "visualization",
                        "action": "No knowledge graph impact (visualization only)",
                        "impact": "None",
                    }
                )

        return suggestions

    def generate_report(self) -> str:
        """
        Generate a full knowledge graph analysis report for Theory Refinement.

        Returns Markdown-formatted report covering:
        - Summary statistics
        - Weak claims (no evidence)
        - Unproven claims (no proof_link)
        - Research gaps (open questions without investigation)
        - Bridge concepts (high-degree nodes)
        """
        summary = self.summary()
        weak = self.find_weak_claims()
        unproven = self.find_unproven_claims()
        gaps = self.find_research_gaps()
        bridges = self.find_bridge_concepts(min_degree=2)

        lines = [
            "# Knowledge Graph Analysis Report",
            "",
            "## Summary",
            "",
            f"- **Vertices:** {summary['vertices']['total']}",
        ]
        for vtype, count in summary["vertices"].get("by_type", {}).items():
            lines.append(f"  - {vtype}: {count}")
        lines.append(f"- **Hyperedges:** {summary['hyperedges']['total']}")
        for etype, count in summary["hyperedges"].get("by_type", {}).items():
            lines.append(f"  - {etype}: {count}")

        lines.extend(
            [
                "",
                "## Weak Claims (No Evidence Chain)",
                "",
            ]
        )
        if weak:
            for c in weak:
                lines.append(
                    f"- **{c['id']}**: {c.get('statement', 'N/A')} "
                    f"— {c.get('reason', 'no evidence')}"
                )
        else:
            lines.append("None found — all claims have evidence chains.")

        lines.extend(
            [
                "",
                "## Unproven Claims (No proof_link)",
                "",
            ]
        )
        if unproven:
            for c in unproven:
                lines.append(f"- **{c['id']}**: {c.get('statement', 'N/A')}")
        else:
            lines.append("None found — all claims have formal proofs.")

        lines.extend(
            [
                "",
                "## Research Gaps (Open Questions Without Investigation)",
                "",
            ]
        )
        if gaps:
            for q in gaps:
                lines.append(
                    f"- **{q['id']}**: {q.get('question', 'N/A')} "
                    f"— {q.get('reason', 'no investigation')}"
                )
        else:
            lines.append("None found — all open questions have investigations.")

        lines.extend(
            [
                "",
                "## Bridge Concepts (High Connectivity)",
                "",
            ]
        )
        if bridges:
            for b in bridges:
                lines.append(
                    f"- **{b['id']}**: {b.get('term', 'N/A')} "
                    f"(degree: {b.get('degree', 0)})"
                )
        else:
            lines.append("No bridge concepts found (min degree: 2).")

        lines.append("")
        return "\n".join(lines)

    def import_hif(self, hif_path: str) -> Dict[str, int]:
        """
        Import data from Hypergraph Interchange Format (HIF) JSON.

        Args:
            hif_path: Path to HIF JSON file

        Returns:
            Dict with counts of imported nodes, edges, incidences
        """
        with open(hif_path) as f:
            hif = json.load(f)

        counts = {"nodes": 0, "edges": 0, "incidences": 0}

        # Import nodes
        for node in hif.get("nodes", []):
            node_id = node["node"]
            attrs = node.get("attrs", {})
            node_type = attrs.pop("type", "Concept")  # Default type

            # Validate type exists
            if node_type not in VERTEX_TYPES:
                node_type = "Concept"

            # Extract the required field based on type
            schema = VERTEX_TYPES[node_type]
            for req in schema["required"]:
                if req not in attrs:
                    # Try to infer from node_id
                    attrs[req] = node_id.split(":")[-1].replace("-", " ").title()

            self.add_vertex(node_id, node_type, attrs, skip_if_exists=False)
            counts["nodes"] += 1

        # Import edges
        for edge_entry in hif.get("edges", []):
            edge_id = edge_entry["edge"]
            attrs = edge_entry.get("attrs", {})
            edge_type = attrs.pop("type", "evidence_chain")

            if edge_type not in HYPEREDGE_TYPES:
                edge_type = "evidence_chain"

            # Collect members from incidences
            members = [
                inc["node"]
                for inc in hif.get("incidences", [])
                if inc["edge"] == edge_id
            ]

            if len(members) >= HYPEREDGE_TYPES[edge_type].get("min_members", 2):
                self.add_hyperedge(
                    edge_id, edge_type, members, attrs, skip_if_exists=False
                )
                counts["edges"] += 1

        counts["incidences"] = sum(
            len([i for i in hif.get("incidences", []) if i["edge"] == e["edge"]])
            for e in hif.get("edges", [])
        )

        return counts

    def visualize(self, output_path: str, title: str = "QBP Knowledge Hypergraph"):
        """
        Visualize the hypergraph using HyperNetX and save as PNG.

        Args:
            output_path: Path for output PNG file
            title: Plot title
        """
        try:
            import hypernetx as hnx
            import matplotlib.pyplot as plt
        except ImportError:
            raise ImportError("Requires: pip install hypernetx matplotlib")

        H = self.to_hypernetx()

        fig, ax = plt.subplots(1, 1, figsize=(14, 10))
        hnx.draw(H, ax=ax)
        ax.set_title(title, fontsize=14)
        fig.tight_layout()
        fig.savefig(output_path, dpi=150, bbox_inches="tight")
        plt.close(fig)

        return output_path

    @classmethod
    def import_from_hypergraphdb(
        cls, hgdb_path: str, sqlite_path: str
    ) -> "QBPKnowledgeSQLite":
        """
        Import data from Hypergraph-DB format to SQLite.

        Args:
            hgdb_path: Path to existing .hgdb file
            sqlite_path: Path for new SQLite database
        """
        from hyperdb import HypergraphDB

        # Load source
        hg = HypergraphDB(storage_file=hgdb_path)

        # Create new SQLite database
        kb = cls(sqlite_path)

        # Import vertices
        for v_id in hg.all_v:
            v_data = hg.v(v_id)
            v_type = v_data.pop("type", "Unknown")
            kb.add_vertex(v_id, v_type, v_data)

        # Import hyperedges
        for i, e in enumerate(hg.all_e):
            e_data = hg.e(e)
            e_type = e_data.pop("type", "unknown")
            edge_id = f"e{i}_{e_type}"
            kb.add_hyperedge(edge_id, e_type, list(e), e_data)

        return kb


# =============================================================================
# CLI
# =============================================================================


def main():
    import argparse

    parser = argparse.ArgumentParser(description="QBP Knowledge System (SQLite)")
    parser.add_argument("--db", default="knowledge/qbp.db", help="Database path")

    subparsers = parser.add_subparsers(dest="command")

    # Summary
    subparsers.add_parser("summary", help="Show database summary")

    # Query
    query_p = subparsers.add_parser("query", help="Query vertices")
    query_p.add_argument("--type", help="Vertex type")
    query_p.add_argument("--tag", help="Filter by tag")
    query_p.add_argument("--search", help="Search in data")

    # Validate
    validate_p = subparsers.add_parser(
        "validate", help="Validate knowledge base integrity"
    )
    validate_p.add_argument(
        "--strict", action="store_true", help="Exit with error on warnings too"
    )

    # Research queries
    subparsers.add_parser("weak-claims", help="Find claims with weak evidence")
    subparsers.add_parser("unproven", help="Find claims without proofs")
    subparsers.add_parser("gaps", help="Find research gaps")
    subparsers.add_parser("bridges", help="Find bridge concepts")

    # Export
    export_p = subparsers.add_parser("export", help="Export data")
    export_p.add_argument("--format", choices=["hif", "json"], default="hif")
    export_p.add_argument("--output", required=True, help="Output file")

    # Import from Hypergraph-DB
    import_p = subparsers.add_parser("import", help="Import from Hypergraph-DB")
    import_p.add_argument(
        "--from", dest="source", required=True, help="Source .hgdb file"
    )

    # Import from HIF
    import_hif_p = subparsers.add_parser("import-hif", help="Import from HIF JSON")
    import_hif_p.add_argument("file", help="HIF JSON file to import")

    # Scan proofs
    scan_p = subparsers.add_parser(
        "scan-proofs", help="Scan Lean files and sync Proof vertices"
    )
    scan_p.add_argument(
        "--apply",
        action="store_true",
        help="Write to knowledge graph (default: dry-run)",
    )

    # Validate proofs
    val_proofs_p = subparsers.add_parser(
        "validate-proofs", help="Validate proof_link hyperedges"
    )
    val_proofs_p.add_argument(
        "--apply",
        action="store_true",
        help="Sync scan results before validating",
    )

    # Trace evidence
    trace_p = subparsers.add_parser(
        "trace", help="Trace all evidence supporting a claim"
    )
    trace_p.add_argument("claim_id", help="Claim ID (with or without claim: prefix)")

    # Suggest updates
    suggest_p = subparsers.add_parser(
        "suggest-updates",
        help="Suggest knowledge graph impacts from changed files",
    )
    suggest_p.add_argument("files", nargs="+", help="Changed file paths")

    # Report
    subparsers.add_parser(
        "report",
        help="Generate full knowledge graph analysis for Theory Refinement",
    )

    # Visualize
    viz_p = subparsers.add_parser(
        "visualize", help="Visualize hypergraph as PNG (requires HyperNetX)"
    )
    viz_p.add_argument(
        "--output",
        default="workspace/qbp_knowledge.png",
        help="Output PNG path (default: workspace/qbp_knowledge.png)",
    )
    viz_p.add_argument("--title", default="QBP Knowledge Hypergraph", help="Plot title")

    args = parser.parse_args()

    if args.command == "import":
        kb = QBPKnowledgeSQLite.import_from_hypergraphdb(args.source, args.db)
        print(f"Imported to {args.db}")
        print(json.dumps(kb.summary(), indent=2))
    else:
        kb = QBPKnowledgeSQLite(args.db)

        if args.command == "summary":
            print(json.dumps(kb.summary(), indent=2))

        elif args.command == "query":
            results = kb.query_vertices(
                vertex_type=args.type, tag=args.tag, search=args.search
            )
            print(json.dumps(results, indent=2))

        elif args.command == "weak-claims":
            results = kb.find_weak_claims()
            print(json.dumps(results, indent=2))

        elif args.command == "unproven":
            results = kb.find_unproven_claims()
            print(json.dumps(results, indent=2))

        elif args.command == "gaps":
            results = kb.find_research_gaps()
            print(json.dumps(results, indent=2))

        elif args.command == "bridges":
            results = kb.find_bridge_concepts()
            print(json.dumps(results, indent=2))

        elif args.command == "validate":
            result = kb.validate()
            print(f"Knowledge Base Validation: {args.db}")
            print(f"{'=' * 50}")
            print(f"Status: {'VALID' if result['valid'] else 'INVALID'}")
            print(
                f"Vertices: {result['stats']['vertices']}, "
                f"Hyperedges: {result['stats']['hyperedges']}"
            )
            print()

            if result["errors"]:
                print(f"ERRORS ({len(result['errors'])}):")
                for e in result["errors"]:
                    print(f"  ✗ {e}")
                print()

            if result["warnings"]:
                print(f"WARNINGS ({len(result['warnings'])}):")
                for w in result["warnings"]:
                    print(f"  ⚠ {w}")
                print()

            if not result["valid"]:
                sys.exit(1)
            elif args.strict and result["warnings"]:
                print("Failing due to --strict mode")
                sys.exit(1)
            else:
                print("✓ Validation passed")

        elif args.command == "export":
            if args.format == "hif":
                kb.export_hif(args.output)
                print(f"Exported HIF to {args.output}")

        elif args.command == "import-hif":
            counts = kb.import_hif(args.file)
            print(f"Imported from {args.file}:")
            print(f"  Nodes: {counts['nodes']}")
            print(f"  Edges: {counts['edges']}")
            print(f"  Incidences: {counts['incidences']}")

        elif args.command == "trace":
            claim_id = args.claim_id
            if not claim_id.startswith("claim:"):
                claim_id = f"claim:{claim_id}"
            result = kb.trace_evidence(claim_id)
            print(json.dumps(result, indent=2))

        elif args.command == "suggest-updates":
            suggestions = kb.suggest_updates(args.files)
            if not suggestions:
                print("No knowledge graph impacts detected for these files.")
            else:
                print("## Knowledge Graph Impact Suggestions\n")
                for s in suggestions:
                    print(f"**{s['file']}** ({s['type']})")
                    print(f"  Action: {s['action']}")
                    print(f"  Impact: {s['impact']}")
                    print()

        elif args.command == "report":
            print(kb.generate_report())

        elif args.command == "visualize":
            output = kb.visualize(args.output, title=args.title)
            print(f"Visualization saved to {output}")

        elif args.command in ("scan-proofs", "validate-proofs"):
            from scan_lean_proofs import scan_all_proofs, sync_to_knowledge_graph
            from scan_lean_proofs import validate_proof_links

            root = Path(__file__).parent.parent
            results = scan_all_proofs(root)

            if args.command == "scan-proofs":
                for lf in results:
                    print(f"\n{lf.path} (namespace: {lf.namespace})")
                    for d in lf.declarations:
                        sorry_marker = " [SORRY]" if d.has_sorry else ""
                        print(f"  L{d.line:3d} {d.kind} {d.name}{sorry_marker}")

                actions = sync_to_knowledge_graph(results, kb, dry_run=not args.apply)
                mode = "Applied" if args.apply else "Dry run"
                print(f"\n{mode}:")
                print(f"  Created: {len(actions['created'])} vertices")
                print(f"  Updated: {len(actions['updated'])} vertices")

            else:  # validate-proofs
                if args.apply:
                    sync_to_knowledge_graph(results, kb, dry_run=False)
                validation = validate_proof_links(results, kb)
                print(f"Proof Link Validation: {validation['checked']} checked")
                print(f"Status: {'VALID' if validation['valid'] else 'INVALID'}")
                for e in validation["errors"]:
                    print(f"  x {e}")
                for w in validation["warnings"]:
                    print(f"  ! {w}")
                if not validation["valid"]:
                    sys.exit(1)

        else:
            parser.print_help()


if __name__ == "__main__":
    main()
