#!/usr/bin/env python3
"""
Migration Script: Hypergraph-DB → SQLite

Converts the QBP knowledge base from Hypergraph-DB's pickle format
to the new SQLite backend for better querying and tooling support.

Usage:
    python scripts/migrate_to_sqlite.py
    python scripts/migrate_to_sqlite.py --source knowledge/qbp.hgdb --target knowledge/qbp.db
    python scripts/migrate_to_sqlite.py --dry-run
"""

import argparse
import sys
from pathlib import Path
from typing import Any, Dict, cast

# Add scripts to path
sys.path.insert(0, str(Path(__file__).parent))


def migrate(source_path: str, target_path: str, dry_run: bool = False) -> dict:
    """
    Migrate from Hypergraph-DB to SQLite.

    Returns migration statistics.
    """
    from hyperdb import HypergraphDB
    from qbp_knowledge_sqlite import QBPKnowledgeSQLite

    print(f"Migration: Hypergraph-DB → SQLite")
    print(f"  Source: {source_path}")
    print(f"  Target: {target_path}")
    print(f"  Dry run: {dry_run}")
    print()

    # Load source
    if not Path(source_path).exists():
        print(f"Error: Source file not found: {source_path}")
        sys.exit(1)

    hg = HypergraphDB(storage_file=source_path)

    # Track stats with properly typed variables
    vertex_total = 0
    vertex_by_type: Dict[str, int] = {}
    hyperedge_total = 0
    hyperedge_by_type: Dict[str, int] = {}
    incidences_count = 0

    # Count source data
    print("Scanning source data...")
    for v_id in hg.all_v:
        v_data = cast(Dict[str, Any], hg.v(v_id))
        v_type = v_data.get("type", "Unknown")
        vertex_total += 1
        vertex_by_type[v_type] = vertex_by_type.get(v_type, 0) + 1

    for edge in hg.all_e:
        e_data = cast(Dict[str, Any], hg.e(edge))
        e_type = e_data.get("type", "unknown")
        hyperedge_total += 1
        hyperedge_by_type[e_type] = hyperedge_by_type.get(e_type, 0) + 1
        incidences_count += len(edge)

    print(f"  Vertices: {vertex_total}")
    for vtype, count in vertex_by_type.items():
        print(f"    - {vtype}: {count}")
    print(f"  Hyperedges: {hyperedge_total}")
    for etype, count in hyperedge_by_type.items():
        print(f"    - {etype}: {count}")
    print(f"  Incidences: {incidences_count}")
    print()

    stats: Dict[str, Any] = {
        "vertices": {"total": vertex_total, "by_type": vertex_by_type},
        "hyperedges": {"total": hyperedge_total, "by_type": hyperedge_by_type},
        "incidences": incidences_count,
    }

    if dry_run:
        print("Dry run complete. No changes made.")
        return stats

    # Perform migration
    print("Migrating to SQLite...")

    # Remove existing target if present
    target = Path(target_path)
    if target.exists():
        print(f"  Removing existing {target_path}")
        target.unlink()

    # Create new SQLite database
    kb = QBPKnowledgeSQLite(target_path)

    # Migrate vertices
    print("  Migrating vertices...")
    for v_id in hg.all_v:
        v_data = cast(Dict[str, Any], hg.v(v_id))
        v_type = v_data.pop("type", "Unknown")
        try:
            kb.add_vertex(v_id, v_type, v_data)
        except Exception as err:
            print(f"    Warning: Failed to migrate vertex {v_id}: {err}")

    # Migrate hyperedges
    print("  Migrating hyperedges...")
    for i, edge in enumerate(hg.all_e):
        e_data = cast(Dict[str, Any], hg.e(edge))
        e_type = e_data.pop("type", "unknown")
        edge_id = f"e{i}_{e_type}"
        try:
            kb.add_hyperedge(edge_id, e_type, list(edge), e_data)
        except Exception as err:
            print(f"    Warning: Failed to migrate edge {edge_id}: {err}")

    print()
    print("Migration complete!")
    print()

    # Verify
    result = cast(Dict[str, Any], kb.summary())
    print("Verification:")
    result_vertices = cast(Dict[str, Any], result["vertices"])
    result_hyperedges = cast(Dict[str, Any], result["hyperedges"])
    print(f"  Vertices: {result_vertices['total']}")
    print(f"  Hyperedges: {result_hyperedges['total']}")
    print(f"  Incidences: {result['incidences']}")
    print(f"  Database: {result['db_path']}")

    # Check counts match
    if result_vertices["total"] != vertex_total:
        print("\n  WARNING: Vertex count mismatch!")
    if result_hyperedges["total"] != hyperedge_total:
        print("\n  WARNING: Hyperedge count mismatch!")

    return stats


def main():
    parser = argparse.ArgumentParser(
        description="Migrate QBP knowledge base from Hypergraph-DB to SQLite"
    )
    parser.add_argument(
        "--source",
        default="knowledge/qbp.hgdb",
        help="Source Hypergraph-DB file (default: knowledge/qbp.hgdb)",
    )
    parser.add_argument(
        "--target",
        default="knowledge/qbp.db",
        help="Target SQLite database (default: knowledge/qbp.db)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be migrated without making changes",
    )

    args = parser.parse_args()
    migrate(args.source, args.target, args.dry_run)


if __name__ == "__main__":
    main()
