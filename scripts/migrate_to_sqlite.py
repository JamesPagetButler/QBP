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
import json
import sys
from pathlib import Path

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

    stats = {
        "vertices": {"total": 0, "by_type": {}},
        "hyperedges": {"total": 0, "by_type": {}},
        "incidences": 0,
    }

    # Count source data
    print("Scanning source data...")
    for v_id in hg.all_v:
        v_data = hg.v(v_id)
        v_type = v_data.get("type", "Unknown")
        stats["vertices"]["total"] += 1
        stats["vertices"]["by_type"][v_type] = (
            stats["vertices"]["by_type"].get(v_type, 0) + 1
        )

    for e in hg.all_e:
        e_data = hg.e(e)
        e_type = e_data.get("type", "unknown")
        stats["hyperedges"]["total"] += 1
        stats["hyperedges"]["by_type"][e_type] = (
            stats["hyperedges"]["by_type"].get(e_type, 0) + 1
        )
        stats["incidences"] += len(e)

    print(f"  Vertices: {stats['vertices']['total']}")
    for vtype, count in stats["vertices"]["by_type"].items():
        print(f"    - {vtype}: {count}")
    print(f"  Hyperedges: {stats['hyperedges']['total']}")
    for etype, count in stats["hyperedges"]["by_type"].items():
        print(f"    - {etype}: {count}")
    print(f"  Incidences: {stats['incidences']}")
    print()

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
        v_data = hg.v(v_id)
        v_type = v_data.pop("type", "Unknown")
        try:
            kb.add_vertex(v_id, v_type, v_data)
        except Exception as e:
            print(f"    Warning: Failed to migrate vertex {v_id}: {e}")

    # Migrate hyperedges
    print("  Migrating hyperedges...")
    for i, e in enumerate(hg.all_e):
        e_data = hg.e(e)
        e_type = e_data.pop("type", "unknown")
        edge_id = f"e{i}_{e_type}"
        try:
            kb.add_hyperedge(edge_id, e_type, list(e), e_data)
        except Exception as e:
            print(f"    Warning: Failed to migrate edge {edge_id}: {e}")

    print()
    print("Migration complete!")
    print()

    # Verify
    result = kb.summary()
    print("Verification:")
    print(f"  Vertices: {result['vertices']['total']}")
    print(f"  Hyperedges: {result['hyperedges']['total']}")
    print(f"  Incidences: {result['incidences']}")
    print(f"  Database: {result['db_path']}")

    # Check counts match
    if result["vertices"]["total"] != stats["vertices"]["total"]:
        print(f"\n  WARNING: Vertex count mismatch!")
    if result["hyperedges"]["total"] != stats["hyperedges"]["total"]:
        print(f"\n  WARNING: Hyperedge count mismatch!")

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
