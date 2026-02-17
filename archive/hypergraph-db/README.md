# Hypergraph-DB Knowledge System (Archived)

**Status:** Superseded by SQLite hypergraph (`knowledge/qbp.db`)
**Archived:** 2026-02-17
**Original issues:** #235 Phase 1 (#236), Phase 2 (#237)

## What this was

The original QBP knowledge system used [Hypergraph-DB](https://pypi.org/project/hypergraph-db/) (a Python pickle-based hypergraph store). It was replaced with a SQLite-based implementation during Sprint 2 because:

- Pickle format is not queryable, not concurrent, not inspectable
- No SQL -- all queries required Python loops
- No ACID transactions
- No standard tooling (DB Browser, etc.)

## Contents

| File | Purpose |
|------|---------|
| `qbp.hgdb` | Hypergraph-DB binary (pickle format) |
| `qbp_knowledge.py` | Original Python wrapper API |
| `seed_qbp_knowledge.py` | Initial data seeding script |
| `migrate_to_sqlite.py` | One-time migration to SQLite |
| `migrate_yaml_to_hypergraph.py` | Earlier migration from YAML to Hypergraph-DB |
| `index.yaml` | YAML index (pre-Hypergraph-DB era) |
| `sources/`, `concepts/`, `claims/`, `questions/` | Legacy YAML data directories |

## Current system

See `knowledge/README.md` and `scripts/qbp_knowledge_sqlite.py`.
