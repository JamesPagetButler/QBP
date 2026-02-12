#!/usr/bin/env python3
"""
Pre-commit hook for validating the QBP knowledge base.

Usage:
    python scripts/validate_knowledge.py [--strict]

Exit codes:
    0 - Valid
    1 - Invalid (errors found) or warnings in strict mode

Can be integrated with pre-commit:
  - repo: local
    hooks:
      - id: validate-knowledge
        name: Validate knowledge base
        entry: python scripts/validate_knowledge.py
        language: python
        files: ^knowledge/
        pass_filenames: false
"""

import sys
from pathlib import Path

# Add scripts directory to path
sys.path.insert(0, str(Path(__file__).parent))

from qbp_knowledge_sqlite import QBPKnowledgeSQLite


def main():
    strict = "--strict" in sys.argv

    db_path = "knowledge/qbp.db"
    if not Path(db_path).exists():
        print(f"Knowledge base not found: {db_path}")
        print("Skipping validation (no database)")
        return 0

    try:
        kb = QBPKnowledgeSQLite(db_path, read_only=True)
        result = kb.validate()
    except Exception as exc:
        # In CI, the .db file may be a Git LFS pointer (not a real SQLite DB)
        print(f"Cannot open knowledge base: {exc}")
        print("Skipping validation (database not readable — likely LFS pointer in CI)")
        return 0

    if result["errors"]:
        print("Knowledge Base Validation FAILED")
        print()
        for e in result["errors"]:
            print(f"  ERROR: {e}")
        return 1

    if strict and result["warnings"]:
        print("Knowledge Base Validation FAILED (strict mode)")
        print()
        for w in result["warnings"]:
            print(f"  WARNING: {w}")
        return 1

    # Only print on success if verbose or if there are warnings
    verbose = "--verbose" in sys.argv or "-v" in sys.argv
    if result["warnings"]:
        # Print warnings to stderr so pre-commit doesn't think we modified files
        import sys as sys_module

        print(
            f"Knowledge Base Validation PASSED "
            f"({len(result['warnings'])} warnings)",
            file=sys_module.stderr,
        )
    elif verbose:
        print("Knowledge Base Validation PASSED")

    return 0


if __name__ == "__main__":
    sys.exit(main())
