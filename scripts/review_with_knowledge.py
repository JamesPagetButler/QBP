#!/usr/bin/env python3
"""
Review PR against the QBP knowledge graph.

Takes a PR number (or file list), identifies changed files, and generates
a "Knowledge Impact" section for review comments.

Usage:
    python scripts/review_with_knowledge.py 243
    python scripts/review_with_knowledge.py --files src/qphysics.py proofs/QBP/Basic.lean
"""

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import List

# Add scripts directory to path
sys.path.insert(0, str(Path(__file__).parent))

from qbp_knowledge_sqlite import QBPKnowledgeSQLite


def get_pr_files(pr_number: int) -> List[str]:
    """Get list of changed files from a PR using gh CLI."""
    gh_path = os.environ.get("GH_PATH", "/home/prime/.local/bin/gh")
    try:
        result = subprocess.run(
            [gh_path, "pr", "diff", str(pr_number), "--name-only"],
            capture_output=True,
            text=True,
            check=True,
        )
        return [f.strip() for f in result.stdout.strip().split("\n") if f.strip()]
    except subprocess.CalledProcessError as e:
        print(f"Error getting PR diff: {e.stderr}", file=sys.stderr)
        return []


def generate_knowledge_impact(files: List[str], kb: QBPKnowledgeSQLite) -> str:
    """Generate a Markdown "Knowledge Impact" section from changed files."""
    suggestions = kb.suggest_updates(files)
    summary = kb.summary()

    lines = [
        "## Knowledge Graph Impact",
        "",
        f"*Knowledge base: {summary['vertices']['total']} vertices, "
        f"{summary['hyperedges']['total']} hyperedges*",
        "",
    ]

    if not suggestions:
        lines.append("No knowledge graph impacts detected for this PR.")
        return "\n".join(lines)

    # Group by impact type
    by_type: dict[str, list[dict[str, str]]] = {}
    for s in suggestions:
        t = s["type"]
        if t not in by_type:
            by_type[t] = []
        by_type[t].append(s)

    for impact_type, items in by_type.items():
        lines.append(f"### {impact_type.title()} Changes")
        lines.append("")
        for item in items:
            lines.append(f"- `{item['file']}`: {item['action']}")
        lines.append("")

    # Add recommended actions
    has_proofs = any(s["type"] == "proof" for s in suggestions)
    has_claims = any(s["type"] == "claim" for s in suggestions)

    if has_proofs or has_claims:
        lines.extend(
            [
                "### Recommended Actions",
                "",
            ]
        )
        if has_proofs:
            lines.append(
                "- [ ] Run `python scripts/qbp_knowledge_sqlite.py scan-proofs --apply`"
            )
            lines.append(
                "- [ ] Run `python scripts/qbp_knowledge_sqlite.py validate-proofs`"
            )
        if has_claims:
            lines.append("- [ ] Review affected claims in knowledge graph")
        lines.append("")

    return "\n".join(lines)


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Review PR against knowledge graph")
    parser.add_argument(
        "pr_number",
        nargs="?",
        type=int,
        help="PR number to review",
    )
    parser.add_argument(
        "--files",
        nargs="+",
        help="Explicit file list (instead of PR number)",
    )
    parser.add_argument(
        "--db",
        default="knowledge/qbp.db",
        help="Knowledge database path",
    )

    args = parser.parse_args()

    if not args.pr_number and not args.files:
        parser.error("Provide either a PR number or --files")

    if args.files:
        files = args.files
    else:
        files = get_pr_files(args.pr_number)
        if not files:
            print("No files found in PR", file=sys.stderr)
            sys.exit(1)

    kb = QBPKnowledgeSQLite(args.db, read_only=True)
    report = generate_knowledge_impact(files, kb)
    print(report)


if __name__ == "__main__":
    main()
