#!/usr/bin/env python3
"""
Research Gate — Hybrid checkpoint between sprints.

Queries the Knowledge Graph for weak claims, research gaps, and unproven
claims, then filters by scope tags to decide whether a full Pre-Sprint
Research phase is needed before the next sprint can begin.

Usage:
    python scripts/research_gate.py --scope sprint-4 experiment-04
    python scripts/research_gate.py              # global-only analysis

Exit codes:
    0 - PASS  (no scoped blocking items)
    1 - BLOCK (scoped weak claims or research gaps found)
    2 - Error (database not found, etc.)
"""

import argparse
import sys
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

# Add scripts directory to path
sys.path.insert(0, str(Path(__file__).parent))

from qbp_knowledge_sqlite import QBPKnowledgeSQLite

DB_PATH = "knowledge/qbp.db"


def tags_for_item(item: Dict[str, Any]) -> Set[str]:
    """Extract the set of tags from a KG item."""
    raw = item.get("tags", [])
    if isinstance(raw, list):
        return {str(t).lower() for t in raw}
    if isinstance(raw, str):
        return {t.strip().lower() for t in raw.split(",") if t.strip()}
    return set()


def partition_by_scope(
    items: List[Dict[str, Any]], scope_tags: Set[str]
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Split items into (scoped, global) based on tag overlap."""
    scoped = []
    unscoped = []
    for item in items:
        if scope_tags & tags_for_item(item):
            scoped.append(item)
        else:
            unscoped.append(item)
    return scoped, unscoped


def render_item(item: Dict[str, Any]) -> str:
    """Format one finding as a Markdown bullet."""
    vid = item.get("id", "?")
    # Pick the best display field
    label = item.get("statement") or item.get("question") or item.get("term") or vid
    reason = item.get("reason", "")
    suffix = f" — {reason}" if reason else ""
    return f"- **{vid}**: {label}{suffix}"


def run_gate(scope_tags: Set[str]) -> int:
    """Run the Research Gate and return exit code."""
    if not Path(DB_PATH).exists():
        print(f"ERROR: Knowledge base not found: {DB_PATH}")
        return 2

    try:
        kb = QBPKnowledgeSQLite(DB_PATH, read_only=True)
    except Exception as exc:
        print(f"ERROR: Cannot open knowledge base: {exc}")
        return 2

    weak = kb.find_weak_claims()
    gaps = kb.find_research_gaps()
    unproven = kb.find_unproven_claims()

    has_scope = bool(scope_tags)

    if has_scope:
        scoped_weak, global_weak = partition_by_scope(weak, scope_tags)
        scoped_gaps, global_gaps = partition_by_scope(gaps, scope_tags)
        scoped_unproven, global_unproven = partition_by_scope(unproven, scope_tags)

        # Warn if nothing in KG matches the requested scope tags
        all_scoped = scoped_weak + scoped_gaps + scoped_unproven
        if not all_scoped and (weak or gaps or unproven):
            # Check whether *any* vertex carries the scope tags
            matched = False
            for tag in scope_tags:
                if kb.query_vertices(tag=tag):
                    matched = True
                    break
            if not matched:
                print(
                    f"WARNING: No KG vertices match scope tags "
                    f"{sorted(scope_tags)}.  The knowledge graph may "
                    f"need tagging for these scopes.\n"
                )
    else:
        scoped_weak = scoped_gaps = scoped_unproven = []
        global_weak = weak
        global_gaps = gaps
        global_unproven = unproven

    blocking = bool(scoped_weak or scoped_gaps)
    verdict = "BLOCK" if blocking else "PASS"

    # ── Render report ────────────────────────────────────────────────
    lines = ["# Research Gate Report", ""]

    if has_scope:
        lines.append(f"**Scope tags:** {', '.join(sorted(scope_tags))}")
    else:
        lines.append("**Scope:** global (no --scope provided)")
    lines.append(f"**Verdict:** {verdict}")
    lines.append("")

    if has_scope:
        lines.append("## Scoped Findings (blocking)")
        lines.append("")

        lines.append("### Weak Claims (no evidence chain)")
        if scoped_weak:
            lines.extend(render_item(i) for i in scoped_weak)
        else:
            lines.append("None.")
        lines.append("")

        lines.append("### Research Gaps (open questions, no investigation)")
        if scoped_gaps:
            lines.extend(render_item(i) for i in scoped_gaps)
        else:
            lines.append("None.")
        lines.append("")

        lines.append("### Unproven Claims (informational — proofs come in Phase 4)")
        if scoped_unproven:
            lines.extend(render_item(i) for i in scoped_unproven)
        else:
            lines.append("None.")
        lines.append("")

    lines.append("## Global Findings (informational)")
    lines.append("")

    lines.append("### Weak Claims")
    if global_weak:
        lines.extend(render_item(i) for i in global_weak)
    else:
        lines.append("None.")
    lines.append("")

    lines.append("### Research Gaps")
    if global_gaps:
        lines.extend(render_item(i) for i in global_gaps)
    else:
        lines.append("None.")
    lines.append("")

    lines.append("### Unproven Claims")
    if global_unproven:
        lines.extend(render_item(i) for i in global_unproven)
    else:
        lines.append("None.")
    lines.append("")

    print("\n".join(lines))
    return 1 if blocking else 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Research Gate — hybrid checkpoint between sprints"
    )
    parser.add_argument(
        "--scope",
        nargs="*",
        default=[],
        help="Scope tags to filter findings (e.g. sprint-4 experiment-04)",
    )
    args = parser.parse_args()

    scope_tags = {t.lower() for t in args.scope}
    return run_gate(scope_tags)


if __name__ == "__main__":
    sys.exit(main())
