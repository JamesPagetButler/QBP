#!/usr/bin/env python3
"""
Research Gate — Hybrid checkpoint between sprints.

Queries the Knowledge Graph for weak claims, research gaps, and unproven
claims, then filters by scope tags to decide whether a full Pre-Sprint
Research phase is needed before the next sprint can begin.

Usage:
    python scripts/research_gate.py --scope sprint-4 experiment-04
    python scripts/research_gate.py --scope sprint-4 --exclude claim:my-target-claim
    python scripts/research_gate.py --force --scope sprint-4 experiment-04
    python scripts/research_gate.py              # global-only analysis

Exit codes:
    0 - PASS  (no scoped blocking items, or --force used)
    1 - BLOCK (scoped weak claims or research gaps found)
    2 - Error (database not found, etc.)
"""

import argparse
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

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


def is_excluded(item: Dict[str, Any], exclude_ids: Set[str]) -> bool:
    """Check if an item's ID is in the exclusion set."""
    vid = item.get("id", "")
    return vid in exclude_ids


def run_gate(
    scope_tags: Set[str],
    exclude_ids: Optional[Set[str]] = None,
    force: bool = False,
) -> int:
    """Run the Research Gate and return exit code."""
    if not Path(DB_PATH).exists():
        print(f"ERROR: Knowledge base not found: {DB_PATH}")
        return 2

    try:
        kb = QBPKnowledgeSQLite(DB_PATH, read_only=True)
    except Exception as exc:
        print(f"ERROR: Cannot open knowledge base: {exc}")
        return 2

    exclude_ids = exclude_ids or set()

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

    # Separate excluded items from blocking items
    if exclude_ids and has_scope:
        excluded_weak = [i for i in scoped_weak if is_excluded(i, exclude_ids)]
        scoped_weak = [i for i in scoped_weak if not is_excluded(i, exclude_ids)]
        excluded_gaps = [i for i in scoped_gaps if is_excluded(i, exclude_ids)]
        scoped_gaps = [i for i in scoped_gaps if not is_excluded(i, exclude_ids)]
    else:
        excluded_weak = []
        excluded_gaps = []

    blocking = bool(scoped_weak or scoped_gaps)

    if force and blocking:
        verdict = "FORCED PASS"
        print("WARNING: Gate forced — BLOCK findings ignored.\n")
    elif blocking:
        verdict = "BLOCK"
    else:
        verdict = "PASS"

    # ── Render report ────────────────────────────────────────────────
    lines = ["# Research Gate Report", ""]

    if has_scope:
        lines.append(f"**Scope tags:** {', '.join(sorted(scope_tags))}")
    else:
        lines.append("**Scope:** global (no --scope provided)")
    if exclude_ids:
        lines.append(f"**Excluded:** {', '.join(sorted(exclude_ids))}")
    if force:
        lines.append("**Mode:** --force (blocking findings ignored)")
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

        if excluded_weak or excluded_gaps:
            lines.append("### Excluded (target claims — not blocking)")
            for i in excluded_weak:
                lines.append(f"- **{i.get('id', '?')}**: excluded (weak claim)")
            for i in excluded_gaps:
                lines.append(f"- **{i.get('id', '?')}**: excluded (research gap)")
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
    if force:
        return 0
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
    parser.add_argument(
        "--exclude",
        nargs="*",
        default=[],
        help="Claim/question IDs to exclude from blocking (target claims)",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Force PASS regardless of findings (logs warning)",
    )
    args = parser.parse_args()

    scope_tags = {t.lower() for t in args.scope}
    exclude_ids = set(args.exclude)
    return run_gate(scope_tags, exclude_ids=exclude_ids, force=args.force)


if __name__ == "__main__":
    sys.exit(main())
