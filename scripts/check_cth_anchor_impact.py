#!/usr/bin/env python3
"""
CTH Anchor Impact Lint — PR template enforcement.

Layer 2 of the CTH tracking discipline. Detects when a PR touches
anchor-bearing paths (paper/, proofs/, analysis/, archive/) without
declaring a CTH anchor impact in the PR body.

Used by .github/workflows/cth-anchor-impact.yml on every PR that
touches relevant paths.

Logic:
- If any file under paper/, proofs/, analysis/, or archive/ changes
  AND the PR body doesn't contain a "## CTH anchor impact" section
  with at least one of the routing-axis checkboxes marked
  → fail with a helpful message
- If the touched files are docs-only (README.md, *.md cross-refs that
  don't change anchors) and the PR is Tier 1, allow N/A declaration
- Adds an informational comment summarizing detected anchor changes
  in archive/cth-inventory/*.json files (computed via JSON diff)

Authors: qbp-implementor (2026-05-15)
Reference: docs/workflows/review_anchoring.md (PR #413),
          docs/workflows/pr7_conflict_routing_rubric.md v0.2 (PR #423)
"""

from __future__ import annotations
import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

SUBSTANTIVE_PATTERNS = (
    "paper/",
    "proofs/",
    "analysis/",
    "archive/",
)

CTH_INVENTORY_PATTERNS = ("archive/cth-inventory/",)


def is_substantive_path(path: str) -> bool:
    return any(path.startswith(p) for p in SUBSTANTIVE_PATTERNS)


def is_cth_inventory_path(path: str) -> bool:
    return any(path.startswith(p) for p in CTH_INVENTORY_PATTERNS)


def parse_changed_files(diff_files_path: str) -> list[str]:
    """Read a newline-delimited list of changed file paths."""
    with open(diff_files_path) as f:
        return [line.strip() for line in f if line.strip()]


def has_anchor_impact_section(pr_body: str) -> bool:
    """Detect the CTH anchor impact section in PR body."""
    return bool(
        re.search(r"^##\s+CTH anchor impact", pr_body, re.MULTILINE | re.IGNORECASE)
    )


def has_routing_axis_declaration(pr_body: str) -> bool:
    """At least one routing-axis checkbox must be marked."""
    patterns = [
        r"\[x\]\s+theory-axis",
        r"\[x\]\s+schema-axis",
        r"\[x\]\s+two-axis",
        r"\[x\]\s+not-conflict",
        r"\[x\]\s+N/A",
        r"\[x\]\s+no anchor impact",
    ]
    return any(re.search(p, pr_body, re.IGNORECASE) for p in patterns)


def detect_inventory_changes(
    changed_files: list[str], base_ref: str, head_ref: str
) -> dict[str, list[str]]:
    """
    For each changed inventory file, compute anchor-level diff.
    Returns {filename: ["added: ID", "removed: ID", "modified: ID"]}.
    Uses `git show` to read both sides; uses anchor "id" field.
    """
    import subprocess

    summary: dict[str, list[str]] = {}
    for path in changed_files:
        if not is_cth_inventory_path(path):
            continue
        if not path.endswith(".json"):
            continue
        try:
            base = subprocess.run(
                ["git", "show", f"{base_ref}:{path}"],
                capture_output=True,
                text=True,
                check=False,
            )
            head = subprocess.run(
                ["git", "show", f"{head_ref}:{path}"],
                capture_output=True,
                text=True,
                check=False,
            )
            base_inv = (
                json.loads(base.stdout) if base.returncode == 0 else {"anchors": []}
            )
            head_inv = (
                json.loads(head.stdout) if head.returncode == 0 else {"anchors": []}
            )
            base_idx = {a.get("id"): a for a in base_inv.get("anchors", [])}
            head_idx = {a.get("id"): a for a in head_inv.get("anchors", [])}
            added = sorted(set(head_idx) - set(base_idx))
            removed = sorted(set(base_idx) - set(head_idx))
            modified = sorted(
                aid
                for aid in set(base_idx) & set(head_idx)
                if base_idx[aid] != head_idx[aid]
            )
            entries: list[str] = []
            for aid in added:
                entries.append(f"added: `{aid}`")
            for aid in removed:
                entries.append(f"removed: `{aid}`")
            for aid in modified:
                entries.append(f"modified: `{aid}`")
            if entries:
                summary[path] = entries
        except Exception as e:
            summary[path] = [f"diff failed: {e}"]
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--changed-files",
        required=True,
        help="Path to newline-delimited list of changed files",
    )
    parser.add_argument(
        "--pr-body-file",
        required=True,
        help="Path to file containing PR body markdown",
    )
    parser.add_argument(
        "--base-ref",
        default="origin/master",
        help="Git ref for base (for inventory diff)",
    )
    parser.add_argument(
        "--head-ref",
        default="HEAD",
        help="Git ref for head (for inventory diff)",
    )
    parser.add_argument(
        "--summary-out",
        default="/tmp/cth_anchor_summary.md",
        help="Where to write the informational summary",
    )
    args = parser.parse_args()

    changed = parse_changed_files(args.changed_files)
    pr_body = Path(args.pr_body_file).read_text()

    substantive_changes = [p for p in changed if is_substantive_path(p)]
    inventory_changes = [p for p in changed if is_cth_inventory_path(p)]

    summary_lines: list[str] = ["## CTH Anchor Impact Lint"]
    summary_lines.append("")

    if not substantive_changes:
        summary_lines.append(
            "🟢 **No anchor-bearing paths touched** (`paper/`, `proofs/`, `analysis/`, `archive/`)."
            " CTH anchor impact declaration not required."
        )
        Path(args.summary_out).write_text("\n".join(summary_lines))
        return 0

    summary_lines.append(
        f"This PR touches {len(substantive_changes)} anchor-bearing path(s):"
    )
    for p in substantive_changes[:10]:
        summary_lines.append(f"- `{p}`")
    if len(substantive_changes) > 10:
        summary_lines.append(f"- ... and {len(substantive_changes) - 10} more")
    summary_lines.append("")

    # Inventory diff details
    if inventory_changes:
        summary_lines.append("### Inventory diff details")
        summary_lines.append("")
        diff = detect_inventory_changes(changed, args.base_ref, args.head_ref)
        if diff:
            for path, entries in diff.items():
                summary_lines.append(f"**`{path}`:**")
                for e in entries:
                    summary_lines.append(f"  - {e}")
                summary_lines.append("")
        else:
            summary_lines.append("_(no parseable JSON changes detected)_")
            summary_lines.append("")

    # Enforcement
    has_section = has_anchor_impact_section(pr_body)
    has_routing = has_routing_axis_declaration(pr_body)

    if not has_section:
        summary_lines.append(
            "🔴 **BLOCKING:** PR body is missing the `## CTH anchor impact` section."
        )
        summary_lines.append(
            "Add the section per `docs/workflows/review_anchoring.md` "
            "(use the Tier-2 or Tier-3 PR template)."
        )
        Path(args.summary_out).write_text("\n".join(summary_lines))
        return 1

    if not has_routing:
        summary_lines.append(
            "🔴 **BLOCKING:** `## CTH anchor impact` section is present but no routing-axis "
            "checkbox is marked. Mark one of: theory-axis / schema-axis / two-axis / not-conflict / N/A."
        )
        Path(args.summary_out).write_text("\n".join(summary_lines))
        return 1

    summary_lines.append("🟢 **PASS:** CTH anchor impact declared with routing axis.")
    Path(args.summary_out).write_text("\n".join(summary_lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
