#!/usr/bin/env python3
"""Pending-upgrade guard.

Reads docs/foundations/pending-upgrades.md, finds every register row tagged
`status: pending` with an `issue: #N`, and queries that issue's state via `gh`.
FAILS (exit 1) if any pending row's unblocking issue is CLOSED — the owed
upgrade must be applied and the row marked `resolved` before the build is green.

This converts "met-pending" rulings from memory-dependent promises into a
mechanical merge-gate: a closed unblocking issue with an un-resolved row cannot
ship (PATTERN-01 — only an un-mergeable state holds).

Skips gracefully (exit 0, loud note) if `gh` is unavailable / unauthenticated,
so it never blocks a local commit on missing credentials — CI is the
authoritative run (same posture as the differential guard, #504).
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

REGISTER = (
    Path(__file__).resolve().parent.parent
    / "docs"
    / "foundations"
    / "pending-upgrades.md"
)
# a register row: ... | issue: #123 | status: pending |
ROW_RE = re.compile(r"issue:\s*#(\d+)\s*\|\s*status:\s*(pending|resolved)", re.I)


def gh_issue_state(num: str) -> str | None:
    """OPEN / CLOSED, or None if gh can't answer."""
    try:
        out = subprocess.run(
            ["gh", "issue", "view", num, "--json", "state", "--jq", ".state"],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip().upper() or None


def main() -> int:
    if not REGISTER.is_file():
        print("no pending-upgrades register — nothing to guard")
        return 0
    rows = ROW_RE.findall(REGISTER.read_text(encoding="utf-8"))
    pending = [num for num, status in rows if status.lower() == "pending"]
    if not pending:
        print("pending-upgrade guard: no pending rows")
        return 0
    if shutil.which("gh") is None:
        print("pending-upgrade guard SKIPPED — gh unavailable; CI is authoritative")
        return 0

    violations: list[str] = []
    for num in pending:
        state = gh_issue_state(num)
        if state is None:
            print(
                f"  #{num}: state UNKNOWN (gh could not resolve) — not failing on this"
            )
            continue
        if state == "CLOSED":
            violations.append(
                f"#{num} is CLOSED but its register row is still `status: pending` — "
                f"apply the owed upgrade and mark the row `resolved`"
            )
        else:
            print(f"  #{num}: OPEN — pending row correctly held")

    if violations:
        print("PENDING-UPGRADE VIOLATIONS:")
        for v in violations:
            print(f"  - {v}")
        return 1
    print("pending-upgrade guard: all pending rows have OPEN unblocking issues")
    return 0


if __name__ == "__main__":
    sys.exit(main())
