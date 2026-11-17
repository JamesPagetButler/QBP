#!/usr/bin/env python3
"""Derive the CTH ledger's current version — QBP#817 variant A.

The ledger file's own `version` key is frozen (scripts/cth_ledger_edit.py). The
*reporting* version a human or another script actually wants ("what version is
the ledger at") is computed, never stored: the frozen base, bumped once per
merged fragment, in the order those fragments actually landed on master — which
scripts/generate_ledger_changelog_view.py's acceptance check reads directly
(two merges -> 6.25.0, 6.26.0, in merge order, per the beekeeper's ruling).

Merge order comes from git history, not from any field inside a fragment: each
fragment's "position" is the position of the commit that first added it, walked
in `git log --reverse` order over the fragments directory. A fragment never
claims its own ordinal — that would just reintroduce the collision this design
removes (two fragments both claiming "I am 6.25.0").

Usage:
    python3 scripts/ledger_version.py                      # current version
    python3 scripts/ledger_version.py --list                # one row per fragment, in order
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

from ledger_fragment import CHANGES_DIR, read_fragments

REPO_ROOT = Path(__file__).resolve().parent.parent
LEDGER = REPO_ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"


class LedgerVersionError(RuntimeError):
    pass


def frozen_base_version(ledger_path: Path = LEDGER) -> str:
    return json.loads(ledger_path.read_text(encoding="utf-8"))["version"]


def bump_minor(version: str, n: int) -> str:
    """ "6.24.0" bumped by 2 -> "6.26.0". n=0 is the base itself, unbumped."""
    major, minor, _patch = version.split(".")
    return f"{major}.{int(minor) + n}.0"


def _fragment_merge_order(changes_dir: Path, repo_root: Path) -> dict:
    """{relative posix path: (commit sha, commit ISO time)} for every fragment
    ever ADDED to the repo, in the commit order git log replays them — oldest
    first. A rebase that replays a fragment-adding commit keeps that commit's
    own authored/committed time, which is what we want here: the time the
    content was actually written, not when some later rebase touched it."""
    try:
        rel = changes_dir.relative_to(repo_root).as_posix()
    except ValueError:
        rel = str(changes_dir)
    out = subprocess.run(
        [
            "git",
            "log",
            "--reverse",
            "--diff-filter=A",
            "--name-status",
            "--format=COMMIT:%H:%cI",
            "--",
            rel,
        ],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    order = {}
    commit_sha = commit_time = None
    for line in out.splitlines():
        if line.startswith("COMMIT:"):
            _, commit_sha, commit_time = line.split(":", 2)
            continue
        if line.startswith("A\t"):
            path = line[2:]
            if path not in order:  # first-added commit wins (should be the only one)
                order[path] = (commit_sha, commit_time)
    return order


def fragment_versions(
    ledger_path: Path = LEDGER,
    changes_dir: Path = CHANGES_DIR,
    repo_root: Path = REPO_ROOT,
) -> list:
    """[{path, data, derived_version, merge_commit, merge_time}, ...] in merge
    order — oldest fragment first, so the list's last entry is the current
    state."""
    base = frozen_base_version(ledger_path)
    fragments = read_fragments(changes_dir)
    merge_order = _fragment_merge_order(changes_dir, repo_root)
    rows = []
    for path, data in fragments:
        try:
            rel = path.relative_to(repo_root).as_posix()
        except ValueError:
            rel = str(path)
        if rel not in merge_order:
            raise LedgerVersionError(
                f"{path} has no 'git log --diff-filter=A' commit on this branch's "
                f"history — run from a checkout with full history, not a shallow clone"
            )
        rows.append(
            {
                "path": path,
                "data": data,
                "merge_commit": merge_order[rel][0],
                "merge_time": merge_order[rel][1],
            }
        )
    # order by the commit's position in overall history, not by filename
    commit_order = subprocess.run(
        ["git", "log", "--reverse", "--format=%H"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    position = {sha: i for i, sha in enumerate(commit_order)}
    rows.sort(key=lambda r: position.get(r["merge_commit"], len(commit_order)))
    for i, row in enumerate(rows, start=1):
        row["derived_version"] = bump_minor(base, i)
    return rows


def current_version(
    ledger_path: Path = LEDGER,
    changes_dir: Path = CHANGES_DIR,
    repo_root: Path = REPO_ROOT,
) -> str:
    rows = fragment_versions(ledger_path, changes_dir, repo_root)
    if not rows:
        return frozen_base_version(ledger_path)
    return rows[-1]["derived_version"]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger", default=str(LEDGER))
    ap.add_argument(
        "--list", action="store_true", help="print one row per fragment, in merge order"
    )
    args = ap.parse_args()
    ledger_path = Path(args.ledger)

    if args.list:
        for row in fragment_versions(ledger_path):
            d = row["data"]
            print(
                f"{row['derived_version']}\t{row['merge_time']}\tissue#{d['issue']}\t"
                f"PR#{d['pr']}\t{d['note'][:60]!r}\t{','.join(d['touched_ids'])}"
            )
    else:
        print(current_version(ledger_path))


if __name__ == "__main__":
    main()
