#!/usr/bin/env python3
"""Derive the CTH ledger's current version — QBP#817 variant A.

The ledger file's own `version` key is frozen (scripts/cth_ledger_edit.py). The
*reporting* version a human or another script actually wants ("what version is
the ledger at") is computed, never stored: the frozen base, bumped once per
merged fragment, in the order those fragments actually landed on master — which
scripts/generate_ledger_changelog_view.py's acceptance check reads directly
(two merges -> 6.25.0, 6.26.0, in merge order, per the beekeeper's ruling).

Merge order comes from git history, not from any field inside a fragment: each
fragment's "position" is the position of the commit that first added it, on
**master's first-parent chain** (qbp-oppenheimer, D2, QBP#817 PR-1 review,
2026-11-17, reproduced in a throwaway repo): a plain `git log --reverse`
walk orders by each fragment-adding commit's own date, which for a true merge
commit is NOT the order the fragments actually landed on master — a branch
merged first can still show a later-dated commit than a branch merged second,
if the second branch's commits were authored earlier and sat unmerged longer.
That would renumber a version already issued the moment a second, earlier-
dated branch merges, which breaks "a derived version never moves" the same
way the original bookkeeping collision did. `git log --first-parent -m`
instead walks the sequence of commits actually reachable by always following
a merge's first parent — i.e., the order things actually appeared on master,
attributing a merge's own introduced files to the merge commit itself, not to
whichever original commit on the merged-in branch first wrote them. A
fragment never claims its own ordinal either way — that would just
reintroduce the collision this design removes (two fragments both claiming
"I am 6.25.0").

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


def _refuse_if_shallow(repo_root: Path) -> None:
    """F1 (qbp-architecture, QBP#817 PR-1 review, 2026-11-17): a shallow clone
    (`git fetch --depth=N`) degrades `git log --first-parent -m` silently —
    the graft root reports every file as freshly "A"dded, so every fragment
    gets the SAME (tip) commit and time, and ties fall back to filename
    order, not true merge order. `fragment_versions()`'s own `LedgerVersionError`
    for "not on this branch's history" never fires in exactly this case,
    because every fragment DOES show up — just all attributed to one wrong
    commit. Check directly instead of hoping the symptom surfaces."""
    is_shallow = subprocess.run(
        ["git", "rev-parse", "--is-shallow-repository"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    if is_shallow == "true":
        raise LedgerVersionError(
            f"{repo_root} is a shallow git clone — merge order from "
            f"'git log --first-parent -m' is unreliable here (every fragment "
            f"collapses onto the graft root's commit/time, breaking order). "
            f"Fetch full history first (git fetch --unshallow, or checkout "
            f"with fetch-depth: 0 in CI)."
        )


def _fragment_merge_order(changes_dir: Path, repo_root: Path) -> dict:
    """{relative posix path: (commit sha, commit ISO time, position)} for every
    fragment ever ADDED to **master's first-parent history**, in true merge
    order (D2, QBP#817 PR-1 review) — oldest first. `--first-parent -m` walks
    only the commits actually reachable by always following a merge's first
    parent (the sequence things actually appeared on master), and `-m` makes a
    merge commit show the files it introduced relative to that first parent —
    so a fragment is attributed to the merge commit that brought it onto
    master, never to whichever original commit on the merged-in branch first
    wrote it. `position` is this function's own encounter order, which IS
    final merge order — callers must not re-derive order from timestamps."""
    _refuse_if_shallow(repo_root)
    try:
        rel = changes_dir.relative_to(repo_root).as_posix()
    except ValueError:
        rel = str(changes_dir)
    out = subprocess.run(
        [
            "git",
            "log",
            "--first-parent",
            "-m",
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
    position = 0
    for line in out.splitlines():
        if line.startswith("COMMIT:"):
            _, commit_sha, commit_time = line.split(":", 2)
            continue
        if line.startswith("A\t"):
            path = line[2:]
            if path not in order:  # first-added commit wins (should be the only one)
                order[path] = (commit_sha, commit_time, position)
                position += 1
    return order


def fragment_versions(
    ledger_path: Path = LEDGER,
    changes_dir: Path = CHANGES_DIR,
    repo_root: Path = REPO_ROOT,
) -> list:
    """[{path, data, derived_version, merge_commit, merge_time}, ...] in true
    first-parent merge order (D2) — oldest fragment first, so the list's last
    entry is the current state."""
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
                f"{path} has no 'git log --first-parent -m --diff-filter=A' commit "
                f"on this branch's history — run from a checkout with full history, "
                f"not a shallow clone"
            )
        commit_sha, commit_time, position = merge_order[rel]
        rows.append(
            {
                "path": path,
                "data": data,
                "merge_commit": commit_sha,
                "merge_time": commit_time,
                "_position": position,
            }
        )
    # _fragment_merge_order's own encounter order IS correct first-parent merge
    # order (D2) — no second, separately-ordered git log call needed.
    rows.sort(key=lambda r: r["_position"])
    for i, row in enumerate(rows, start=1):
        row["derived_version"] = bump_minor(base, i)
        del row["_position"]
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
