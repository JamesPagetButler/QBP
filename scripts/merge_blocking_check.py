#!/usr/bin/env python3
"""Required status check: fail when a merge-blocking sign-off box is unticked (#507 §7).

Consumer 2 of the §2.2 box parser (`scripts/pr_merge_blocking_boxes.py`, the ONE
parser shared with the notifier's nudge — consumer 1).  Wired as the GitHub
check `Merge-blocking boxes` (`.github/workflows/merge-blocking-boxes.yml`); the
beekeeper adds that name to the master ruleset's required checks, after which
an unticked merge-blocking box disables the merge button — for everyone,
including the beekeeper (ruling on #507, 2026-10-27).  Auto-nudge, never
auto-tick: this script reads the body and exits; the hand that owns a box still
ticks it (or ⊘-nils it with a reason).

Exit codes (the contract the workflow relies on):
  0  no unticked merge-blocking box: all ticked and/or ⊘-nil'd, OR no §2.2
     region in the body (not assessable — `::warning::`, see below)
  1  `region=present` and `unticked > 0`  → red check, each box named
  1  `region=absent` and `--absent-blocks` → red check (the beekeeper's flip)
  2  usage error (unreadable body file)

No-region policy (PR B, beekeeper-confirmable): a body that uses neither §2.2
form is NOT blocked here — the notifier already withholds ✅ for it (🟡 "not
assessable", fail-closed R3) and the PR templates do not yet carry the region
everywhere.  The check passes with a `::warning::` that names the fix.  To make
absence blocking later, pass `--absent-blocks` in the workflow step (one line).

Usage: merge_blocking_check.py [--body-file F | reads stdin] [--absent-blocks]
"""

from __future__ import annotations

import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pr_merge_blocking_boxes import parse  # noqa: E402

DOC_URL = (
    "https://github.com/JamesPagetButler/inter/blob/main/github-best-practices.md"
    "#22-body"
)
LOCAL_DOC = "docs/workflows/review_tiers.md (Evidence-first discipline, item 8)"
FIX_HINT = (
    "tick the box, or ⊘-nil it with a reason (`- [ ] ~~option~~ ⊘ reason`) — "
    "the hand that owns the box ticks it; nothing auto-ticks"
)
ABSENT_FIX = (
    "add a `Sign-off required (merge-blocking):` list (or the "
    "`<!-- merge-blocking -->` sentinel) to the PR body per github-best-practices "
    "§2.2 so the sign-off state is assessable; the notifier shows 🟡 not-assessable "
    "until then"
)


def _annot(level: str, msg: str) -> None:
    # GitHub workflow command; one line (newlines would end the command)
    print(f"::{level}::{msg}".replace("\n", " "))


def check(body: str, absent_blocks: bool = False) -> int:
    """Return the exit code for `body` and print the actionable report."""
    res = parse(body)
    n_un, n_t, n_nil = len(res["unticked"]), len(res["ticked"]), len(res["nil"])
    print(f"unticked={n_un} ticked={n_t} nil={n_nil} region={res['region']}")
    if res["region"] == "absent":
        msg = f"Merge-blocking boxes: no §2.2 region in the PR body — {ABSENT_FIX}."
        if absent_blocks:
            _annot("error", msg + f" (absence is BLOCKING here) See {DOC_URL}")
            return 1
        _annot("warning", msg + f" (not blocking in this configuration) See {DOC_URL}")
        return 0
    if n_un > 0:
        print(
            f"\nFAIL — {n_un} merge-blocking sign-off box(es) unticked "
            f"(github-best-practices §2.2 region present):"
        )
        for t in res["unticked"]:
            print(f"  - [ ] {t}")
            _annot("error", f"unticked merge-blocking box: {t} — {FIX_HINT}")
        print(f"\nFix: {FIX_HINT}.")
        print(f"Contract: {DOC_URL}  ·  {LOCAL_DOC}")
        print("Edit the PR body; this check re-runs on `pull_request: edited`.")
        return 1
    _annot(
        "notice",
        f"Merge-blocking boxes: all clear ({n_t} ticked, {n_nil} ⊘-nil'd, "
        f"0 unticked in the §2.2 region).",
    )
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--body-file", help="PR body file (default: stdin)")
    ap.add_argument(
        "--absent-blocks",
        action="store_true",
        help="also fail when the body has no §2.2 region (beekeeper's flip)",
    )
    args = ap.parse_args(argv)
    try:
        if args.body_file:
            with open(args.body_file, encoding="utf-8") as fh:
                body = fh.read()
        else:
            body = sys.stdin.read()
    except OSError as e:
        _annot("error", f"Merge-blocking boxes: cannot read PR body: {e}")
        return 2
    return check(body, absent_blocks=args.absent_blocks)


if __name__ == "__main__":
    sys.exit(main())
