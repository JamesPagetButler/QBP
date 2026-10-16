#!/usr/bin/env python3
"""QBP#706 — derive the pr-check-status notifier's review checklist from the SAME detected
review artifacts the Tier-3 gate uses, so the machine comment can never contradict the
record (the beekeeper read PR #705's hardcoded-unticked boxes as open work although every
leg was ticked with evidence in the PR body: "I do not want to be misinformed").

Reuses `check_tier3_label`'s `REVIEW_VERDICT`, `NOTIFIER_MARKER` and `COMMENT_BOUNDARY`
VERBATIM — that gate is NOT modified (AC3). The only addition is splitting the reviewer
SIGNATURE per reviewer (Red Team vs Gemini), which the single-regex gate does not need. A
row ticks iff ONE non-notifier comment carries that reviewer's signature AND a rendered
verdict in the SAME comment (the gate's co-occurrence rule, anti-rubber-stamp FAULT-S4-003).
A carried review (the re-land case, PR #705) is an ordinary non-notifier comment, so it
counts the same as a fresh one.

Reads --comments-file (the COMMENT_BOUNDARY-joined blob the workflow already builds) and
prints `red_team=0|1` and `gemini=0|1` for the workflow to read.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
# AC3: imported, never modified. One source of the verdict rule + the notifier/boundary
# markers, shared with the Tier-3 gate so the two can never drift.
from check_tier3_label import (  # noqa: E402
    COMMENT_BOUNDARY,
    NOTIFIER_MARKER,
    REVIEW_VERDICT,
)

# The per-reviewer split of the gate's single REVIEW_SIGNATURE (which is the union of these).
RED_TEAM_SIG = re.compile(r"Red Team|Sabine|Grothendieck|Knuth", re.IGNORECASE)
GEMINI_SIG = re.compile(r"Gemini|Furey|Feynman", re.IGNORECASE)


def detect(comments_blob: str) -> tuple[bool, bool]:
    """(red_team, gemini): each True iff some NON-notifier comment carries that reviewer's
    signature AND a rendered verdict together. Notifier-authored comments (which NAME the
    reviewers in their checklist but render no verdict) are skipped, so the notifier can
    never self-tick."""
    red = gem = False
    for block in comments_blob.split(COMMENT_BOUNDARY):
        if NOTIFIER_MARKER in block:
            continue
        if not REVIEW_VERDICT.search(block):
            continue
        if RED_TEAM_SIG.search(block):
            red = True
        if GEMINI_SIG.search(block):
            gem = True
    return red, gem


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--comments-file", required=True)
    args = ap.parse_args(argv)
    try:
        blob = Path(args.comments_file).read_text(encoding="utf-8")
    except FileNotFoundError:
        blob = ""
    red, gem = detect(blob)
    print(f"red_team={int(red)}")
    print(f"gemini={int(gem)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
