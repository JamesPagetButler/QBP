#!/usr/bin/env python3
"""Parse a PR body for merge-blocking sign-off boxes (#507 §4/§7, github-best-practices §2.2).

Contract (inter `github-best-practices.md` §2.2, adopted by the QBP notifier):
a reader-list splits sign-off-required from informational boxes.  A task-list box is
MERGE-BLOCKING when it sits in a *merge-blocking region*, which starts at either

  * a LABEL line that starts with "sign-off required" or "merge-blocking" after any
    heading/emphasis/blockquote marks (e.g. "Sign-off required (merge-blocking):",
    "## Sign-off required (merge-blocking)", "**Merge-blocking:**"), or
  * an HTML sentinel `<!-- merge-blocking -->`,

and ends at the next markdown heading that is not itself such a label, a label
line starting with "informational" or "non-blocking", a `<!-- /merge-blocking -->`
/ `<!-- informational -->` sentinel, or a blank line followed by a non-list line.
Everything outside such a region is informational and never counted.  A prose
sentence that merely mentions the words ("this is not merge-blocking") opens
nothing.

Box states: `- [x]` / `- [X]` ticked; `- [ ]` unticked.  An unticked box that
carries the nil mark `⊘`, or whose WHOLE text is struck through (`~~…~~`), is a
deliberately nil'd option (QBP convention `- [ ] ~~option~~ ⊘ reason`), not undone
work, and is NOT counted as unticked.  A struck fragment inside a live ask stays
unticked.

This module is the ONE parser shared by (a) the notifier's nudge state and
(b) the future required check (PR B, gated on the §7 beekeeper ruling).  It
never edits anything.  Auto-nudge, never auto-tick.

CLI: pr_merge_blocking_boxes.py [--body-file F | reads stdin] [--json]
Prints `unticked=<n> ticked=<n>` (or JSON) and exits 0 always; the CALLER
decides whether unticked > 0 is a nudge or a failure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys

BOX_RE = re.compile(r"^\s*[-*+]\s+\[(?P<mark>[ xX])\]\s*(?P<text>.*)$")
HEADING_RE = re.compile(r"^\s{0,3}#{1,6}\s")
OPEN_SENTINEL = re.compile(r"<!--\s*merge-blocking\s*-->", re.I)
CLOSE_SENTINEL = re.compile(r"<!--\s*(/merge-blocking|informational)\s*-->", re.I)
# Word openers/closers are LABEL LINES: after stripping markdown emphasis, heading
# marks and blockquote marks, the line must START with the phrase (G2: a prose
# sentence such as "This is not merge-blocking." never opens a region). The HTML
# sentinel form is preferred and is unambiguous.
_LABEL_PREFIX = r"^[\s#>*_`]*"
OPEN_WORDS = re.compile(
    _LABEL_PREFIX + r"(sign[- ]?off\s+required|merge-blocking)\b", re.I
)
CLOSE_WORDS = re.compile(_LABEL_PREFIX + r"(informational|non-blocking)\b", re.I)
# A box is NIL (a deliberately unselected option, not undone work) when it carries
# the nil mark ⊘, or when its WHOLE text is struck through. A struck fragment inside
# a live ask ("@a — ~~old~~ still owed") stays unticked (G3).
NIL_RE = re.compile(r"⊘|^~~[^~]*~~\s*$")
FENCE_RE = re.compile(r"^\s*(```|~~~)")


def _is_nil(text: str) -> bool:
    return bool(NIL_RE.search(text))


def parse(body: str):
    """Return dict(ticked=[...], unticked=[...], nil=[...]) of merge-blocking box texts."""
    ticked: list[str] = []
    unticked: list[str] = []
    nil: list[str] = []
    in_region = False
    in_fence = False
    prev_blank = False
    for raw in body.splitlines():
        line = raw.rstrip("\n")
        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        stripped = line.strip()
        if HEADING_RE.match(line):
            # A heading ends the previous region; a heading that IS the §2.2 label
            # ("## Sign-off required (merge-blocking)") opens a new one (G1).
            in_region = bool(OPEN_WORDS.search(line)) and not CLOSE_WORDS.search(line)
            prev_blank = False
            continue
        if CLOSE_SENTINEL.search(line):
            in_region = False
            prev_blank = False
            continue
        if OPEN_SENTINEL.search(line):
            in_region = True
            prev_blank = False
            continue
        m = BOX_RE.match(line)
        if m is None:
            # a region opener / closer in prose (not itself a box line)
            if OPEN_WORDS.search(line):
                in_region = True
            elif CLOSE_WORDS.search(line):
                in_region = False
            elif in_region and prev_blank and stripped:
                # blank line followed by a non-list, non-opener line ends the region
                in_region = False
            prev_blank = not stripped
            continue
        prev_blank = False
        if not in_region:
            continue
        text = m.group("text").strip()
        if m.group("mark").lower() == "x":
            ticked.append(text)
        elif _is_nil(text):
            nil.append(text)
        else:
            unticked.append(text)
    return {"ticked": ticked, "unticked": unticked, "nil": nil}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--body-file", help="PR body file (default: stdin)")
    ap.add_argument(
        "--json", action="store_true", help="emit JSON instead of key=value"
    )
    args = ap.parse_args(argv)
    if args.body_file:
        with open(args.body_file, encoding="utf-8") as fh:
            body = fh.read()
    else:
        body = sys.stdin.read()
    res = parse(body)
    if args.json:
        print(json.dumps(res, ensure_ascii=False))
    else:
        print(
            f"unticked={len(res['unticked'])} ticked={len(res['ticked'])} nil={len(res['nil'])}"
        )
        for t in res["unticked"]:
            print(f"UNTICKED: {t}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
