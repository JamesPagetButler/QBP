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

Region presence (fail-closed, federation rule R3 — qbp-architecture §I4 on PR
#731): the result also says whether ANY §2.2 region opener (label line, heading
form or sentinel) was seen at all.  `region=present` means the sign-off state
was assessable; `region=absent` means the body uses neither form and the caller
must NOT read `unticked=0` as "nothing owed" — reviewer boxes in some other
shape (e.g. `- [ ] **§I4 @seat** (sign-off required)`) are not counted and the
notifier reports "sign-off state not assessable" instead of ALL GREEN.

CLI: pr_merge_blocking_boxes.py [--body-file F | reads stdin] [--json]
Prints `unticked=<n> ticked=<n> nil=<n> region=present|absent` (or JSON) and
exits 0 always; the first-line prefix `unticked=<int> …` is the stable contract
for callers (the notifier reads it with `sed`), and the CALLER decides whether
unticked > 0 / region=absent is a nudge or a failure.
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
    """Return dict(ticked=[...], unticked=[...], nil=[...], region="present"|"absent").

    `region` is "present" as soon as any §2.2 opener (label line, heading-form
    label or `<!-- merge-blocking -->` sentinel) is seen, even if the region
    holds no boxes; "absent" means the body uses neither form (fail-closed:
    the caller must not treat unticked=0 as assessed).
    """
    ticked: list[str] = []
    unticked: list[str] = []
    nil: list[str] = []
    in_region = False
    region_seen = False
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
            region_seen = region_seen or in_region
            prev_blank = False
            continue
        if CLOSE_SENTINEL.search(line):
            in_region = False
            prev_blank = False
            continue
        if OPEN_SENTINEL.search(line):
            in_region = True
            region_seen = True
            prev_blank = False
            continue
        m = BOX_RE.match(line)
        if m is None:
            # a region opener / closer in prose (not itself a box line)
            if OPEN_WORDS.search(line):
                in_region = True
                region_seen = True
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
    return {
        "ticked": ticked,
        "unticked": unticked,
        "nil": nil,
        "region": "present" if region_seen else "absent",
    }


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
            f"unticked={len(res['unticked'])} ticked={len(res['ticked'])} "
            f"nil={len(res['nil'])} region={res['region']}"
        )
        for t in res["unticked"]:
            print(f"UNTICKED: {t}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
