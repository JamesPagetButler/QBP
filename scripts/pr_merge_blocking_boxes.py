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

The notifier-owned CI-green EVIDENCE box (#538, #507 §8a, #815) is its own class:
`evidence`.  It is the box `set_ci_box` in `.github/workflows/pr-check-status.yml`
ticks/unticks — the FIRST line of the body that is a `- [ ]`/`- [x]` box whose
lowercased text contains "ci green" and none of review / sign-off / visual / hvr /
red team / gemini / approve (`is_ci_green_evidence_box`, kept in sync with that awk).
Inside a merge-blocking region it is counted as neither ticked nor unticked: its
truth is the CI state, which the required checks already enforce, and counting it
would deadlock (`Merge-blocking boxes` red on the box ↔ the notifier ticking it only
once that check is green — PR #814).  A second "CI green" box the notifier does not
own stays a normal box.

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
Prints `unticked=<n> ticked=<n> nil=<n> region=present|absent evidence=<n>` (or
JSON, which adds an `evidence` list) and
exits 0 always; the first-line prefix `unticked=<int> …` is the stable contract
for callers (the notifier reads it with `sed`; `evidence=` is appended AFTER
`region=` so `s/^unticked=.*region=\([a-z]*\).*/` still extracts the region), and the CALLER decides whether
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
# Inline code spans are literal text, like fenced blocks: a prose mention of the
# sentinel (`<!-- merge-blocking -->` in backticks, e.g. a PR that documents this
# parser) must not open a region — otherwise region=present is reported for a
# body that has no real §2.2 region, defeating the fail-closed verdict.
CODE_SPAN_RE = re.compile(r"`[^`\n]*`")
# The notifier's set_ci_box (pr-check-status.yml) awk predicate, byte-for-byte in
# intent: box regex `^[[:space:]]*-[[:space:]]\[[ xX]\]`, then on the lowercased
# WHOLE line `ci green` and NOT `review|sign.?off|visual|hvr|red team|gemini|approve`.
# The awk scans every line (fences included) and owns only the FIRST match.
_CI_BOX_RE = re.compile(r"^\s*-\s\[[ xX]\]")
_CI_EXCLUDE_RE = re.compile(r"review|sign.?off|visual|hvr|red team|gemini|approve")


def _is_nil(text: str) -> bool:
    return bool(NIL_RE.search(text))


def is_ci_green_evidence_box(line: str) -> bool:
    """True iff `line` matches set_ci_box's awk predicate in pr-check-status.yml.

    KEEP IN SYNC with `set_ci_box()` in .github/workflows/pr-check-status.yml
    (#815): change one, change the other.
    """
    low = line.lower()
    return bool(
        _CI_BOX_RE.match(line) and "ci green" in low and not _CI_EXCLUDE_RE.search(low)
    )


def _ci_box_index(lines: list[str]):
    """Index of the box set_ci_box owns (its FIRST match, fences included), or None."""
    for i, line in enumerate(lines):
        if is_ci_green_evidence_box(line):
            return i
    return None


def parse(body: str):
    """Return dict(ticked=[...], unticked=[...], nil=[...], evidence=[...],
    region="present"|"absent").

    `evidence` lists the notifier-owned CI-green box when it sits in a region
    (ticked or not); it is never in `ticked` / `unticked`.

    `region` is "present" as soon as any §2.2 opener (label line, heading-form
    label or `<!-- merge-blocking -->` sentinel) is seen, even if the region
    holds no boxes; "absent" means the body uses neither form (fail-closed:
    the caller must not treat unticked=0 as assessed).
    """
    ticked: list[str] = []
    unticked: list[str] = []
    nil: list[str] = []
    evidence: list[str] = []
    lines = body.splitlines()
    ci_idx = _ci_box_index(lines)
    in_region = False
    region_seen = False
    in_fence = False
    prev_blank = False
    for idx, raw in enumerate(lines):
        line = raw.rstrip("\n")
        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        stripped = line.strip()
        # sentinel checks run on the line with inline code spans removed
        nospan = CODE_SPAN_RE.sub("", line)
        if HEADING_RE.match(line):
            # A heading ends the previous region; a heading that IS the §2.2 label
            # ("## Sign-off required (merge-blocking)") opens a new one (G1).
            in_region = bool(OPEN_WORDS.search(line)) and not CLOSE_WORDS.search(line)
            region_seen = region_seen or in_region
            prev_blank = False
            continue
        if CLOSE_SENTINEL.search(nospan):
            in_region = False
            prev_blank = False
            continue
        if OPEN_SENTINEL.search(nospan):
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
        if idx == ci_idx:
            evidence.append(text)
        elif m.group("mark").lower() == "x":
            ticked.append(text)
        elif _is_nil(text):
            nil.append(text)
        else:
            unticked.append(text)
    return {
        "ticked": ticked,
        "unticked": unticked,
        "nil": nil,
        "evidence": evidence,
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
            f"nil={len(res['nil'])} region={res['region']} "
            f"evidence={len(res['evidence'])}"
        )
        for t in res["unticked"]:
            print(f"UNTICKED: {t}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
