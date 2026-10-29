#!/usr/bin/env python3
"""Comment-evidence vs unticked-box detection for the notifier's 🟡 nudge (#507 AC4).

The other half of §4.  PR #731 made the notifier NAME each unticked merge-blocking
sign-off box (github-best-practices §2.2) and ask the owner to cite any posted
APPROVE; it did not detect one (disclosed in PR #731, Red Team S1).  This module
detects one.  For every UNTICKED merge-blocking box it looks through the PR's
issue comments and reviews for a candidate evidence post and, when it finds one,
produces the richer nudge line:

    🟡 box "§I4 @qbp-architecture — contract co-sign" is UNTICKED but an APPROVE was
    posted (<url>, reviewed-sha 486ad51 ≠ head cdda215) — the box owner ticks it or
    re-reviews at head

Rules (all of them load-bearing):

* **Never auto-tick.**  This module edits nothing and returns text; the hand that
  owns a box ticks it.  Auto-nudge, never auto-tick (#507 §4, bma-systema#245).
* **One parser.**  Boxes come from `pr_merge_blocking_boxes.parse` — the ONE §2.2
  parser shared with the required check (`Merge-blocking boxes`) — never a fork.
* **Evidence = APPROVE-class verdict + the box's hand, in one post.**  A verdict
  is `APPROVE` / `APPROVE-WITH-CONCERN` in a comment or review body, or a review
  whose `state` is `APPROVED`.  The hand is the `@handle` in the box line (e.g.
  `§I4 @qbp-architecture`); it matches when it is the post's `author.login`, OR
  when the body names `@handle` **on the same line as the verdict** (federation
  personas post through the beekeeper's account, so author alone is not enough).
  Same-line is a precision rule, not pedantry: on PR #780 the Gemini disposition
  said `VERDICT: APPROVE` and, three lines later, `§I4 @qbp-architecture co-sign
  remains open` — that comment is NOT evidence for the architect's box.
* **The shared login is non-identifying** (`SHARED_LOGINS`).  Every federation
  persona posts through the one GitHub account `JamesPagetButler`, so that login
  says nothing about WHICH hand wrote the post.  The `author.login` match is
  never taken for a shared login — not even for a box whose hand is literally
  `@JamesPagetButler` — so a persona's APPROVE cannot satisfy the beekeeper's box
  (arch §I4 on PR #785, item 1).  For a shared-login post only the same-line
  `@handle` rule applies; a non-shared login (a reviewer with their own account)
  still author-matches its own box anywhere in the post.
* **A verdict word in a request is not a verdict** (arch §I4 on PR #785, item 2).
  A line that carries `APPROVE` but says the box is still owed is skipped.  Three
  negation shapes, scoped so a legitimate verdict line survives:
    - HARD — anywhere on the verdict line: `remains open`, `still open`, `not
      yet`, `left unticked`, `requested`, `outstanding`, `owed`, `awaiting`,
      `ask`/`asks`/`asked`/`asking`, `waiting`, `need`/`needs`/`needed`,
      `require`/`required`, `missing` (word-bounded; Gemini r3 on PR #785, F1:
      "We need an APPROVE", "Waiting for @h to APPROVE", "Required: APPROVE by @h").
    - PRE — only when it PRECEDES the verdict token on the line: `please`, `for
      your` ("@qbp-architecture please APPROVE", "for your APPROVE" are asks;
      "APPROVE — please merge", "APPROVE — for your records" are verdicts).
    - ADJACENT — only when it touches the verdict token or an `@handle` with
      nothing but whitespace/punctuation between: `pending` ("APPROVE pending
      from @qbp-architecture", "pending @qbp-architecture APPROVE" are asks;
      "APPROVE — the pending item is tracked in #781" is a verdict).
* **Boxes without an `@handle`** fall back to the Red Team / Gemini role
  signatures used by the Tier-3 gate (Sabine/Grothendieck/Knuth, Furey/Feynman)
  with the gate's own co-occurrence rule — signature (usually the review's
  header line) and a non-negated verdict line in the SAME post; any other
  handle-less box (Human Visual Review, a bare AC) gets no evidence — the plain
  nudge line stands.
* **The notifier's own comment** (`<!-- pr-check-status-notifier -->`) and
  `github-actions` posts are never evidence.
* **Sha.**  The post's `<!-- reviewed-sha: … -->` marker wins; otherwise a 7–40 hex
  sha after `at` / `@` / `head` in the body — one that carries at least one hex
  LETTER and one DIGIT (`20261028` is a date, `defaced` is a word; neither is a
  commit).  The human line says when the cited sha ≠ the current head (the owner
  re-reviews at head rather than ticking on a stale review), and says so when no
  sha was cited.
* **Quoted text is not the post's own voice.**  Markdown blockquote lines (`> …`,
  what GitHub's "quote reply" produces) are dropped before any rule runs — a reply
  that quotes an earlier `APPROVE` line, a role header or a `reviewed-sha` marker
  is not itself a verdict (Gemini review on PR #785, finding 1).
* **Deterministic.**  When several posts qualify, the cited one is chosen by: the
  hand on the post's LEAD line (`## Red Team — PR #N …`, `**§I4 … @handle:
  APPROVE**` — the federation header convention) over a passing mention; then a
  `<!-- reviewed-sha: … -->` marker (the review-artifact convention) over an
  unmarked summary; then the newest (by timestamp, then url).  The candidate
  count is reported.  Stdlib only.

CLI:
    pr_box_evidence.py --body BODY.md --comments COMMENTS.json --head SHA [--human|--json]

`COMMENTS.json` is the object `gh pr view N --json comments,reviews` prints
(`comments[].author.login/body/createdAt/url`, `reviews[].author.login/state/body/
submittedAt/url`); the paginated REST shapes (`user.login`, `html_url`,
`created_at` / `submitted_at` — what the notifier fetches, so no 100-comment cap)
are read too; a bare list is read as comments.  Default output is one
machine line per unticked box after a summary line
`boxes=<n> with_evidence=<n> head=<sha>`:
    EVIDENCE   box=<i> hand=<@handle|role> url=<url> sha=<sha|none> sha_vs_head=<same|differs|unknown> posts=<k>
    NOEVIDENCE box=<i> hand=<@handle|role|none>
`--human` prints exactly the markdown list the notifier pastes into the 🟡 nudge
(🟡 lines for boxes with evidence, the unchanged `- ⏸ <box>` line otherwise).
Exit 0 always; the caller decides what to do with the text.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pr_merge_blocking_boxes import parse  # noqa: E402  (the ONE §2.2 parser)

NOTIFIER_MARKER = "<!-- pr-check-status-notifier -->"
BOT_LOGINS = {"github-actions", "github-actions[bot]"}
# Logins that identify NO hand: every federation persona (@qbp-architecture,
# @qbp-implementor, @herschel, …) posts through this one account, so a post by it
# could be any seat's — the same-line `@handle` rule is the only identification
# (arch §I4 on PR #785, item 1). Compared case-insensitively.
SHARED_LOGINS = {"JamesPagetButler"}
_SHARED_LOGINS_LC = {s.lower() for s in SHARED_LOGINS}

# APPROVE-class verdicts only. `\bAPPROVE\b` does not match APPROVED/APPROVES;
# review state APPROVED is handled as a state, not as text.
APPROVE_RE = re.compile(r"\bAPPROVE(?:-WITH-CONCERN)?\b")
# A line that carries the verdict but says the box is still owed is not evidence.
# HARD negators: anywhere on the line (see the module docstring for the scoping).
NEGATION_RE = re.compile(
    r"remains?\s+open|still\s+open|not\s+yet|left\s+unticked|requested|outstanding"
    r"|owed|\bawaiting\b|\bwaiting\b|\bask(?:s|ed|ing)?\b"
    r"|\bneed(?:s|ed)?\b|\brequired?\b|\bmissing\b",
    re.I,
)
# PRE negators: a request shape only when they come BEFORE the verdict token
# ("please APPROVE", "for your APPROVE"); after it they are part of a verdict
# ("APPROVE — please merge").
PRE_NEGATION_RE = re.compile(r"\bplease\b|\bfor\s+your\b", re.I)
# ADJACENT negator: `pending` touching the verdict token or an @handle, with only
# whitespace/punctuation between ("APPROVE pending from …", "pending @arch APPROVE");
# "APPROVE — the pending item is tracked in #781" keeps its verdict.
_ADJ_ANCHOR = r"(?:\bAPPROVE(?:-WITH-CONCERN)?\b|@[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)"  # handle shape mirrors HANDLE_RE (no trailing hyphen) — Gemini r3 on PR #785, F2
ADJ_NEGATION_RE = re.compile(
    rf"{_ADJ_ANCHOR}[\W_]*\bpending\b|\bpending\b[\W_]*{_ADJ_ANCHOR}", re.I
)
HANDLE_RE = re.compile(r"@([A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)")
REVIEWED_SHA_RE = re.compile(r"<!--\s*reviewed-sha:\s*([0-9a-fA-F]{7,40})\s*-->")
# "at `486ad51`", "@ a0ca562", "head cdda215", "head sha 486ad51"
LOOSE_SHA_RE = re.compile(
    r"(?:\bat\b|@|\bhead(?:\s+sha)?)\s*[`'\"]?\b([0-9a-f]{7,40})\b", re.I
)
# A loose sha must carry a hex LETTER and a DIGIT: "at 20261028" (a date) or "at
# 40604935020" (a run id) is not a commit, and neither is "at defaced" (an English
# word made of hex letters — Gemini on PR #785, finding 2). Real 7-char shas that
# are all digits (~4%) or all letters (~0.1%) are accepted as a miss; the
# `reviewed-sha` marker form is exact and unaffected.
HEX_LETTER_RE = re.compile(r"[a-f]", re.I)
HEX_DIGIT_RE = re.compile(r"[0-9]")
# Markdown blockquote (GitHub "quote reply"): quoted text is not the post's own voice.
QUOTE_RE = re.compile(r"^\s*>")
HEX_TOKEN_RE = re.compile(r"[0-9a-f]{7,40}", re.I)
# Role fallbacks for handle-less boxes (same words the Tier-3 gate uses).
ROLE_SIGS = {
    "red-team": re.compile(r"Red Team|Sabine|Grothendieck|Knuth", re.I),
    "gemini": re.compile(r"Gemini|Furey|Feynman", re.I),
}
BOX_LABEL_MAX = 72


def _norm_posts(data) -> list[dict]:
    """Flatten `{"comments": [...], "reviews": [...]}` (or a bare list) to one list."""
    comments: list
    reviews: list
    if isinstance(data, list):
        comments, reviews = data, []
    else:
        comments = data.get("comments") or []
        reviews = data.get("reviews") or []

    # Both shapes are read: `gh pr view --json` (author.login / url / createdAt /
    # submittedAt) and the paginated REST endpoints the notifier already uses
    # (user.login / html_url / created_at / submitted_at).
    def _login(x):
        return (((x.get("author") or x.get("user")) or {}).get("login") or "").strip()

    posts = []
    for c in comments:
        posts.append(
            {
                "kind": "comment",
                "author": _login(c),
                "body": c.get("body") or "",
                "url": c.get("html_url") or c.get("url") or "",
                "when": c.get("createdAt") or c.get("created_at") or "",
                "state": "",
            }
        )
    for r in reviews:
        posts.append(
            {
                "kind": "review",
                "author": _login(r),
                "body": r.get("body") or "",
                "url": r.get("html_url") or r.get("url") or "",
                "when": r.get("submittedAt") or r.get("submitted_at") or "",
                "state": (r.get("state") or "").upper(),
            }
        )
    return posts


def _is_bot(post: dict) -> bool:
    return post["author"].lower() in BOT_LOGINS or NOTIFIER_MARKER in post["body"]


def _live_lines(body: str) -> list[str]:
    """The post's own lines — markdown blockquotes (`> …`) dropped (Gemini #785 F1)."""
    return [ln for ln in body.splitlines() if not QUOTE_RE.match(ln)]


def _live_text(post: dict) -> str:
    return "\n".join(_live_lines(post["body"]))


def box_hand(box_text: str):
    """Return ("handle", "qbp-architecture") | ("role", "red-team") | (None, None)."""
    for m in HANDLE_RE.finditer(box_text):
        # "folded @a0ca562" is a sha cite, not a hand
        if not HEX_TOKEN_RE.fullmatch(m.group(1)):
            return "handle", m.group(1)
    for role, sig in ROLE_SIGS.items():
        if sig.search(box_text):
            return "role", role
    return None, None


def _handle_in_line(handle: str, line: str) -> bool:
    return any(h.lower() == handle.lower() for h in HANDLE_RE.findall(line))


def _negated(text: str) -> bool:
    """Does the text say the verdict is still owed (HARD / PRE / ADJACENT shapes)?"""
    if NEGATION_RE.search(text):
        return True
    m = APPROVE_RE.search(text)
    if m and PRE_NEGATION_RE.search(text[: m.start()]):
        return True
    return bool(ADJ_NEGATION_RE.search(text))


def _verdict_lines(post: dict) -> list[str]:
    """Lines of the post that carry an APPROVE-class verdict (not negated)."""
    out: list[str] = []
    for line in _live_lines(post["body"]):
        if APPROVE_RE.search(line) and not _negated(line):
            out.append(line)
    return out


def _author_is(post: dict, handle: str) -> bool:
    """author.login identifies the hand — never for a shared (multi-persona) login."""
    login = post["author"].lower()
    return login == handle.lower() and login not in _SHARED_LOGINS_LC


def post_is_evidence(post: dict, kind, hand) -> bool:
    """Does this post carry an APPROVE-class verdict by/for the box's hand?"""
    if kind is None or _is_bot(post):
        return False
    lines = _verdict_lines(post)
    approved_review = post["kind"] == "review" and post["state"] == "APPROVED"
    if kind == "handle":
        if _author_is(post, hand):
            return bool(lines) or approved_review
        if approved_review and _handle_in_line(hand, _live_text(post)):
            return not _negated(_live_text(post))
        return any(_handle_in_line(hand, ln) for ln in lines)
    # role fallback: the Tier-3 gate's co-occurrence rule — the role signature
    # (usually the review's header line) and a verdict in the SAME post.
    sig = ROLE_SIGS[hand]
    if not sig.search(_live_text(post)):
        return False
    return approved_review or bool(lines)


def _hand_in_lead_line(post: dict, kind, hand) -> bool:
    """Does the post's first content line (skipping HTML markers, quotes) carry the hand?"""
    for line in _live_lines(post["body"]):
        s = line.strip()
        if not s or s.startswith("<!--"):
            continue
        if kind == "handle":
            return _handle_in_line(hand, s)
        return bool(ROLE_SIGS[hand].search(s))
    return False


def cited_sha(post: dict):
    text = _live_text(post)
    m = REVIEWED_SHA_RE.search(text)
    if m:
        return m.group(1).lower()
    for m in LOOSE_SHA_RE.finditer(text):
        tok = m.group(1)
        if HEX_LETTER_RE.search(tok) and HEX_DIGIT_RE.search(tok):
            return tok.lower()
    return None


def sha_vs_head(sha, head):
    if not sha or not head:
        return "unknown"
    a, b = sha.lower(), head.lower()
    return "same" if (a.startswith(b) or b.startswith(a)) else "differs"


def box_label(text: str) -> str:
    """Short, deterministic label for the human line."""
    label = text.strip()
    for sep in (" — ", " - ", ": "):
        head, s, _ = label.partition(sep)
        if s and HANDLE_RE.search(head):
            label = head
            break
    if len(label) > BOX_LABEL_MAX:
        label = label[: BOX_LABEL_MAX - 1].rstrip() + "…"
    return label


def detect(body: str, posts_json, head: str) -> dict:
    """Per unticked merge-blocking box, the candidate evidence post (if any)."""
    boxes = parse(body)
    posts = _norm_posts(posts_json)
    results = []
    for i, text in enumerate(boxes["unticked"], start=1):
        kind, hand = box_hand(text)
        hits = [p for p in posts if post_is_evidence(p, kind, hand)]
        # cite (last wins): a post whose LEAD line carries the hand ("## Red Team —
        # PR #N …", "**§I4 … @qbp-architecture: APPROVE**") over one that mentions it
        # in passing; then a `reviewed-sha`-marked post (the review-artifact
        # convention) over an unmarked summary; then the newest; then url.
        hits.sort(
            key=lambda p: (
                _hand_in_lead_line(p, kind, hand),
                bool(REVIEWED_SHA_RE.search(_live_text(p))),
                p["when"],
                p["url"],
            )
        )
        entry = {
            "box": i,
            "text": text,
            "hand": (f"@{hand}" if kind == "handle" else hand),
            "evidence": None,
            "posts": len(hits),
        }
        if hits:
            p = hits[-1]
            sha = cited_sha(p)
            entry["evidence"] = {
                "url": p["url"],
                "author": p["author"],
                "kind": p["kind"],
                "when": p["when"],
                "sha": sha,
                "sha_vs_head": sha_vs_head(sha, head),
            }
        results.append(entry)
    return {
        "head": head,
        "region": boxes["region"],
        "boxes": results,
        "with_evidence": sum(1 for r in results if r["evidence"]),
    }


def human_lines(res: dict) -> list[str]:
    """The markdown list for the nudge: 🟡 where evidence exists, ⏸ otherwise."""
    short_head = (res["head"] or "")[:7]
    out: list[str] = []
    for r in res["boxes"]:
        ev = r["evidence"]
        if not ev:
            out.append(f"- ⏸ {r['text']}")
            continue
        verdict = "an APPROVE" if ev["kind"] == "comment" else "an APPROVED review"
        sha = (ev["sha"] or "")[:7]
        if ev["sha_vs_head"] == "same":
            where = f"reviewed-sha {sha} = head"
            ask = "the box owner ticks it"
        elif ev["sha_vs_head"] == "differs":
            where = f"reviewed-sha {sha} ≠ head {short_head}"
            ask = "the box owner ticks it or re-reviews at head"
        else:
            where = f"no reviewed-sha cited — confirm it covers head {short_head}"
            ask = "the box owner ticks it or re-reviews at head"
        more = f"; {r['posts']} candidate posts, newest cited" if r["posts"] > 1 else ""
        out.append(
            f'- 🟡 box "{box_label(r["text"])}" is UNTICKED but {verdict} was posted '
            f"({ev['url']}, {where}{more}) — {ask} (auto-nudge, never auto-tick)"
        )
    return out


def machine_lines(res: dict) -> list[str]:
    out = [
        f"boxes={len(res['boxes'])} with_evidence={res['with_evidence']} head={res['head'] or 'none'}"
    ]
    for r in res["boxes"]:
        ev = r["evidence"]
        if ev:
            out.append(
                f"EVIDENCE box={r['box']} hand={r['hand']} url={ev['url']} "
                f"sha={ev['sha'] or 'none'} sha_vs_head={ev['sha_vs_head']} posts={r['posts']}"
            )
        else:
            out.append(f"NOEVIDENCE box={r['box']} hand={r['hand'] or 'none'}")
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--body", required=True, help="PR body file")
    ap.add_argument(
        "--comments",
        required=True,
        help="JSON from `gh pr view N --json comments,reviews`",
    )
    ap.add_argument("--head", default="", help="current head sha")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument(
        "--human", action="store_true", help="print the nudge list for the notifier"
    )
    mode.add_argument("--json", action="store_true", help="print the full result")
    args = ap.parse_args(argv)
    body = Path(args.body).read_text(encoding="utf-8")
    with open(args.comments, encoding="utf-8") as fh:
        posts = json.load(fh)
    res = detect(body, posts, args.head)
    if args.json:
        print(json.dumps(res, ensure_ascii=False))
    elif args.human:
        print("\n".join(human_lines(res)))
    else:
        print("\n".join(machine_lines(res)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
