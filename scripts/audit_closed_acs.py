#!/usr/bin/env python3
"""Retroactive sweep: audit every CLOSED issue for unchecked acceptance criteria.

Issue #543 (FAULT-S4-004 retroactive cleanup). The forward guard
(`check_closing_acs.py` + the "Closing-keyword AC guard" workflow) blocks NEW
auto-closes of issues with unchecked `- [ ] **AC` boxes; the post-merge backstop
(`reopen_falsely_closed.py`) heals same-push slips. Neither looks backwards. This
tool does: it enumerates all closed issues, counts their unchecked boxes, and
emits a beekeeper-review report. It is REPORT-ONLY — it never closes, reopens,
comments on or edits anything, and writes nothing except the `--out` paths.

Box conventions (shared with the forward guard so the two tools agree):
  * `- [ ] **AC...`  unticked acceptance criterion  -> counts as UNTICKED AC.
  * `- [x] ...`      ticked                           -> resolved.
  * nil convention   `⊘` anywhere on the box line, or the box text wrapped in
                     `~~strikethrough~~`              -> resolved (nil'd), never
                     counted as unticked.
  * Any other `- [ ]` box (e.g. under a "Test plan" heading, or an un-bolded
    item) is reported separately as an "other" box. Per #543 AC2 the FLAG is
    driven by the `**AC` boxes only; "other" boxes are shown for context and
    never flag an issue on their own.
  * Nested boxes (indented) count exactly like top-level ones.
  * `guard_unticked` is `check_closing_acs.count_unchecked_acs(body)` verbatim —
    the forward guard's own verdict on the body as it stands today. If it is >0
    for an issue that was closed by a PR, the guard would have caught that close
    (#543 AC5), modulo any body edits made after the close.

Cache-first (#543 AC1): ONE bulk `gh issue list --json ...` call (gh paginates
internally); no per-issue API calls. `closedByPullRequestsReferences` comes back
in the same bulk payload, so "closed by PR" vs "closed manually" costs nothing
extra. Use `--from-cache FILE` to run entirely offline on a saved payload, and
`--save-cache FILE` to keep the raw payload as evidence next to the report.

Deterministic: output depends only on the fetched payload and the flags; rows
are sorted by closedAt desc, then issue number desc; JSON is key-sorted. Running
twice on the same payload produces byte-identical files.

Usage:
  audit_closed_acs.py --out analysis/543-closed-ac-sweep/report-YYYY-MM-DD.md
  audit_closed_acs.py --since 2026-06-01 --limit 200 --out /tmp/r.md
  audit_closed_acs.py --from-cache payload.json --out /tmp/r.md
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from typing import Any, Dict, List, Optional, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from check_closing_acs import count_unchecked_acs  # noqa: E402

DEFAULT_REPO = "JamesPagetButler/QBP"
NIL_MARK = "⊘"

# A markdown task-list item: `- [ ] text` / `* [x] text` / `1. [ ] text`, any indent.
BOX = re.compile(
    r"^(?P<indent>\s*)(?:[-*+]|\d+[.)])\s*\[(?P<mark>[ xX])\]\s*(?P<text>.*)$"
)
HEADING = re.compile(r"^\s{0,3}#{1,6}\s+(?P<title>.+?)\s*#*\s*$")
STRIKE_WRAPPED = re.compile(r"^~~.*~~\s*$")
AC_PREFIX = re.compile(r"^\*\*AC")  # the guard's convention: bold **AC...


# --------------------------------------------------------------------------- parsing


def _is_nil(text: str) -> bool:
    """Nil convention: ⊘ on the line, or the whole box text struck through."""
    t = text.strip()
    if NIL_MARK in t:
        return True
    return bool(STRIKE_WRAPPED.match(t))


def _strip_nil(text: str) -> str:
    return text.replace(NIL_MARK, "").replace("~~", "").strip()


def parse_boxes(body: Optional[str]) -> List[Dict[str, Any]]:
    """Return one record per task-list box in `body`.

    Each record: {text, heading, is_ac, ticked, nil, resolved}
      - is_ac    : box text (after nil-stripping) starts with `**AC`
      - ticked   : `[x]`
      - nil      : nil convention present (⊘ or ~~wrapped~~)
      - resolved : ticked or nil
    Fenced code blocks are skipped (a box quoted inside ``` is documentation).
    """
    out: List[Dict[str, Any]] = []
    heading = ""
    in_fence = False
    for raw in (body or "").splitlines():
        line = raw.rstrip("\r")
        if line.lstrip().startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        h = HEADING.match(line)
        if h:
            heading = h.group("title").strip()
            continue
        m = BOX.match(line)
        if not m:
            continue
        text = m.group("text")
        ticked = m.group("mark").lower() == "x"
        nil = _is_nil(text)
        out.append(
            {
                "text": text.strip(),
                "heading": heading,
                "is_ac": bool(AC_PREFIX.match(_strip_nil(text))),
                "ticked": ticked,
                "nil": nil,
                "resolved": ticked or nil,
            }
        )
    return out


def summarize_boxes(body: Optional[str]) -> Dict[str, int]:
    """Counts used by the report. Keys:
    ac_total, ac_unticked, other_total, other_unticked, nil, guard_unticked."""
    boxes = parse_boxes(body)
    ac = [b for b in boxes if b["is_ac"]]
    other = [b for b in boxes if not b["is_ac"]]
    return {
        "ac_total": len(ac),
        "ac_unticked": sum(1 for b in ac if not b["resolved"]),
        "other_total": len(other),
        "other_unticked": sum(1 for b in other if not b["resolved"]),
        "nil": sum(1 for b in boxes if b["nil"]),
        "guard_unticked": count_unchecked_acs(body),
    }


# --------------------------------------------------------------------------- fetch


def fetch_closed_issues(repo: str, limit: int) -> List[Dict[str, Any]]:
    """ONE bulk call (gh paginates internally). No per-issue requests."""
    cmd = [
        "gh",
        "issue",
        "list",
        "--repo",
        repo,
        "--state",
        "closed",
        "--limit",
        str(limit),
        "--json",
        "number,title,body,closedAt,labels,url,stateReason,closedByPullRequestsReferences",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if out.returncode != 0:
        raise SystemExit(f"gh failed ({out.returncode}): {out.stderr.strip()}")
    data = json.loads(out.stdout)
    if not isinstance(data, list):
        raise SystemExit("unexpected gh payload (expected a JSON list)")
    return data


def load_cache(path: str) -> List[Dict[str, Any]]:
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, list):
        raise SystemExit(f"{path}: expected a JSON list of issues")
    return data


# --------------------------------------------------------------------------- audit


def closed_by(issue: Dict[str, Any], repo: str = DEFAULT_REPO) -> Tuple[str, List[str]]:
    """('pr', ['#512', 'JamesPagetButler/qbp-systema#1', ...]) if a closing PR is
    linked (same-repo PRs as '#n', cross-repo as 'owner/name#n'), else ('manual', []).
    """
    refs = issue.get("closedByPullRequestsReferences") or []
    labels = set()
    for r in refs:
        n = r.get("number")
        if n is None:
            continue
        rep = r.get("repository") or {}
        owner = (rep.get("owner") or {}).get("login") or ""
        name = rep.get("name") or ""
        full = f"{owner}/{name}" if owner and name else ""
        if full and full.lower() != repo.lower():
            labels.add(f"{full}#{int(n)}")
        else:
            labels.add(f"#{int(n)}")
    if labels:
        return "pr", sorted(labels, key=lambda x: (x.count("/"), x))
    return "manual", []


def audit(
    issues: List[Dict[str, Any]], since: Optional[str] = None, repo: str = DEFAULT_REPO
) -> Dict[str, Any]:
    rows: List[Dict[str, Any]] = []
    for it in issues:
        closed_at = it.get("closedAt") or ""
        if since and closed_at[:10] < since:
            continue
        counts = summarize_boxes(it.get("body"))
        how, prs = closed_by(it, repo)
        rows.append(
            {
                "number": int(it["number"]),
                "title": it.get("title") or "",
                "url": it.get("url") or "",
                "closedAt": closed_at,
                "stateReason": it.get("stateReason") or "",
                "labels": sorted(
                    (lb.get("name") or "") for lb in (it.get("labels") or [])
                ),
                "closed_by": how,
                "closing_prs": prs,
                **counts,
                "flagged": counts["ac_unticked"] >= 1,
                # #543 AC5: would the forward guard (as it stands) have blocked this
                # close? Only meaningful for PR-closed issues.
                "guard_would_catch": (how == "pr" and counts["guard_unticked"] >= 1),
            }
        )
    rows.sort(key=lambda r: (r["closedAt"], r["number"]), reverse=True)

    flagged = [r for r in rows if r["flagged"]]
    any_unticked = [r for r in rows if r["ac_unticked"] + r["other_unticked"] >= 1]
    flagged_pr = [r for r in flagged if r["closed_by"] == "pr"]
    summary = {
        "scanned": len(rows),
        "flagged_unticked_ac": len(flagged),
        "flagged_closed_by_pr": len(flagged_pr),
        "flagged_closed_manually": len(flagged) - len(flagged_pr),
        "flagged_pr_guard_would_catch": sum(
            1 for r in flagged_pr if r["guard_would_catch"]
        ),
        "any_unticked_box": len(any_unticked),
        "other_only_unticked": len(any_unticked) - len(flagged),
        "clean": len(rows) - len(any_unticked),
        "total_unticked_ac_boxes": sum(r["ac_unticked"] for r in rows),
        "closed_by_pr": sum(1 for r in rows if r["closed_by"] == "pr"),
        "closed_manually": sum(1 for r in rows if r["closed_by"] == "manual"),
        "closedAt_min": min((r["closedAt"] for r in rows), default=""),
        "closedAt_max": max((r["closedAt"] for r in rows), default=""),
        "since": since or "",
    }
    return {"summary": summary, "rows": rows}


# --------------------------------------------------------------------------- render


def _md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ").strip()


def render_markdown(result: Dict[str, Any], repo: str, report_date: str) -> str:
    s = result["summary"]
    rows = result["rows"]
    flagged = [r for r in rows if r["flagged"]]
    other_only = [r for r in rows if not r["flagged"] and r["other_unticked"] >= 1]

    L: List[str] = []
    L.append(f"# Closed-issue AC sweep — {repo} — {report_date}")
    L.append("")
    L.append(
        "Issue #543 (FAULT-S4-004 retroactive sweep). **Report only** — nothing was "
        "closed, reopened, ticked or commented. The beekeeper triages the flagged rows "
        "(#543 AC3) and fills the *verdict* / *action* columns."
    )
    L.append("")
    L.append(
        "Generated by `scripts/audit_closed_acs.py` (one bulk `gh issue list` call, "
        "no per-issue API calls). Box convention = the forward guard's "
        "(`- [ ] **AC` = unticked AC; `[x]` ticked; `⊘` / `~~…~~` = nil'd = resolved). "
        '"Other" boxes = any non-`**AC` box (test plans, sub-tasks); they are shown but '
        "do not flag an issue (#543 AC2)."
    )
    L.append("")
    L.append("## Summary")
    L.append("")
    L.append("| Metric | Count |")
    L.append("|---|---:|")
    L.append(
        f"| Closed issues scanned{' (since ' + s['since'] + ')' if s['since'] else ''} | {s['scanned']} |"
    )
    L.append(
        f"| closedAt range | {s['closedAt_min'][:10]} → {s['closedAt_max'][:10]} |"
    )
    L.append(
        f"| **Flagged: ≥1 unticked `**AC` box** | **{s['flagged_unticked_ac']}** |"
    )
    L.append(f"| … of which closed by a linked PR | {s['flagged_closed_by_pr']} |")
    L.append(
        f"| … of which closed manually (no linked closing PR) | {s['flagged_closed_manually']} |"
    )
    L.append(
        f"| … PR-closed AND forward guard would have caught it (AC5) | "
        f"{s['flagged_pr_guard_would_catch']} / {s['flagged_closed_by_pr']} |"
    )
    L.append(
        f"| Total unticked `**AC` boxes across flagged issues | {s['total_unticked_ac_boxes']} |"
    )
    L.append(f"| Issues with ≥1 unticked box of ANY kind | {s['any_unticked_box']} |")
    L.append(
        f"| … only non-AC (\"other\") boxes unticked | {s['other_only_unticked']} |"
    )
    L.append(f"| Clean (no unticked boxes at all) | {s['clean']} |")
    L.append(
        f"| Closed by linked PR / manually (all scanned) | {s['closed_by_pr']} / {s['closed_manually']} |"
    )
    L.append("")
    L.append("## Flagged issues (≥1 unticked `**AC` box) — sorted by closedAt desc")
    L.append("")
    L.append(
        "| # | Title | closedAt | AC unticked/total | other unticked/total | closed by | guard catches? | verdict | action | url |"
    )
    L.append("|---|---|---|---:|---:|---|---|---|---|---|")
    for r in flagged:
        cb = "PR " + ", ".join(r["closing_prs"]) if r["closed_by"] == "pr" else "manual"
        if r["stateReason"] == "NOT_PLANNED":
            cb += " (not planned)"
        guard = (
            ("yes" if r["guard_would_catch"] else "no")
            if r["closed_by"] == "pr"
            else "n/a"
        )
        L.append(
            f"| #{r['number']} | {_md_escape(r['title'])} | {r['closedAt'][:10]} | "
            f"{r['ac_unticked']}/{r['ac_total']} | {r['other_unticked']}/{r['other_total']} | "
            f"{cb} | {guard} | — | — | {r['url']} |"
        )
    L.append("")
    L.append("## Not flagged, but with unticked non-AC boxes (context only)")
    L.append("")
    L.append("| # | Title | closedAt | other unticked/total | closed by | url |")
    L.append("|---|---|---|---:|---|---|")
    for r in other_only:
        cb = "PR " + ", ".join(r["closing_prs"]) if r["closed_by"] == "pr" else "manual"
        L.append(
            f"| #{r['number']} | {_md_escape(r['title'])} | {r['closedAt'][:10]} | "
            f"{r['other_unticked']}/{r['other_total']} | {cb} | {r['url']} |"
        )
    L.append("")
    L.append("## Triage key (#543 AC3 — beekeeper fills in)")
    L.append("")
    L.append("- **reopen** — genuinely incomplete (like #474).")
    L.append("- **tick** — ACs met but never ticked: tick with evidence, leave closed.")
    L.append("- **nil** — AC stale/obsolete: mark `⊘ ~~…~~` with a note, leave closed.")
    L.append("")
    L.append(
        "*guard catches?* = `check_closing_acs.count_unchecked_acs(body) ≥ 1` on the "
        "body as it stands today, for PR-closed issues (AC5). A `no` means the body's "
        "unticked boxes are not in the guard's `- [ ] **AC` form (so the nil/`**AC` "
        "classifier flagged it but the guard regex would not) — or the body was edited "
        "after the close."
    )
    L.append("")
    return "\n".join(L)


# --------------------------------------------------------------------------- main


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=DEFAULT_REPO)
    ap.add_argument(
        "--since", default=None, help="only issues closed on/after YYYY-MM-DD"
    )
    ap.add_argument(
        "--limit", type=int, default=1000, help="max closed issues to fetch"
    )
    ap.add_argument(
        "--out",
        required=True,
        help="markdown report path; JSON sidecar = same stem + .json",
    )
    ap.add_argument(
        "--from-cache",
        default=None,
        help="read the gh payload from this file instead of calling gh",
    )
    ap.add_argument(
        "--save-cache",
        default=None,
        help="also save the raw gh payload here (evidence)",
    )
    ap.add_argument(
        "--report-date",
        default=None,
        help="date label for the report header (default: from --out stem or closedAt max)",
    )
    args = ap.parse_args(argv)

    if args.since and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", args.since):
        ap.error("--since must be YYYY-MM-DD")

    issues = (
        load_cache(args.from_cache)
        if args.from_cache
        else fetch_closed_issues(args.repo, args.limit)
    )
    result = audit(issues, since=args.since, repo=args.repo)
    result["repo"] = args.repo
    result["limit"] = args.limit

    stem, _ = os.path.splitext(args.out)
    m = re.search(r"(\d{4}-\d{2}-\d{2})", os.path.basename(stem))
    report_date = args.report_date or (
        m.group(1) if m else result["summary"]["closedAt_max"][:10]
    )
    result["report_date"] = report_date

    out_dir = os.path.dirname(os.path.abspath(args.out))
    os.makedirs(out_dir, exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(render_markdown(result, args.repo, report_date))
    with open(stem + ".json", "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    if args.save_cache:
        with open(args.save_cache, "w", encoding="utf-8") as f:
            json.dump(
                sorted(issues, key=lambda i: i["number"]),
                f,
                indent=1,
                sort_keys=True,
                ensure_ascii=False,
            )
            f.write("\n")

    s = result["summary"]
    print(
        f"scanned={s['scanned']} flagged_unticked_ac={s['flagged_unticked_ac']} "
        f"(pr={s['flagged_closed_by_pr']}, manual={s['flagged_closed_manually']}, "
        f"guard_would_catch={s['flagged_pr_guard_would_catch']}) "
        f"any_unticked={s['any_unticked_box']} clean={s['clean']}"
    )
    print(f"wrote {args.out} and {stem + '.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
