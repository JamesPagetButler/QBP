#!/usr/bin/env python3
"""Retroactive sweep: audit every CLOSED issue for unchecked acceptance criteria.

Issue #543 (FAULT-S4-004 retroactive cleanup). The forward guard
(`check_closing_acs.py` + the "Closing-keyword AC guard" workflow) blocks NEW
auto-closes of issues with unchecked `- [ ] **AC` boxes; the post-merge backstop
(`reopen_falsely_closed.py`) heals same-push slips. Neither looks backwards. This
tool does: it enumerates all closed issues, counts their unchecked boxes, and
emits a beekeeper-review report. It is REPORT-ONLY — it never closes, reopens,
comments on or edits anything, and writes nothing except the `--out` paths
(+ the optional `--save-*-cache` paths).

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
  * Nested boxes (indented) count exactly like top-level ones. Boxes inside
    ``` / ~~~ fenced code or inside <!-- HTML comments --> are documentation
    and are skipped. Known gaps (no live occurrence): a 4-space-indented ```
    is treated as a fence (CommonMark says indented code); `[\\t]` is not a box.

Close attribution — two DIFFERENT relations, both reported:
  * `linked_prs`  — GitHub's `closedByPullRequestsReferences`: PRs *linked* to the
    issue (closing keyword in the PR text, or a manual Development-sidebar link),
    open or merged. Linkage is NOT "the PR that closed it": a hand-closed issue
    can carry a linked PR that merged hours later (#236/#237 vs PR #240).
  * `closed_how`  — real attribution from ONE extra bulk call per repo
    (`gh pr list --state merged --json number,mergedAt,title,body,
    closingIssuesReferences`): `merged-pr` iff a merged PR lists the issue in its
    `closingIssuesReferences` AND `|mergedAt - closedAt| <= --merge-window`
    (default 120 s); else `manual` (which also covers a closing keyword in a
    commit pushed straight to master — invisible here and to the guard); or
    `unknown` when no merged-PR payload is available (issues-only cache).
    Cross-repo closers (e.g. qbp-systema PRs closing QBP issues) are resolved by
    fetching the merged PRs of every repo that appears in `linked_prs`.

Forward-guard retro-check (#543 AC5) — the guard fires iff BOTH
  (a) the PR title+body carries a closing keyword for #N   (`closing_refs`), and
  (b) the issue body has >=1 unticked `- [ ] **AC` box       (`count_unchecked_acs`).
  * `body_check_would_trip`  = (b) on the body as it stands today (any close).
  * `closing_pr_has_keyword` = (a) on the attributed closing PR (merged-pr only).
  * `guard_would_have_fired` = merged-pr in THIS repo AND (a) AND (b). A closer in
    another repo (e.g. `Closes [QBP #441](…)` from qbp-systema) is outside the
    guard's reach: the workflow is installed in QBP only.
  A merged-pr close WITHOUT a keyword is a manual Development-sidebar link: GitHub
  still auto-closes on merge, but the guard cannot see it (#22 via PR #285).

Cache-first (#543 AC1): bulk fetches only (gh paginates internally), never a
per-issue call: 1 issues call + 1 merged-PR call per repo seen in `linked_prs`
(2 today: QBP + qbp-systema) = 3. `--from-cache` / `--from-merged-cache` replay
saved payloads offline; `--save-cache` / `--save-merged-cache` keep them as
evidence next to the report.

Deterministic: output depends only on the payloads and the flags; rows are
sorted by closedAt desc, then issue number desc; JSON is key-sorted. Running
twice on the same payloads produces byte-identical files.

Usage:
  audit_closed_acs.py --out analysis/543-closed-ac-sweep/report-YYYY-MM-DD.md \\
      --save-cache …/report-YYYY-MM-DD.issues.json \\
      --save-merged-cache …/report-YYYY-MM-DD.merged-prs.json
  audit_closed_acs.py --since 2026-06-01 --limit 200 --out /tmp/r.md
  audit_closed_acs.py --from-cache issues.json --from-merged-cache prs.json --out /tmp/r.md
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from check_closing_acs import closing_refs, count_unchecked_acs  # noqa: E402

DEFAULT_REPO = "JamesPagetButler/QBP"
DEFAULT_MERGE_WINDOW_S = 120
NIL_MARK = "⊘"

# A markdown task-list item: `- [ ] text` / `* [x] text` / `1. [ ] text`, any indent.
BOX = re.compile(
    r"^(?P<indent>\s*)(?:[-*+]|\d+[.)])\s*\[(?P<mark>[ xX])\]\s*(?P<text>.*)$"
)
HEADING = re.compile(r"^\s{0,3}#{1,6}\s+(?P<title>.+?)\s*#*\s*$")
FENCE = re.compile(r"^\s*(?P<fence>```|~~~)")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
STRIKE_WRAPPED = re.compile(r"^~~.*~~\s*$")
AC_PREFIX = re.compile(r"^\*\*AC")  # the guard's convention: bold **AC...
ISSUE_FIELDS = (
    "number,title,body,closedAt,labels,url,stateReason,closedByPullRequestsReferences"
)
PR_FIELDS = "number,title,body,mergedAt,closingIssuesReferences"


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
    Fenced code (``` or ~~~) and <!-- HTML comments --> are skipped.
    """
    out: List[Dict[str, Any]] = []
    heading = ""
    fence: Optional[str] = None
    for raw in HTML_COMMENT.sub("", body or "").splitlines():
        line = raw.rstrip("\r")
        fm = FENCE.match(line)
        if fm:
            mark = fm.group("fence")
            if fence is None:
                fence = mark
            elif mark == fence:
                fence = None
            continue
        if fence is not None:
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


def _gh_list(cmd: List[str]) -> List[Dict[str, Any]]:
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    if out.returncode != 0:
        raise SystemExit(f"gh failed ({out.returncode}): {out.stderr.strip()}")
    data = json.loads(out.stdout)
    if not isinstance(data, list):
        raise SystemExit("unexpected gh payload (expected a JSON list)")
    return data


def fetch_closed_issues(repo: str, limit: int) -> List[Dict[str, Any]]:
    """ONE bulk call (gh paginates internally). No per-issue requests."""
    data = _gh_list(
        [
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
            ISSUE_FIELDS,
        ]
    )
    if len(data) >= limit:
        print(
            f"WARNING: fetched {len(data)} issues == --limit {limit}; the list may be "
            f"truncated (gh orders by creation date, so --since can miss recent closes "
            f"of old issues). Raise --limit.",
            file=sys.stderr,
        )
    return data


def fetch_merged_prs(repo: str, limit: int) -> List[Dict[str, Any]]:
    """ONE bulk call per repo (gh paginates internally)."""
    data = _gh_list(
        [
            "gh",
            "pr",
            "list",
            "--repo",
            repo,
            "--state",
            "merged",
            "--limit",
            str(limit),
            "--json",
            PR_FIELDS,
        ]
    )
    if len(data) >= limit:
        print(
            f"WARNING: fetched {len(data)} merged PRs from {repo} == --limit {limit}; "
            f"the list may be truncated. Raise --limit.",
            file=sys.stderr,
        )
    return data


def load_json(path: str) -> Any:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def load_cache(path: str) -> List[Dict[str, Any]]:
    data = load_json(path)
    if not isinstance(data, list):
        raise SystemExit(f"{path}: expected a JSON list of issues")
    return data


def load_merged_cache(path: str) -> Dict[str, List[Dict[str, Any]]]:
    data = load_json(path)
    if not isinstance(data, dict):
        raise SystemExit(f"{path}: expected a JSON object {{repo: [merged PRs]}}")
    return data


# --------------------------------------------------------------------------- attribution


def _pr_label(ref: Dict[str, Any], repo: str) -> Tuple[str, str]:
    """('owner/name', '#n' or 'owner/name#n') for a PR/issue reference record."""
    rep = ref.get("repository") or {}
    owner = (rep.get("owner") or {}).get("login") or ""
    name = rep.get("name") or ""
    full = f"{owner}/{name}" if owner and name else repo
    n = int(ref["number"])
    label = f"#{n}" if full.lower() == repo.lower() else f"{full}#{n}"
    return full, label


def linked_prs(issue: Dict[str, Any], repo: str) -> List[Tuple[str, int, str]]:
    """[(repo_full, pr_number, label)] from closedByPullRequestsReferences,
    sorted same-repo first then by label."""
    out = set()
    for r in issue.get("closedByPullRequestsReferences") or []:
        if r.get("number") is None:
            continue
        full, label = _pr_label(r, repo)
        out.add((full, int(r["number"]), label))
    return sorted(out, key=lambda t: (t[2].count("/"), t[2]))


def repos_in_linked_prs(issues: List[Dict[str, Any]], repo: str) -> List[str]:
    """Every repo that appears in any issue's linked PRs (the target repo first)."""
    seen = {repo}
    for it in issues:
        for full, _n, _lbl in linked_prs(it, repo):
            seen.add(full)
    return [repo] + sorted(r for r in seen if r != repo)


def _ts(s: str) -> Optional[datetime]:
    if not s:
        return None
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(timezone.utc)
    except ValueError:
        return None


def build_closer_index(
    merged: Dict[str, List[Dict[str, Any]]], repo: str
) -> Dict[int, List[Dict[str, Any]]]:
    """issue number -> [merged PR records (with repo_full) whose
    closingIssuesReferences name that issue of the target repo]."""
    idx: Dict[int, List[Dict[str, Any]]] = {}
    for pr_repo, prs in merged.items():
        for pr in prs:
            for ref in pr.get("closingIssuesReferences") or []:
                if ref.get("number") is None:
                    continue
                full, _lbl = _pr_label(ref, repo)
                if full.lower() != repo.lower():
                    continue
                rec = dict(pr)
                rec["repo_full"] = pr_repo
                idx.setdefault(int(ref["number"]), []).append(rec)
    return idx


def attribute_close(
    issue: Dict[str, Any],
    closers: Dict[int, List[Dict[str, Any]]],
    repo: str,
    window_s: int,
    have_merged: bool,
) -> Dict[str, Any]:
    """Return {closed_how, closing_pr, closing_pr_repo, merge_delta_s,
    closing_pr_has_keyword}."""
    res: Dict[str, Any] = {
        "closed_how": "unknown" if not have_merged else "manual",
        "closing_pr": "",
        "closing_pr_repo": "",
        "merge_delta_s": None,
        "closing_pr_has_keyword": None,
    }
    if not have_merged:
        return res
    closed_at = _ts(issue.get("closedAt") or "")
    if closed_at is None:
        return res
    best: Optional[Tuple[float, Dict[str, Any]]] = None
    for pr in closers.get(int(issue["number"]), []):
        merged_at = _ts(pr.get("mergedAt") or "")
        if merged_at is None:
            continue
        delta = abs((merged_at - closed_at).total_seconds())
        if delta <= window_s and (best is None or delta < best[0]):
            best = (delta, pr)
    if best is None:
        return res
    delta, pr = best
    _full, label = _pr_label(
        {
            "number": pr["number"],
            "repository": {
                "owner": {"login": pr["repo_full"].split("/")[0]},
                "name": pr["repo_full"].split("/")[1],
            },
        },
        repo,
    )
    text = (pr.get("title") or "") + "\n" + (pr.get("body") or "")
    res.update(
        {
            "closed_how": "merged-pr",
            "closing_pr": label,
            "closing_pr_repo": pr["repo_full"],
            "merge_delta_s": int(delta),
            "closing_pr_has_keyword": int(issue["number"]) in closing_refs(text),
        }
    )
    return res


# --------------------------------------------------------------------------- audit


def audit(
    issues: List[Dict[str, Any]],
    since: Optional[str] = None,
    repo: str = DEFAULT_REPO,
    merged: Optional[Dict[str, List[Dict[str, Any]]]] = None,
    window_s: int = DEFAULT_MERGE_WINDOW_S,
) -> Dict[str, Any]:
    have_merged = merged is not None
    closers = build_closer_index(merged or {}, repo)
    rows: List[Dict[str, Any]] = []
    for it in issues:
        closed_at = it.get("closedAt") or ""
        if since and closed_at[:10] < since:
            continue
        counts = summarize_boxes(it.get("body"))
        links = linked_prs(it, repo)
        attr = attribute_close(it, closers, repo, window_s, have_merged)
        body_trip = counts["guard_unticked"] >= 1
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
                "linked_prs": [lbl for _f, _n, lbl in links],
                **attr,
                **counts,
                "flagged": counts["ac_unticked"] >= 1,
                "all_ac_unticked": counts["ac_total"] >= 1
                and counts["ac_unticked"] == counts["ac_total"],
                # #543 AC5 — the two halves of the forward guard, separately:
                "body_check_would_trip": body_trip,
                "closing_pr_cross_repo": (
                    attr["closed_how"] == "merged-pr"
                    and attr["closing_pr_repo"].lower() != repo.lower()
                ),
                # The guard is a QBP workflow: it only ever sees PRs in THIS repo.
                "guard_would_have_fired": (
                    attr["closed_how"] == "merged-pr"
                    and attr["closing_pr_repo"].lower() == repo.lower()
                    and bool(attr["closing_pr_has_keyword"])
                    and body_trip
                ),
            }
        )
    rows.sort(key=lambda r: (r["closedAt"], r["number"]), reverse=True)

    flagged = [r for r in rows if r["flagged"]]
    any_unticked = [r for r in rows if r["ac_unticked"] + r["other_unticked"] >= 1]
    f_merged = [r for r in flagged if r["closed_how"] == "merged-pr"]
    f_manual = [r for r in flagged if r["closed_how"] == "manual"]
    f_unknown = [r for r in flagged if r["closed_how"] == "unknown"]
    f_linked = [r for r in flagged if r["linked_prs"]]
    summary = {
        "scanned": len(rows),
        "flagged_unticked_ac": len(flagged),
        "flagged_all_ac_unticked": sum(1 for r in flagged if r["all_ac_unticked"]),
        "flagged_with_linked_pr": len(f_linked),
        "flagged_closed_by_merged_pr": len(f_merged),
        "flagged_closed_manually": len(f_manual),
        "flagged_closed_unknown": len(f_unknown),
        "flagged_linked_but_hand_closed": sum(
            1 for r in f_linked if r["closed_how"] == "manual"
        ),
        "flagged_merged_pr_guard_would_have_fired": sum(
            1 for r in f_merged if r["guard_would_have_fired"]
        ),
        "flagged_merged_pr_no_keyword": sum(
            1
            for r in f_merged
            if not r["closing_pr_has_keyword"] and not r["closing_pr_cross_repo"]
        ),
        "flagged_merged_pr_cross_repo": sum(
            1 for r in f_merged if r["closing_pr_cross_repo"]
        ),
        "flagged_body_check_would_trip": sum(
            1 for r in flagged if r["body_check_would_trip"]
        ),
        "any_unticked_box": len(any_unticked),
        "other_only_unticked": len(any_unticked) - len(flagged),
        "clean": len(rows) - len(any_unticked),
        "total_unticked_ac_boxes": sum(r["ac_unticked"] for r in rows),
        "with_linked_pr": sum(1 for r in rows if r["linked_prs"]),
        "closed_by_merged_pr": sum(1 for r in rows if r["closed_how"] == "merged-pr"),
        "closed_manually": sum(1 for r in rows if r["closed_how"] == "manual"),
        "closed_unknown": sum(1 for r in rows if r["closed_how"] == "unknown"),
        "closedAt_min": min((r["closedAt"] for r in rows), default=""),
        "closedAt_max": max((r["closedAt"] for r in rows), default=""),
        "since": since or "",
        "merge_window_s": window_s,
        "merged_pr_repos": sorted((merged or {}).keys()),
    }
    return {"summary": summary, "rows": rows}


# --------------------------------------------------------------------------- render


def _md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ").strip()


def _how_cell(r: Dict[str, Any]) -> str:
    if r["closed_how"] == "merged-pr":
        cell = f"merged-pr {r['closing_pr']}"
        if r["merge_delta_s"]:
            cell += f" (Δ{r['merge_delta_s']}s)"
    else:
        cell = r["closed_how"]
    if r["stateReason"] == "NOT_PLANNED":
        cell += " (not planned)"
    return cell


def _linked_cell(r: Dict[str, Any]) -> str:
    return ", ".join(r["linked_prs"]) if r["linked_prs"] else "—"


def _guard_cell(r: Dict[str, Any]) -> str:
    if r["closed_how"] == "merged-pr":
        if r["guard_would_have_fired"]:
            return "yes (keyword + body)"
        if r["closing_pr_cross_repo"]:
            return "no — closing PR is in another repo (guard not installed there)"
        if not r["closing_pr_has_keyword"]:
            return "no — no keyword in PR text (manual link; guard blind)"
        return "no — body would not trip"
    if r["closed_how"] == "manual":
        return "n/a (manual)"
    return "n/a (unknown)"


def render_markdown(result: Dict[str, Any], repo: str, report_date: str) -> str:
    s = result["summary"]
    rows = result["rows"]
    flagged = [r for r in rows if r["flagged"]]
    other_only = [r for r in rows if not r["flagged"] and r["other_unticked"] >= 1]
    since = f" (since {s['since']})" if s["since"] else ""
    repos = ", ".join(f"`{r}`" for r in s["merged_pr_repos"]) or "none"

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
        "Generated by `scripts/audit_closed_acs.py` (bulk `gh issue list` + one bulk "
        "`gh pr list --state merged` per repo seen in linked PRs; no per-issue API "
        "calls). Box convention = the forward guard's (`- [ ] **AC` = unticked AC; "
        '`[x]` ticked; `⊘` / `~~…~~` = nil\'d = resolved). "Other" boxes = any '
        "non-`**AC` box (test plans, sub-tasks); they are shown but do not flag an "
        "issue (#543 AC2)."
    )
    L.append("")
    L.append(
        "**Two close relations are reported.** *linked PR* = GitHub's "
        "`closedByPullRequestsReferences` — PRs linked to the issue (closing keyword "
        "or manual Development-sidebar link), open or merged; it is NOT the closer. "
        "*closed how* = real attribution: `merged-pr #n` iff a merged PR lists the "
        f"issue in `closingIssuesReferences` and merged within {s['merge_window_s']} s "
        "of `closedAt` (Δ shown); otherwise `manual` — which also covers a closing "
        "keyword in a commit pushed straight to master (invisible here and to the "
        f"guard). Merged-PR payloads: {repos}."
    )
    L.append("")
    L.append("## Summary")
    L.append("")
    L.append("| Metric | Count |")
    L.append("|---|---:|")
    L.append(f"| Closed issues scanned{since} | {s['scanned']} |")
    L.append(
        f"| closedAt range | {s['closedAt_min'][:10]} → {s['closedAt_max'][:10]} |"
    )
    L.append(
        f"| **Flagged: ≥1 unticked `**AC` box** | **{s['flagged_unticked_ac']}** |"
    )
    L.append(
        f"| … with ALL AC boxes unticked (n/n — closed without ever ticking) | "
        f"{s['flagged_all_ac_unticked']} |"
    )
    L.append(
        f"| … closed by a merged PR (within window) | {s['flagged_closed_by_merged_pr']} |"
    )
    L.append(
        f"| … closed manually (no merged PR within window) | {s['flagged_closed_manually']} |"
    )
    if s["flagged_closed_unknown"]:
        L.append(
            f"| … attribution unknown (no merged-PR payload) | {s['flagged_closed_unknown']} |"
        )
    L.append(f"| … carrying a linked PR | {s['flagged_with_linked_pr']} |")
    L.append(
        f"| … linked PR but hand-closed (linkage ≠ closer) | "
        f"{s['flagged_linked_but_hand_closed']} |"
    )
    L.append(
        f"| AC5 — forward guard would have fired (keyword in PR text AND unticked "
        f"body) | {s['flagged_merged_pr_guard_would_have_fired']} / "
        f"{s['flagged_closed_by_merged_pr']} merged-PR closes |"
    )
    L.append(
        f"| AC5 — merged-PR close with NO closing keyword (manual link; guard blind) | "
        f"{s['flagged_merged_pr_no_keyword']} |"
    )
    L.append(
        f"| AC5 — merged-PR close from ANOTHER repo (QBP's guard never sees it) | "
        f"{s['flagged_merged_pr_cross_repo']} |"
    )
    L.append(
        f"| Body-check half alone would trip (`count_unchecked_acs ≥ 1`) | "
        f"{s['flagged_body_check_would_trip']} / {s['flagged_unticked_ac']} |"
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
        f"| All scanned: merged-pr / manual / unknown | {s['closed_by_merged_pr']} / "
        f"{s['closed_manually']} / {s['closed_unknown']} |"
    )
    L.append(f"| All scanned: with a linked PR | {s['with_linked_pr']} |")
    L.append("")
    L.append("## Flagged issues (≥1 unticked `**AC` box) — sorted by closedAt desc")
    L.append("")
    L.append(
        "| # | Title | closedAt | AC unticked/total | other unticked/total | "
        "closed how | linked PR | guard would have fired? | verdict | action | url |"
    )
    L.append("|---|---|---|---:|---:|---|---|---|---|---|---|")
    for r in flagged:
        L.append(
            f"| #{r['number']} | {_md_escape(r['title'])} | {r['closedAt'][:10]} | "
            f"{r['ac_unticked']}/{r['ac_total']} | {r['other_unticked']}/{r['other_total']} | "
            f"{_how_cell(r)} | {_linked_cell(r)} | {_guard_cell(r)} | — | — | {r['url']} |"
        )
    L.append("")
    L.append("## Not flagged, but with unticked non-AC boxes (context only)")
    L.append("")
    L.append(
        "| # | Title | closedAt | other unticked/total | closed how | linked PR | url |"
    )
    L.append("|---|---|---|---:|---|---|---|")
    for r in other_only:
        L.append(
            f"| #{r['number']} | {_md_escape(r['title'])} | {r['closedAt'][:10]} | "
            f"{r['other_unticked']}/{r['other_total']} | {_how_cell(r)} | "
            f"{_linked_cell(r)} | {r['url']} |"
        )
    L.append("")
    L.append("## Triage key (#543 AC3 — beekeeper fills in)")
    L.append("")
    L.append("- **reopen** — genuinely incomplete (like #474).")
    L.append("- **tick** — ACs met but never ticked: tick with evidence, leave closed.")
    L.append("- **nil** — AC stale/obsolete: mark `⊘ ~~…~~` with a note, leave closed.")
    L.append("")
    L.append(
        "*guard would have fired?* (AC5) = the close was a merged PR within the window "
        "AND that PR's title+body carries a closing keyword for the issue "
        "(`check_closing_acs.closing_refs`) AND the body has ≥1 `- [ ] **AC` box "
        "(`count_unchecked_acs`). Both halves are evaluated on the text as it stands "
        "today: a body or PR description edited after the close could change either "
        "answer, in either direction. `manual` closes and closers merged in another "
        "repo are outside the guard's view by construction."
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
        "--limit", type=int, default=1000, help="max issues / merged PRs per bulk call"
    )
    ap.add_argument(
        "--merge-window",
        type=int,
        default=DEFAULT_MERGE_WINDOW_S,
        help="seconds between a linked PR's mergedAt and closedAt to attribute the close",
    )
    ap.add_argument(
        "--out",
        required=True,
        help="markdown report path; JSON sidecar = same stem + .json",
    )
    ap.add_argument(
        "--from-cache",
        default=None,
        help="read the issues payload from this file instead of gh",
    )
    ap.add_argument(
        "--from-merged-cache",
        default=None,
        help="read the merged-PR payloads ({repo: [...]}) from this file instead of gh",
    )
    ap.add_argument(
        "--no-merged",
        action="store_true",
        help="skip merged-PR attribution (closed_how=unknown)",
    )
    ap.add_argument(
        "--save-cache", default=None, help="save the raw issues payload here"
    )
    ap.add_argument(
        "--save-merged-cache", default=None, help="save the raw merged-PR payloads here"
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
    merged: Optional[Dict[str, List[Dict[str, Any]]]]
    if args.no_merged:
        merged = None
    elif args.from_merged_cache:
        merged = load_merged_cache(args.from_merged_cache)
    elif args.from_cache:
        merged = (
            None  # issues-only replay: attribution unknown unless a PR cache is given
        )
    else:
        merged = {
            r: fetch_merged_prs(r, args.limit)
            for r in repos_in_linked_prs(issues, args.repo)
        }

    result = audit(
        issues,
        since=args.since,
        repo=args.repo,
        merged=merged,
        window_s=args.merge_window,
    )
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
    if args.save_merged_cache and merged is not None:
        with open(args.save_merged_cache, "w", encoding="utf-8") as f:
            json.dump(
                {k: sorted(v, key=lambda p: p["number"]) for k, v in merged.items()},
                f,
                indent=1,
                sort_keys=True,
                ensure_ascii=False,
            )
            f.write("\n")

    s = result["summary"]
    print(
        f"scanned={s['scanned']} flagged_unticked_ac={s['flagged_unticked_ac']} "
        f"(all_unticked={s['flagged_all_ac_unticked']}, merged-pr={s['flagged_closed_by_merged_pr']}, "
        f"manual={s['flagged_closed_manually']}, unknown={s['flagged_closed_unknown']}; "
        f"guard_would_have_fired={s['flagged_merged_pr_guard_would_have_fired']}, "
        f"merged_no_keyword={s['flagged_merged_pr_no_keyword']}, "
        f"linked_but_hand_closed={s['flagged_linked_but_hand_closed']}) "
        f"any_unticked={s['any_unticked_box']} clean={s['clean']}"
    )
    print(f"wrote {args.out} and {stem + '.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
