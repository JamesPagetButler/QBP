#!/usr/bin/env python3
"""Post-merge backstop: auto-reopen any issue just closed while it still has unchecked ACs.

Layer 2 of the FAULT-S4-004 defence (layer 1 = check_closing_acs.py, a PR-time
guard that can be bypassed if it is not a required check or if a fresh closing
keyword is typed in the squash-merge box at merge time). It is independent of
branch protection: the worst case is an issue is wrongly CLOSED for ~one CI run,
then auto-reopened with a warning.

Two entry modes (both wired in .github/workflows/reopen-falsely-closed.yml):

  --commits-file FILE   (push to master) scan the pushed commit messages for
                        closing keywords; for each referenced issue, reopen iff it
                        is CLOSED/COMPLETED with >=1 unchecked `- [ ] **AC` box.
                        This is the original path and is unchanged.

  --issue N             (issues: closed event; #753) look at WHO closed the issue:
                        the last ClosedEvent's `closer` on the issue timeline
                        (GraphQL). `closer` is one of
                          - null        -> a human clicked Close: EXEMPT, never touched;
                          - PullRequest -> closed by a merged PR (any repo: a sibling
                                           repo saying "Closes JamesPagetButler/QBP#N"
                                           lands here, as does an in-repo PR and a
                                           manual Development-sidebar link);
                          - Commit      -> closed by a commit message (any repo).
                        For a PullRequest / Commit closer the decision depends ONLY
                        on the issue's own state and unchecked-AC count — exactly
                        the in-repo keyword rule — and the reopen comment names the
                        closing repo + PR (or commit). Cross-repo closes never produce
                        a QBP push, so this is the only path that sees them.
                        Residual: a closer in a repo this token cannot read may
                        come back null (-> read as a hand close, logged) or with
                        no repository field (-> still automatic, repo shown as ?).

SAFETY — only ever undoes an automatic close, never fights a deliberate one:
  - a hand close (closer == null) is exempt in --issue mode; in --commits-file
    mode only issues referenced with a closing keyword in THIS push are touched,
  - only if the issue is now CLOSED with stateReason == COMPLETED (NOT_PLANNED is
    a deliberate close and is left alone),
  - only if it still has >=1 unchecked `- [ ] **AC` box,
  - the two modes can both fire on one in-repo close; the reopen is idempotent and
    the comment is deduplicated by a hidden marker newer than the close event.

Offline replay (tests / dry-run without `gh`):
  reopen_falsely_closed.py --replay-json CASE.json
  CASE.json = {"repo": "owner/name", "issue": {number, state, stateReason, body,
  closedAt}, "closed_event": <GraphQL ClosedEvent node or null>, "comments": [...]}
  Implies --dry-run; prints one `DECISION:` line.

Usage:
  reopen_falsely_closed.py --commits-file pushed_commit_messages.txt [--dry-run]
  reopen_falsely_closed.py --issue N [--repo owner/name] [--dry-run]
  reopen_falsely_closed.py --replay-json CASE.json
"""

import argparse
import json
import os
import subprocess
import sys
import time
from typing import Any, Dict, List, Optional

from check_closing_acs import closing_refs, count_unchecked_acs

# Hidden marker on every backstop comment; the --issue path uses it to avoid a
# second comment when the push path already healed the same close.
MARKER = "<!-- fault-s4-004-backstop -->"

# The ClosedEvent's `closer` can lag the `issues: closed` webhook by a moment;
# retry a few times before concluding "no closer" (= hand close, exempt). A hand
# close and a lagging closer look identical on the ClosedEvent (closer: null), so
# the retry is skipped only when the issue has NO linked closing PR at all
# (`closedByPullRequestsReferences.totalCount == 0`) — then nothing can be lagging.
CLOSER_RETRIES = 3
CLOSER_RETRY_SLEEP_S = 5

CLOSED_EVENT_QUERY = (
    "query($owner: String!, $name: String!, $number: Int!) { "
    "repository(owner: $owner, name: $name) { issue(number: $number) { "
    "number state stateReason closedAt body "
    "closedByPullRequestsReferences(first: 1) { totalCount } "
    "timelineItems(last: 1, itemTypes: [CLOSED_EVENT]) { nodes { "
    "... on ClosedEvent { createdAt stateReason actor { login } closer { __typename "
    "... on PullRequest { number merged url repository { nameWithOwner } } "
    "... on Commit { oid url repository { nameWithOwner } "
    "associatedPullRequests(first: 5) { nodes { number merged url "
    "repository { nameWithOwner } } } } } } } } } } }"
)


def gh_json(args: List[str], timeout: int = 60) -> Any:
    out = subprocess.run(["gh", *args], capture_output=True, text=True, timeout=timeout)
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return out.stdout


# --------------------------------------------------------------------- closer logic


def describe_closer(closer: Optional[Dict[str, Any]], repo: str) -> Dict[str, Any]:
    """Normalise a GraphQL `closer` node.

    Returns {kind: manual|pull_request|commit|unknown, repo, number, oid, url,
    cross_repo, label}. `label` is the human form used in the reopen comment, e.g.
    `JamesPagetButler/qbp-systema#1` or `JamesPagetButler/QBP@83bf23b (PR #456)`.
    A closer whose repository field is missing (e.g. not visible to the token) is
    still a PullRequest/Commit — it is NOT demoted to manual; repo is then "?".
    """
    out: Dict[str, Any] = {
        "kind": "manual",
        "repo": "",
        "number": None,
        "oid": "",
        "url": "",
        "cross_repo": False,
        "label": "",
    }
    if not closer:
        return out
    kind = closer.get("__typename")
    c_repo = ((closer.get("repository") or {}).get("nameWithOwner")) or ""
    out["repo"] = c_repo or "?"
    out["url"] = closer.get("url") or ""
    out["cross_repo"] = bool(c_repo) and c_repo.lower() != repo.lower()
    if kind == "PullRequest":
        out["kind"] = "pull_request"
        out["number"] = closer.get("number")
        out["label"] = f"{out['repo']}#{out['number']}"
    elif kind == "Commit":
        out["kind"] = "commit"
        out["oid"] = closer.get("oid") or ""
        prs = [
            p
            for p in ((closer.get("associatedPullRequests") or {}).get("nodes") or [])
            if p and p.get("number") is not None
        ]
        out["label"] = f"{out['repo']}@{out['oid'][:7]}"
        # prefer the merged PR (a commit can sit in an unmerged PR too); label only
        prs.sort(key=lambda p: 0 if p.get("merged") else 1)
        if prs:
            p = prs[0]
            p_repo = ((p.get("repository") or {}).get("nameWithOwner")) or out["repo"]
            out["number"] = p.get("number")
            out["label"] += f" (PR {p_repo}#{p['number']})"
    else:
        # A closer type we do not know. Treat as automatic (it is not a human
        # click — `closer` is null for those) so the AC rule still applies.
        out["kind"] = "unknown"
        out["label"] = f"{out['repo']} ({kind or 'unknown closer'})"
    return out


def decide(issue: Dict[str, Any], closer: Dict[str, Any]) -> Dict[str, Any]:
    """Pure decision for --issue mode. Returns {action: reopen|exempt-manual|no-action,
    reason, n_unmet}."""
    state = issue.get("state")
    reason = issue.get("stateReason")
    n_unmet = count_unchecked_acs(issue.get("body", ""))
    if closer["kind"] == "manual":
        return {
            "action": "exempt-manual",
            "reason": "no closer visible (hand close, or closer not yet materialised / "
            "not readable by this token) — never touched",
            "n_unmet": n_unmet,
        }
    if state != "CLOSED":
        return {
            "action": "no-action",
            "reason": f"state={state} (already open)",
            "n_unmet": n_unmet,
        }
    if reason != "COMPLETED":
        return {
            "action": "no-action",
            "reason": f"stateReason={reason} (deliberate close, not a completion claim)",
            "n_unmet": n_unmet,
        }
    if n_unmet == 0:
        return {"action": "no-action", "reason": "no unchecked ACs", "n_unmet": 0}
    return {
        "action": "reopen",
        "reason": f"CLOSED/COMPLETED with {n_unmet} unchecked AC(s), closed by "
        f"{closer['label']}" + (" [cross-repo]" if closer["cross_repo"] else ""),
        "n_unmet": n_unmet,
    }


def reopen_comment_issue_mode(num: int, n_unmet: int, closer: Dict[str, Any]) -> str:
    if closer["kind"] == "pull_request":
        how = f"merged pull request **{closer['label']}**"
    elif closer["kind"] == "commit":
        how = f"commit **{closer['label']}**"
    else:
        how = f"**{closer['label']}**"
    where = (
        " in **another repository** — the PR-time guard only runs on QBP PRs, so "
        "nothing could fire before the merge"
        if closer["cross_repo"]
        else ""
    )
    return (
        f"## ⚠️ Auto-reopened (FAULT-S4-004 backstop)\n\n"
        f"This issue was closed by {how}{where}, but it still has **{n_unmet} "
        f"unchecked acceptance criterion(a)**. A tracked issue never closes with open "
        f"ACs. Reopened automatically.\n\n"
        f"Use `Refs #{num} (satisfies ACn)` instead of a closing keyword (in any repo — "
        f"`Closes JamesPagetButler/QBP#{num}` from a sibling repo closes this issue just "
        f"the same); close manually once every AC is met and verified.\n{MARKER}"
    )


def already_commented(comments: List[Dict[str, Any]], since: str) -> bool:
    """True if a backstop comment at/after `since` (ISO-8601 Z, lexically comparable)
    already exists — the push path healed this close first."""
    for c in comments or []:
        if MARKER in (c.get("body") or "") and (c.get("createdAt") or "") >= (
            since or ""
        ):
            return True
    return False


def should_retry(node: Dict[str, Any], ev: Optional[Dict[str, Any]]) -> bool:
    """True iff a second look at the timeline could change the answer: the issue is
    still CLOSED, no closer is visible yet, and at least one closing PR is linked
    (so the null closer may be webhook lag rather than a hand close). A hand close
    with no linked PR (the common case) returns False immediately — no sleep."""
    if node.get("state") != "CLOSED":
        return False
    if ev is not None and ev.get("closer"):
        return False
    refs = node.get("closedByPullRequestsReferences") or {}
    return int(refs.get("totalCount") or 0) > 0


def fetch_issue_and_closed_event(repo: str, num: int) -> Optional[Dict[str, Any]]:
    owner, name = repo.split("/", 1)
    data = gh_json(
        [
            "api",
            "graphql",
            "-F",
            f"owner={owner}",
            "-F",
            f"name={name}",
            "-F",
            f"number={num}",
            "-f",
            f"query={CLOSED_EVENT_QUERY}",
        ]
    )
    if not isinstance(data, dict):
        return None
    return ((data.get("data") or {}).get("repository") or {}).get("issue")


def fetch_comments(repo: str, num: int) -> List[Dict[str, Any]]:
    info = gh_json(["issue", "view", str(num), "-R", repo, "--json", "comments"])
    if isinstance(info, dict):
        return list(info.get("comments") or [])
    return []


def run_issue_mode(
    num: int, repo: str, dry_run: bool, retries: int = CLOSER_RETRIES
) -> int:
    node = None
    ev: Optional[Dict[str, Any]] = None
    for attempt in range(max(1, retries)):
        node = fetch_issue_and_closed_event(repo, num)
        if node is None:
            print(f"  #{num}: could not fetch issue/timeline — nothing to do")
            return 0
        nodes = [e for e in ((node.get("timelineItems") or {}).get("nodes") or []) if e]
        ev = nodes[-1] if nodes else None
        if not should_retry(node, ev):
            break
        if attempt + 1 < retries:
            time.sleep(CLOSER_RETRY_SLEEP_S)
    if node is None:
        return 0
    return apply_decision(
        repo, node, ev, fetch_comments(repo, num) if not dry_run else [], dry_run
    )


def apply_decision(
    repo: str,
    issue: Dict[str, Any],
    ev: Optional[Dict[str, Any]],
    comments: List[Dict[str, Any]],
    dry_run: bool,
) -> int:
    num = int(issue.get("number") or 0)
    closer = describe_closer((ev or {}).get("closer"), repo)
    d = decide(issue, closer)
    print(
        f"DECISION: #{num} action={d['action']} closer_kind={closer['kind']} "
        f"closer={closer['label'] or '-'} cross_repo={closer['cross_repo']} "
        f"unchecked_ACs={d['n_unmet']} — {d['reason']}"
    )
    if d["action"] != "reopen":
        return 0
    if dry_run:
        print(f"::warning::(dry-run) would auto-reopen #{num}")
        return 0
    subprocess.run(["gh", "issue", "reopen", str(num), "-R", repo], timeout=60)
    since = (ev or {}).get("createdAt") or issue.get("closedAt") or ""
    if already_commented(comments, since):
        print(
            f"  #{num}: backstop comment already present since {since} — not repeating"
        )
    else:
        subprocess.run(
            [
                "gh",
                "issue",
                "comment",
                str(num),
                "-R",
                repo,
                "--body",
                reopen_comment_issue_mode(num, d["n_unmet"], closer),
            ],
            timeout=60,
        )
    print(f"::warning::auto-reopened #{num} (closed by {closer['label']})")
    return 0


def run_replay(path: str) -> int:
    with open(path, encoding="utf-8") as f:
        case = json.load(f)
    repo = case.get("repo") or "JamesPagetButler/QBP"
    return apply_decision(
        repo,
        case.get("issue") or {},
        case.get("closed_event"),
        case.get("comments") or [],
        dry_run=True,
    )


# ------------------------------------------------------------------ push-mode (orig)


def run_push_mode(commits_file: str, dry_run: bool) -> int:
    try:
        with open(commits_file, encoding="utf-8") as f:
            text = f.read()
    except FileNotFoundError:
        print("no commits file — nothing to do.")
        return 0

    refs = closing_refs(text)
    if not refs:
        print("no closing keywords in pushed commits — nothing to do.")
        return 0

    print(f"closing-keyword refs in this push: {sorted(refs)}")
    reopened = []
    for num in sorted(refs):
        info = gh_json(["issue", "view", str(num), "--json", "state,stateReason,body"])
        if not isinstance(info, dict):
            print(f"  #{num}: could not fetch — skipping")
            continue
        state = info.get("state")
        reason = info.get("stateReason")
        n_unmet = count_unchecked_acs(info.get("body", ""))
        if state == "CLOSED" and reason == "COMPLETED" and n_unmet > 0:
            print(
                f"  #{num}: CLOSED/COMPLETED with {n_unmet} unchecked AC(s) — REOPENING"
            )
            if dry_run:
                reopened.append(num)
                continue
            subprocess.run(["gh", "issue", "reopen", str(num)], timeout=60)
            warn = (
                f"## ⚠️ Auto-reopened (FAULT-S4-004 backstop)\n\n"
                f"This issue was closed by a `close/fix/resolve #{num}` keyword in a just-"
                f"merged commit, but it still has **{n_unmet} unchecked acceptance "
                f"criterion(a)**. A tracked issue never closes with open ACs. Reopened "
                f"automatically. Use `Refs #{num} (satisfies ACn)` instead of a closing "
                f"keyword; close manually once every AC is met and verified.\n{MARKER}"
            )
            subprocess.run(
                ["gh", "issue", "comment", str(num), "--body", warn], timeout=60
            )
            reopened.append(num)
        else:
            print(
                f"  #{num}: state={state} reason={reason} unchecked_ACs={n_unmet} — no action"
            )

    if reopened:
        print(f"::warning::auto-reopened issues with unchecked ACs: {reopened}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--commits-file", help="push mode: pushed commit messages")
    mode.add_argument("--issue", type=int, help="issues:closed mode: issue number")
    mode.add_argument("--replay-json", help="offline replay of one case (dry-run)")
    ap.add_argument(
        "--repo",
        default=os.environ.get("GITHUB_REPOSITORY", "JamesPagetButler/QBP"),
        help="owner/name of THIS repo (default: $GITHUB_REPOSITORY)",
    )
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument(
        "--closer-retries",
        type=int,
        default=CLOSER_RETRIES,
        help="attempts to see a non-null closer before treating the close as manual",
    )
    args = ap.parse_args()

    if args.replay_json:
        return run_replay(args.replay_json)
    if args.issue is not None:
        return run_issue_mode(args.issue, args.repo, args.dry_run, args.closer_retries)
    return run_push_mode(args.commits_file, args.dry_run)
    # backstop never fails the build — it heals, it doesn't block


if __name__ == "__main__":
    sys.exit(main())
