#!/usr/bin/env python3
"""Tests for the FAULT-S4-004 layer-2 backstop (scripts/reopen_falsely_closed.py).

#753: the backstop used to see only closing keywords pushed to QBP master, so a
sibling-repo PR saying "Closes JamesPagetButler/QBP#N" closed a QBP issue with its
ACs unticked and nothing fired. The `--issue` path now reads the issue's last
ClosedEvent `closer` and applies the same unchecked-AC rule to any PullRequest /
Commit closer, from any repository; a null closer (hand close) stays exempt.

No network: every case is replayed offline via `--replay-json` (same decision
code path as the live `--issue` mode minus the fetch) or by importing the pure
functions. Run: python3 scripts/test_reopen_falsely_closed.py
            or python3 -m pytest scripts/test_reopen_falsely_closed.py -v
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
SCRIPT = os.path.join(HERE, "reopen_falsely_closed.py")
WORKFLOW = os.path.join(HERE, "..", ".github", "workflows", "reopen-falsely-closed.yml")
SWEEP_ISSUES = os.path.join(
    HERE, "..", "analysis", "543-closed-ac-sweep", "report-2026-10-17.issues.json"
)

import reopen_falsely_closed as R  # noqa: E402

REPO = "JamesPagetButler/QBP"

# --------------------------------------------------------------------- fixtures

BODY_OPEN_ACS = """## Acceptance Criteria
- [ ] **AC1:** first
- [x] **AC2:** done
- [ ] **AC3:** third
"""
BODY_ALL_TICKED = """## Acceptance Criteria
- [x] **AC1:** first
- [x] **AC2:** done
"""


def pr_closer(repo, number, url=None):
    return {
        "__typename": "PullRequest",
        "number": number,
        "merged": True,
        "url": url or f"https://github.com/{repo}/pull/{number}",
        "repository": {"nameWithOwner": repo},
    }


def commit_closer(repo, oid, pr=None):
    node = {
        "__typename": "Commit",
        "oid": oid,
        "url": f"https://github.com/{repo}/commit/{oid}",
        "repository": {"nameWithOwner": repo},
        "associatedPullRequests": {"nodes": []},
    }
    if pr is not None:
        node["associatedPullRequests"]["nodes"].append(pr_closer(repo, pr))
    return node


def closed_event(closer, at="2026-10-24T00:00:00Z", reason="COMPLETED"):
    return {
        "createdAt": at,
        "stateReason": reason,
        "actor": {"login": "JamesPagetButler"},
        "closer": closer,
    }


def issue(number, body, state="CLOSED", reason="COMPLETED", closed_at=None):
    return {
        "number": number,
        "state": state,
        "stateReason": reason,
        "body": body,
        "closedAt": closed_at or "2026-10-24T00:00:00Z",
    }


# Live ClosedEvent nodes for the three historical cross-repo cases, fetched
# 2026-10-24 via GraphQL `timelineItems(last:1, itemTypes:[CLOSED_EVENT])`
# (issue #753 plan comment). Bodies come from the committed #543 sweep payload.
HISTORICAL = {
    441: closed_event(
        pr_closer("JamesPagetButler/qbp-systema", 1), at="2026-05-22T01:49:56Z"
    ),
    442: closed_event(
        pr_closer("JamesPagetButler/qbp-systema", 3), at="2026-05-22T01:40:54Z"
    ),
    445: closed_event(
        pr_closer("JamesPagetButler/qbp-systema", 2), at="2026-05-22T01:45:06Z"
    ),
    # the one manual-link miss of the sweep: PR #285 linked via the Development
    # sidebar, no keyword in its text — GitHub still records closer = PullRequest.
    22: closed_event(pr_closer(REPO, 285), at="2026-02-13T05:02:59Z"),
}
EXPECTED_LABEL = {
    441: "JamesPagetButler/qbp-systema#1",
    442: "JamesPagetButler/qbp-systema#3",
    445: "JamesPagetButler/qbp-systema#2",
    22: "JamesPagetButler/QBP#285",
}


def sweep_body(number):
    with open(SWEEP_ISSUES, encoding="utf-8") as f:
        for row in json.load(f):
            if row.get("number") == number:
                return row
    raise AssertionError(f"#{number} not in the committed #543 payload")


# ------------------------------------------------------------------- harness


def replay(case):
    """Run the script offline on one case; return (exit, stdout)."""
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "case.json")
        with open(p, "w", encoding="utf-8") as f:
            json.dump(case, f)
        r = subprocess.run(
            [sys.executable, SCRIPT, "--replay-json", p],
            capture_output=True,
            text=True,
        )
        return r.returncode, r.stdout + r.stderr


def decision_line(out):
    for line in out.splitlines():
        if line.startswith("DECISION:"):
            return line
    raise AssertionError(f"no DECISION line in:\n{out}")


def case(num, body, closer, **kw):
    ev_kw = {k: kw.pop(k) for k in ("at",) if k in kw}
    return {
        "repo": REPO,
        "issue": issue(num, body, **kw),
        "closed_event": closed_event(closer, **ev_kw) if closer != "none" else None,
        "comments": [],
    }


# (name, case, expected action, expected substrings in the DECISION line)
CASES = [
    (
        "in-repo PR close with keyword, open ACs → reopen (unchanged behaviour)",
        case(900, BODY_OPEN_ACS, pr_closer(REPO, 901)),
        "reopen",
        ["cross_repo=False", "closer=JamesPagetButler/QBP#901"],
    ),
    (
        "cross-repo PR close, open ACs → reopen, comment names the other repo",
        case(900, BODY_OPEN_ACS, pr_closer("JamesPagetButler/qbp-systema", 7)),
        "reopen",
        ["cross_repo=True", "closer=JamesPagetButler/qbp-systema#7"],
    ),
    (
        "cross-repo COMMIT close (keyword in a squashed commit elsewhere) → reopen",
        case(
            900, BODY_OPEN_ACS, commit_closer("JamesPagetButler/wyrd", "abcdef0123", 12)
        ),
        "reopen",
        ["cross_repo=True", "closer_kind=commit", "JamesPagetButler/wyrd@abcdef0"],
    ),
    (
        "manual close (closer null), open ACs → EXEMPT, no reopen",
        case(900, BODY_OPEN_ACS, None),
        "exempt-manual",
        ["closer_kind=manual", "no closer visible"],
    ),
    (
        "no closed event at all (timeline empty) → treated as manual, exempt",
        case(900, BODY_OPEN_ACS, "none"),
        "exempt-manual",
        [],
    ),
    (
        "cross-repo close, all ACs ticked → no action",
        case(900, BODY_ALL_TICKED, pr_closer("JamesPagetButler/qbp-systema", 7)),
        "no-action",
        ["unchecked_ACs=0"],
    ),
    (
        "cross-repo close, NOT_PLANNED → no action (deliberate close)",
        case(
            900,
            BODY_OPEN_ACS,
            pr_closer("JamesPagetButler/qbp-systema", 7),
            reason="NOT_PLANNED",
        ),
        "no-action",
        ["NOT_PLANNED"],
    ),
    (
        "already OPEN again (push path got there first) → no action",
        case(900, BODY_OPEN_ACS, pr_closer(REPO, 901), state="OPEN", reason=None),
        "no-action",
        ["already open"],
    ),
    (
        "closer with no visible repository field → still automatic, repo '?'",
        case(
            900,
            BODY_OPEN_ACS,
            {"__typename": "PullRequest", "number": 5, "merged": True},
        ),
        "reopen",
        ["closer=?#5", "cross_repo=False"],
    ),
]


def check_case(name, c, exp_action, exp_subs):
    code, out = replay(c)
    line = decision_line(out)
    ok = (
        code == 0
        and f"action={exp_action}" in line
        and all(s in line for s in exp_subs)
    )
    return ok, f"{name}  (exit {code}; {line})"


def test_cases():
    for name, c, exp_action, exp_subs in CASES:
        ok, msg = check_case(name, c, exp_action, exp_subs)
        assert ok, msg


def historical_replay(number):
    row = sweep_body(number)
    c = {
        "repo": REPO,
        "issue": {
            "number": number,
            "state": "CLOSED",
            "stateReason": row.get("stateReason"),
            "body": row.get("body") or "",
            "closedAt": row.get("closedAt"),
        },
        "closed_event": HISTORICAL[number],
        "comments": [],
    }
    code, out = replay(c)
    return code, decision_line(out)


def test_historical_cross_repo_cases_reopen():
    """#441 / #442 / #445: closed by qbp-systema#1 / #3 / #2 with 4/5/4 unticked ACs
    (bodies as of 2026-10-17). Under the new rule each one → REOPEN, cross-repo."""
    for n in (441, 442, 445):
        code, line = historical_replay(n)
        assert code == 0, line
        assert "action=reopen" in line, line
        assert "cross_repo=True" in line, line
        assert f"closer={EXPECTED_LABEL[n]}" in line, line


def test_historical_manual_link_case_is_covered():
    """#22 (sweep's one manual-link miss): closer is PullRequest #285 even though the
    link was made by hand in the sidebar — the closer-based rule covers it."""
    code, line = historical_replay(22)
    assert code == 0 and "action=reopen" in line and "cross_repo=False" in line, line
    assert f"closer={EXPECTED_LABEL[22]}" in line, line


def test_describe_closer_shapes():
    d = R.describe_closer(None, REPO)
    assert d["kind"] == "manual" and not d["cross_repo"]
    d = R.describe_closer(pr_closer("JamesPagetButler/qbp-systema", 1), REPO)
    assert d["kind"] == "pull_request" and d["cross_repo"]
    assert d["label"] == "JamesPagetButler/qbp-systema#1"
    d = R.describe_closer(pr_closer("jamespagetbutler/qbp", 9), REPO)
    assert not d["cross_repo"], "repo comparison must be case-insensitive"
    d = R.describe_closer(commit_closer(REPO, "83bf23b060e6", 456), REPO)
    assert d["kind"] == "commit" and d["number"] == 456
    assert d["label"] == "JamesPagetButler/QBP@83bf23b (PR JamesPagetButler/QBP#456)"
    unmerged = pr_closer(REPO, 1)
    unmerged["merged"] = False
    both = commit_closer(REPO, "deadbeef0000")
    both["associatedPullRequests"]["nodes"] = [unmerged, pr_closer(REPO, 2)]
    d = R.describe_closer(both, REPO)
    assert d["number"] == 2, "label must prefer the MERGED associated PR"
    d = R.describe_closer({"__typename": "Something"}, REPO)
    assert d["kind"] == "unknown", "an unknown non-null closer is NOT a hand close"


def test_decide_is_pure_and_ordered():
    pr = R.describe_closer(pr_closer("JamesPagetButler/qbp-systema", 1), REPO)
    assert R.decide(issue(1, BODY_OPEN_ACS), pr)["action"] == "reopen"
    assert R.decide(issue(1, BODY_ALL_TICKED), pr)["action"] == "no-action"
    assert R.decide(issue(1, BODY_OPEN_ACS, reason="NOT_PLANNED"), pr)["action"] == (
        "no-action"
    )
    assert R.decide(issue(1, BODY_OPEN_ACS, state="OPEN"), pr)["action"] == "no-action"
    manual = R.describe_closer(None, REPO)
    assert R.decide(issue(1, BODY_OPEN_ACS), manual)["action"] == "exempt-manual"


def test_should_retry_only_when_a_closer_could_be_lagging():
    """Gemini SHOULD-FIX (PR #760): a hand close must not burn the retry budget.
    Retry iff CLOSED + no closer yet + >=1 linked closing PR (possible webhook lag)."""
    closed_no_refs = {
        "state": "CLOSED",
        "closedByPullRequestsReferences": {"totalCount": 0},
    }
    closed_refs = {
        "state": "CLOSED",
        "closedByPullRequestsReferences": {"totalCount": 1},
    }
    assert not R.should_retry(
        closed_no_refs, closed_event(None)
    ), "hand close: no retry"
    assert not R.should_retry(closed_no_refs, None), "no event, no refs: no retry"
    assert R.should_retry(
        closed_refs, closed_event(None)
    ), "linked PR, null closer: retry"
    assert R.should_retry(closed_refs, None), "linked PR, no event yet: retry"
    assert not R.should_retry(
        closed_refs, closed_event(pr_closer(REPO, 1))
    ), "closer seen"
    assert not R.should_retry(
        {"state": "OPEN", "closedByPullRequestsReferences": {"totalCount": 1}}, None
    )
    assert not R.should_retry({"state": "CLOSED"}, None), "field absent -> treated as 0"


def test_comment_dedupe_marker():
    since = "2026-10-24T10:00:00Z"
    older = {"body": R.MARKER + " x", "createdAt": "2026-10-24T09:59:59Z"}
    newer = {
        "body": "## Auto-reopened\n" + R.MARKER,
        "createdAt": "2026-10-24T10:00:01Z",
    }
    plain = {"body": "unrelated", "createdAt": "2026-10-24T10:00:01Z"}
    assert not R.already_commented([older, plain], since)
    assert R.already_commented([older, newer], since)
    assert not R.already_commented([], since)


def test_reopen_comment_names_repo_and_pr():
    closer = R.describe_closer(pr_closer("JamesPagetButler/qbp-systema", 1), REPO)
    body = R.reopen_comment_issue_mode(441, 4, closer)
    assert "JamesPagetButler/qbp-systema#1" in body
    assert "another repository" in body
    assert "4 unchecked" in body and R.MARKER in body
    in_repo = R.describe_closer(pr_closer(REPO, 713), REPO)
    assert "another repository" not in R.reopen_comment_issue_mode(711, 1, in_repo)


def test_push_path_unchanged_without_keywords():
    """Push mode: no closing keyword in the pushed commits → nothing to do, exit 0,
    no gh call (the keyword scan is the gate, as before #753)."""
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "commits.txt")
        open(p, "w").write("docs: tidy README\n\nRefs #441 (satisfies AC2)\n")
        r = subprocess.run(
            [sys.executable, SCRIPT, "--commits-file", p, "--dry-run"],
            capture_output=True,
            text=True,
        )
    assert r.returncode == 0 and "no closing keywords" in r.stdout, r.stdout


def test_workflow_wires_both_paths():
    wf = open(WORKFLOW, encoding="utf-8").read()
    assert "issues:" in wf and "types: [closed]" in wf, "issues:closed trigger missing"
    assert "--issue" in wf and "github.event.issue.number" in wf
    assert "--commits-file /tmp/commits.txt" in wf, "push path must stay"
    assert (
        "GITHUB_REPOSITORY:" not in wf
    ), "default GITHUB_* vars must not be overridden"
    assert "branches: [master]" in wf
    assert "issues: write" in wf


def main():
    failures = 0
    for name, c, exp_action, exp_subs in CASES:
        ok, msg = check_case(name, c, exp_action, exp_subs)
        print(f"  [{'PASS' if ok else 'FAIL'}] {msg}")
        failures += not ok
    for fn in (
        test_historical_cross_repo_cases_reopen,
        test_historical_manual_link_case_is_covered,
        test_describe_closer_shapes,
        test_decide_is_pure_and_ordered,
        test_should_retry_only_when_a_closer_could_be_lagging,
        test_comment_dedupe_marker,
        test_reopen_comment_names_repo_and_pr,
        test_push_path_unchanged_without_keywords,
        test_workflow_wires_both_paths,
    ):
        try:
            fn()
            print(f"  [PASS] {fn.__name__}")
        except AssertionError as e:
            print(f"  [FAIL] {fn.__name__}: {e}")
            failures += 1
    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print("\nAll backstop tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
