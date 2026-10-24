#!/usr/bin/env python3
"""Tests for scripts/audit_closed_acs.py (#543 closed-issue AC sweep).

Run: python3 -m pytest scripts/test_audit_closed_acs.py -v

Covers the box parser on fixture bodies (unticked / ticked / nil-strikethrough /
nested / non-AC "Test plan" boxes / fenced code incl. ~~~ / HTML comments /
empty), agreement with the forward guard's `count_unchecked_acs`, the flag
boundary (exactly one unticked AC flags), close attribution (linked PR vs
merged-PR-within-window vs manual vs unknown, cross-repo closers, keyword half
of the guard), the --since filter, sort order, and byte-identical idempotent
output from --from-cache / --from-merged-cache.
"""

import json
import os
import subprocess
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import audit_closed_acs as A  # noqa: E402
from check_closing_acs import count_unchecked_acs  # noqa: E402

# ----------------------------------------------------------------------- fixtures

UNTICKED = """## Scope
- [ ] **AC1:** Enumerate all closed issues.
- [ ] **AC2:** Count boxes.
- [x] **AC3:** Already done.
"""

ONE_UNTICKED = """## Acceptance criteria
- [x] **AC1:** done
- [ ] **AC2:** the single open one
"""

ALL_UNTICKED = """## Acceptance criteria
- [ ] **AC1:** never ticked
- [ ] **AC2:** never ticked
"""

TICKED = """## Acceptance criteria
- [x] **AC1:** done
- [X] **AC2:** done (capital X)
"""

NIL = """## Acceptance criteria
- [x] **AC1:** done
- [ ] ⊘ ~~**AC2:** obsolete after #700~~
- [ ] **AC3:** ~~superseded~~ ⊘
- [ ] ~~**AC4:** struck through, no ⊘~~
"""

NESTED = """## Acceptance criteria
- [ ] **AC1:** parent
  - [ ] **AC1a:** nested unticked
  - [x] **AC1b:** nested ticked
    * [ ] **AC1c:** deeper, star bullet
1. [ ] **AC2:** numbered list box
"""

TEST_PLAN = """## Acceptance criteria
- [x] **AC1:** shipped

## Test plan
- [ ] run the thing
- [ ] check the output
- [x] CI green
"""

MIXED_OTHER = """Some prose.
- [ ] Documentation updated
- [ ] AC1: not bold, so not an AC box by the guard's convention
- [x] Reviewed
"""

FENCED = """## Acceptance criteria
- [ ] **AC1:** real
```
- [ ] **AC2:** quoted in a code block — documentation, not a box
```
"""

TILDE_FENCED = """## Acceptance criteria
- [ ] **AC1:** real
~~~markdown
- [ ] **AC2:** quoted in a ~~~ fence
~~~
```
- [ ] **AC3:** quoted in a ``` fence
```
"""

HTML_COMMENT = """## Acceptance criteria
- [ ] **AC1:** real
<!--
- [ ] **AC2:** hidden in an HTML comment (template residue)
-->
- [x] **AC3:** done <!-- inline comment -->
"""

EMPTY = ""


# ----------------------------------------------------------------------- parser


def counts(body):
    return A.summarize_boxes(body)


def test_unticked():
    c = counts(UNTICKED)
    assert (c["ac_unticked"], c["ac_total"]) == (2, 3)
    assert c["other_total"] == 0
    assert c["guard_unticked"] == 2


def test_ticked_including_capital_x():
    c = counts(TICKED)
    assert (c["ac_unticked"], c["ac_total"]) == (0, 2)
    assert c["guard_unticked"] == 0


def test_nil_strikethrough_counts_as_resolved():
    boxes = A.parse_boxes(NIL)
    assert [b["nil"] for b in boxes] == [False, True, True, True]
    assert all(b["is_ac"] for b in boxes), "nil markers must not hide the **AC prefix"
    c = counts(NIL)
    assert (c["ac_unticked"], c["ac_total"], c["nil"]) == (0, 4, 3)
    # Documented divergence from the forward guard: the guard's regex does not
    # know the nil convention, so `- [ ] **AC3:** ~~…~~ ⊘` still trips it.
    assert c["guard_unticked"] == count_unchecked_acs(NIL) == 1


def test_nested_boxes_count_like_top_level():
    c = counts(NESTED)
    assert (c["ac_unticked"], c["ac_total"]) == (4, 5)
    headings = {b["heading"] for b in A.parse_boxes(NESTED)}
    assert headings == {"Acceptance criteria"}


def test_test_plan_boxes_are_other_not_ac():
    """#543 AC2 wording: flag on `- [ ] **AC` boxes only. Test-plan boxes are
    reported in the 'other' columns and never flag the issue on their own."""
    c = counts(TEST_PLAN)
    assert (c["ac_unticked"], c["ac_total"]) == (0, 1)
    assert (c["other_unticked"], c["other_total"]) == (2, 3)
    boxes = A.parse_boxes(TEST_PLAN)
    assert [b["heading"] for b in boxes if not b["is_ac"]] == ["Test plan"] * 3
    row = A.audit([_issue(1, TEST_PLAN)], repo="x/y", merged={})["rows"][0]
    assert row["flagged"] is False


def test_unbolded_ac_is_other():
    c = counts(MIXED_OTHER)
    assert c["ac_total"] == 0
    assert (c["other_unticked"], c["other_total"]) == (2, 3)
    assert c["guard_unticked"] == 0


def test_fenced_code_is_skipped():
    c = counts(FENCED)
    assert (c["ac_unticked"], c["ac_total"]) == (1, 1)


def test_tilde_fence_and_mixed_fences_are_skipped():
    c = counts(TILDE_FENCED)
    assert (c["ac_unticked"], c["ac_total"]) == (1, 1)


def test_html_comments_are_stripped():
    c = counts(HTML_COMMENT)
    assert (c["ac_unticked"], c["ac_total"]) == (1, 2)
    assert A.parse_boxes(HTML_COMMENT)[1]["ticked"] is True


def test_empty_and_none_body():
    for body in (EMPTY, None):
        c = counts(body)
        assert c == {
            "ac_total": 0,
            "ac_unticked": 0,
            "other_total": 0,
            "other_unticked": 0,
            "nil": 0,
            "guard_unticked": 0,
        }


def test_agrees_with_forward_guard_on_plain_bodies():
    """Without nil markers the primary AC count equals the guard's count."""
    for body in (
        UNTICKED,
        ONE_UNTICKED,
        ALL_UNTICKED,
        TICKED,
        TEST_PLAN,
        MIXED_OTHER,
        EMPTY,
    ):
        assert counts(body)["ac_unticked"] == count_unchecked_acs(body), body


def test_documented_divergence_star_and_numbered_bullets():
    """The guard regex only knows `-` bullets; the sweep also reads `*` and `1.`
    boxes. Dash-only nesting agrees; the star/numbered boxes are the delta."""
    dash_only = "\n".join(
        l for l in NESTED.splitlines() if "* [" not in l and "1. [" not in l
    )
    assert counts(dash_only)["ac_unticked"] == count_unchecked_acs(dash_only) == 2
    assert counts(NESTED)["ac_unticked"] == 4 and count_unchecked_acs(NESTED) == 2


def test_documented_divergence_fenced_code_and_comments():
    """The guard's `count_unchecked_acs` strips neither fenced code nor HTML
    comments (only its `closing_refs` strips code), so it over-counts there —
    conservative for a guard; the sweep skips them as documentation."""
    assert counts(FENCED)["ac_unticked"] == 1 and count_unchecked_acs(FENCED) == 2
    assert (
        counts(TILDE_FENCED)["ac_unticked"] == 1
        and count_unchecked_acs(TILDE_FENCED) == 3
    )
    assert (
        counts(HTML_COMMENT)["ac_unticked"] == 1
        and count_unchecked_acs(HTML_COMMENT) == 2
    )


# ----------------------------------------------------------------------- fixtures: issues + PRs

REPO = "x/y"
T = "2026-09-10T12:00:00Z"  # a reference close time


def _ref(number, repo=REPO):
    owner, name = repo.split("/")
    return {
        "number": number,
        "url": f"https://github.com/{repo}/pull/{number}",
        "repository": {"name": name, "owner": {"login": owner}},
    }


def _issue(n, body, closed_at=T, linked=(), reason="COMPLETED"):
    """linked: iterable of PR numbers or (repo, number) tuples."""
    refs = []
    for p in linked:
        refs.append(_ref(p[1], p[0]) if isinstance(p, tuple) else _ref(p))
    return {
        "number": n,
        "title": f"issue {n} | with pipe",
        "body": body,
        "closedAt": closed_at,
        "url": f"https://github.com/{REPO}/issues/{n}",
        "stateReason": reason,
        "labels": [{"name": "housekeeping"}],
        "closedByPullRequestsReferences": refs,
    }


def _pr(number, merged_at, closes=(), keyword=True, issue_repo=REPO):
    body = "\n".join(
        (f"Closes #{n}" if keyword else f"Refs #{n} (satisfies AC1)") for n in closes
    )
    return {
        "number": number,
        "title": f"pr {number}",
        "body": body,
        "mergedAt": merged_at,
        "closingIssuesReferences": [_ref(n, issue_repo) for n in closes],
    }


# Six issues, each exercising one attribution path.
ISSUES = [
    # #10 flagged; closed 1 s after PR #11 merged, keyword present -> merged-pr, guard fires
    _issue(10, UNTICKED, "2026-09-01T00:00:01Z", linked=(11,)),
    # #20 flagged; no linked PR, nothing merged -> manual
    _issue(20, UNTICKED, "2026-09-02T00:00:00Z"),
    # #30 clean; two linked PRs, #32 merged 2 s before close -> merged-pr
    _issue(30, TICKED, "2026-09-03T00:00:02Z", linked=(31, 32)),
    # #40 other-only; manual
    _issue(40, TEST_PLAN, "2026-09-04T00:00:00Z"),
    # #50 flagged (one unticked); linked PR #51 merged 8 h LATER -> hand-closed (#236/#237 shape)
    _issue(50, ONE_UNTICKED, "2026-09-05T00:00:00Z", linked=(51,)),
    # #60 flagged (all unticked); PR #61 merged 1 s before, NO keyword (manual link, #22 shape)
    _issue(60, ALL_UNTICKED, "2026-09-05T00:00:00Z", linked=(61,)),
    # #70 flagged; closed by a CROSS-REPO PR x/other#7, 1 s before, keyword present
    _issue(70, UNTICKED, "2026-09-06T00:00:01Z", linked=(("x/other", 7),)),
    # #80 clean, not planned, nil'd body
    _issue(80, NIL, "2026-09-07T00:00:00Z", reason="NOT_PLANNED"),
]

MERGED = {
    REPO: [
        _pr(11, "2026-09-01T00:00:00Z", closes=(10,)),
        _pr(31, "2026-08-20T00:00:00Z", closes=(30,)),  # old, outside window
        _pr(32, "2026-09-03T00:00:00Z", closes=(30,)),
        _pr(51, "2026-09-05T08:00:00Z", closes=(50,)),  # 8 h after the close
        _pr(61, "2026-09-04T23:59:59Z", closes=(60,), keyword=False),
        _pr(99, "2026-09-09T00:00:00Z", closes=()),  # unrelated
    ],
    "x/other": [
        _pr(7, "2026-09-06T00:00:00Z", closes=(70,)),
    ],
}


def _rows(issues=ISSUES, merged=MERGED, **kw):
    r = A.audit(issues, repo=REPO, merged=merged, **kw)
    return r["summary"], {row["number"]: row for row in r["rows"]}


# ----------------------------------------------------------------------- flag boundary (mutant M3)


def test_exactly_one_unticked_ac_flags():
    _s, by = _rows()
    assert by[50]["ac_unticked"] == 1 and by[50]["flagged"] is True
    assert by[30]["flagged"] is False and by[80]["flagged"] is False


def test_all_ac_unticked_signal():
    s, by = _rows()
    assert by[60]["all_ac_unticked"] is True  # 2/2
    assert by[10]["all_ac_unticked"] is False  # 2/3
    assert by[50]["all_ac_unticked"] is False  # 1/2
    assert by[80]["all_ac_unticked"] is False  # 0/4 (nil'd / ticked)
    assert s["flagged_all_ac_unticked"] == 1


# ----------------------------------------------------------------------- attribution


def test_linked_prs_is_reported_separately_from_closer():
    _s, by = _rows()
    assert by[30]["linked_prs"] == ["#31", "#32"]
    assert by[30]["closed_how"] == "merged-pr" and by[30]["closing_pr"] == "#32"
    assert by[30]["merge_delta_s"] == 2
    assert by[20]["linked_prs"] == [] and by[20]["closed_how"] == "manual"


def test_linked_pr_merged_hours_later_is_hand_closed():
    """#236/#237 shape: linkage exists but the issue was closed by hand first."""
    _s, by = _rows()
    assert by[50]["linked_prs"] == ["#51"]
    assert by[50]["closed_how"] == "manual"
    assert by[50]["closing_pr"] == "" and by[50]["merge_delta_s"] is None


def test_merge_window_is_configurable():
    _s, by = _rows(window_s=9 * 3600)
    assert by[50]["closed_how"] == "merged-pr" and by[50]["closing_pr"] == "#51"


def test_cross_repo_closer_is_qualified():
    _s, by = _rows()
    assert by[70]["linked_prs"] == ["x/other#7"]
    assert by[70]["closed_how"] == "merged-pr"
    assert (
        by[70]["closing_pr"] == "x/other#7" and by[70]["closing_pr_repo"] == "x/other"
    )
    assert by[70]["closing_pr_has_keyword"] is True
    assert by[70]["closing_pr_cross_repo"] is True
    # QBP's guard workflow never runs on another repo's PRs
    assert by[70]["guard_would_have_fired"] is False
    assert by[10]["closing_pr_cross_repo"] is False
    assert A.repos_in_linked_prs(ISSUES, REPO) == [REPO, "x/other"]


def test_unknown_attribution_without_merged_payload():
    s, by = _rows(merged=None)
    assert {row["closed_how"] for row in by.values()} == {"unknown"}
    assert by[10]["closing_pr_has_keyword"] is None
    assert by[10]["guard_would_have_fired"] is False
    assert by[10]["body_check_would_trip"] is True
    assert s["flagged_closed_unknown"] == 5 and s["closed_unknown"] == 8


# ----------------------------------------------------------------------- guard halves (AC5, mutant M5)


def test_guard_fires_only_for_merged_pr_with_keyword_and_unticked_body():
    _s, by = _rows()
    # merged-pr + keyword + unticked body
    assert by[10]["closed_how"] == "merged-pr"
    assert by[10]["closing_pr_has_keyword"] is True
    assert by[10]["body_check_would_trip"] is True
    assert by[10]["guard_would_have_fired"] is True
    # merged-pr + keyword, but body clean -> body half false, guard silent
    assert by[30]["closing_pr_has_keyword"] is True
    assert by[30]["body_check_would_trip"] is False
    assert by[30]["guard_would_have_fired"] is False


def test_manual_close_with_unticked_acs_is_not_guard_catchable():
    """Mutant M5: dropping the merged-pr conjunct must fail here."""
    _s, by = _rows()
    assert by[20]["closed_how"] == "manual"
    assert by[20]["body_check_would_trip"] is True
    assert by[20]["guard_would_have_fired"] is False
    assert by[50]["body_check_would_trip"] is True
    assert by[50]["guard_would_have_fired"] is False


def test_merged_pr_without_keyword_is_guard_blind():
    """#22 shape: GitHub closed it on merge via a manual sidebar link; the
    guard scans PR text for a closing keyword and would not have fired."""
    _s, by = _rows()
    assert by[60]["closed_how"] == "merged-pr" and by[60]["closing_pr"] == "#61"
    assert by[60]["closing_pr_has_keyword"] is False
    assert by[60]["body_check_would_trip"] is True
    assert by[60]["guard_would_have_fired"] is False


def test_summary_counts():
    s, _by = _rows()
    assert s["scanned"] == 8
    assert s["flagged_unticked_ac"] == 5  # 10, 20, 50, 60, 70
    assert s["flagged_closed_by_merged_pr"] == 3  # 10, 60, 70
    assert s["flagged_closed_manually"] == 2  # 20, 50
    assert s["flagged_closed_unknown"] == 0
    assert s["flagged_with_linked_pr"] == 4  # 10, 50, 60, 70
    assert s["flagged_linked_but_hand_closed"] == 1  # 50
    assert s["flagged_merged_pr_guard_would_have_fired"] == 1  # 10
    assert s["flagged_merged_pr_no_keyword"] == 1  # 60
    assert s["flagged_merged_pr_cross_repo"] == 1  # 70
    assert s["flagged_body_check_would_trip"] == 5
    assert s["any_unticked_box"] == 6  # + 40
    assert s["other_only_unticked"] == 1
    assert s["clean"] == 2  # 30, 80
    assert s["closed_by_merged_pr"] == 4 and s["closed_manually"] == 4
    assert s["with_linked_pr"] == 5
    assert s["merged_pr_repos"] == sorted([REPO, "x/other"])
    # partitions
    assert (
        s["flagged_closed_by_merged_pr"]
        + s["flagged_closed_manually"]
        + s["flagged_closed_unknown"]
        == s["flagged_unticked_ac"]
    )


# ----------------------------------------------------------------------- ordering / filter / render


def test_sort_closed_at_desc_then_number_desc():
    nums = [row["number"] for row in A.audit(ISSUES, repo=REPO, merged=MERGED)["rows"]]
    assert nums == [80, 70, 60, 50, 40, 30, 20, 10]


def test_since_filter():
    r = A.audit(ISSUES, since="2026-09-05", repo=REPO, merged=MERGED)
    assert [row["number"] for row in r["rows"]] == [80, 70, 60, 50]
    assert r["summary"]["since"] == "2026-09-05"


def test_markdown_render():
    md = A.render_markdown(
        A.audit(ISSUES, repo=REPO, merged=MERGED), REPO, "2026-10-17"
    )
    assert "issue 10 \\| with pipe" in md
    assert "| merged-pr #11 (Δ1s) | #11 | yes (keyword + body) |" in md
    assert "| manual | #51 | n/a (manual) |" in md  # linked but hand-closed
    assert "no — no keyword in PR text (manual link; guard blind)" in md
    assert "merged-pr x/other#7" in md
    assert "no — closing PR is in another repo (guard not installed there)" in md
    assert "| #40 |" in md  # context section
    assert "| #30 |" not in md and "| #80 |" not in md  # clean rows are not listed
    assert "with ALL AC boxes unticked" in md


# ----------------------------------------------------------------------- #739 timeline fallback


def _tl_pr(number, merged_at, repo=REPO, merged=True):
    return {
        "number": number,
        "merged": merged,
        "mergedAt": merged_at,
        "repository": {"nameWithOwner": repo},
    }


def _tl_node(n, closed_at, closer, events_before=()):
    """Raw GraphQL issue node: the LAST closed event carries `closer`
    (None = hand-close; a PullRequest or Commit dict otherwise)."""
    nodes = [
        {
            "createdAt": at,
            "stateReason": "COMPLETED",
            "actor": {"login": "someone"},
            "closer": c,
        }
        for at, c in events_before
    ]
    nodes.append(
        {
            "createdAt": closed_at,
            "stateReason": "COMPLETED",
            "actor": {"login": "someone"},
            "closer": closer,
        }
    )
    return {"number": n, "closedAt": closed_at, "timelineItems": {"nodes": nodes}}


def _commit(oid, prs=()):
    return {
        "__typename": "Commit",
        "oid": oid,
        "committedDate": "2026-09-09T00:00:00Z",
        "associatedPullRequests": {"nodes": list(prs)},
    }


def _pr_closer(number, merged_at, repo=REPO, merged=True):
    return {"__typename": "PullRequest", **_tl_pr(number, merged_at, repo, merged)}


T9 = "2026-09-09T00:00:02Z"  # close time of the timeline fixtures

# Issues with EMPTY closedByPullRequestsReferences that the bulk pass leaves manual.
TL_ISSUES = ISSUES + [
    # #90 flagged; closed via the squash commit of PR #91 (keyword in commit msg only)
    _issue(90, UNTICKED, T9),
    # #100 clean; closer is the merged PR #101 itself
    _issue(100, TICKED, T9),
    # #110 flagged; hand-closed (closer null) — the #668 shape
    _issue(110, ONE_UNTICKED, T9),
    # #120 flagged; closed by a commit pushed straight to master (no PR) — #256 shape
    _issue(120, UNTICKED, T9),
    # #130 flagged; no timeline record at all
    _issue(130, UNTICKED, T9),
    # #140 flagged; timeline event is STALE (8 h off closedAt) -> ignored
    _issue(140, UNTICKED, T9),
    # #150 flagged; closed via a commit whose merged PR is in ANOTHER repo
    _issue(150, UNTICKED, T9),
    # #160 flagged; PR-closed, reopened, then hand-closed (#474 shape): last wins
    _issue(160, UNTICKED, T9),
    # #170 clean; commit whose only associated PR is NOT merged -> commit-only
    _issue(170, TICKED, T9),
    # #180 clean; commit with TWO merged PRs: the one merged nearer closedAt wins
    _issue(180, TICKED, T9),
    # #190 clean; two merged PRs at EQUAL Δ: lower number wins
    _issue(190, TICKED, T9),
    # #200 clean; event exactly --merge-window BEFORE closedAt: accepted (boundary)
    _issue(200, TICKED, T9),
    # #210 clean; event 8 h BEFORE closedAt: stale (sign-insensitive)
    _issue(210, TICKED, T9),
    # #220 clean; closer is a PullRequest that is NOT merged -> unusable record
    _issue(220, TICKED, T9),
]

TL_MERGED = {
    REPO: MERGED[REPO]
    + [
        # #91 does NOT list #90 in closingIssuesReferences and has no keyword in its text
        _pr(91, "2026-09-09T00:00:00Z", closes=(), keyword=False),
        _pr(101, "2026-09-09T00:00:01Z", closes=()),
    ],
    "x/other": MERGED["x/other"],
}

TIMELINE = {
    "90": _tl_node(
        90, T9, _commit("c0ffee0123456789", [_tl_pr(91, "2026-09-09T00:00:00Z")])
    ),
    "100": _tl_node(100, T9, _pr_closer(101, "2026-09-09T00:00:01Z")),
    "110": _tl_node(110, T9, None),
    "120": _tl_node(120, T9, _commit("deadbeef00000000", [])),
    "140": _tl_node(
        140, "2026-09-09T08:00:00Z", _pr_closer(101, "2026-09-09T08:00:00Z")
    ),
    "150": _tl_node(
        150,
        T9,
        _commit("abc1234567890000", [_tl_pr(8, "2026-09-09T00:00:00Z", "x/other")]),
    ),
    "160": _tl_node(
        160,
        T9,
        None,
        events_before=[
            ("2026-09-01T00:00:00Z", _pr_closer(11, "2026-09-01T00:00:00Z"))
        ],
    ),
    "170": _tl_node(
        170,
        T9,
        _commit(
            "0000000000000001", [_tl_pr(171, "2026-09-09T00:00:00Z", merged=False)]
        ),
    ),
    "180": _tl_node(
        180,
        T9,
        _commit(
            "0000000000000002",
            [
                _tl_pr(181, "2026-09-08T00:00:00Z"),  # a day earlier
                _tl_pr(182, "2026-09-09T00:00:01Z"),  # 1 s from the close -> wins
            ],
        ),
    ),
    "190": _tl_node(
        190,
        T9,
        _commit(
            "0000000000000003",
            [_tl_pr(192, "2026-09-09T00:00:02Z"), _tl_pr(191, "2026-09-09T00:00:02Z")],
        ),
    ),
    "200": _tl_node(
        200, "2026-09-08T23:58:02Z", _pr_closer(101, "2026-09-08T23:58:02Z")
    ),
    "210": _tl_node(
        210, "2026-09-08T16:00:02Z", _pr_closer(101, "2026-09-08T16:00:02Z")
    ),
    "220": _tl_node(220, T9, _pr_closer(221, "", merged=False)),
    # a contradicting record for a bulk-attributed row must be ignored
    "10": _tl_node(10, "2026-09-01T00:00:01Z", None),
}


def _tl_rows(timeline=TIMELINE, **kw):
    r = A.audit(TL_ISSUES, repo=REPO, merged=TL_MERGED, timeline=timeline, **kw)
    return r["summary"], {row["number"]: row for row in r["rows"]}


def test_timeline_empty_refs_commit_resolves_to_merged_pr():
    _s, by = _tl_rows()
    r = by[90]
    assert r["linked_prs"] == []  # closedByPullRequestsReferences was empty
    assert r["closed_how"] == "merged-pr" and r["closing_pr"] == "#91"
    assert r["close_source"] == "timeline-commit-pr"
    assert r["close_commit"] == "c0ffee0123456789"
    assert r["closing_pr_repo"] == REPO and r["merge_delta_s"] == 2
    # keyword lived in the commit message, not the PR text -> guard blind
    assert r["closing_pr_has_keyword"] is False
    assert r["guard_would_have_fired"] is False and r["flagged"] is True
    assert "keyword in commit message" in A._guard_cell(r)
    assert "post-merge backstop" in A._guard_cell(r)
    assert A._how_cell(r) == "merged-pr #91 (Δ2s) via commit c0ffee0"


def test_timeline_empty_refs_pr_closer_resolves_to_merged_pr():
    _s, by = _tl_rows()
    r = by[100]
    assert r["closed_how"] == "merged-pr" and r["closing_pr"] == "#101"
    assert r["close_source"] == "timeline-pr" and r["close_commit"] == ""
    assert r["closing_pr_has_keyword"] is False  # #101's text names no issue
    assert A._how_cell(r) == "merged-pr #101 (Δ1s) via timeline"


def test_timeline_empty_refs_no_resolvable_pr_stays_manual():
    _s, by = _tl_rows()
    # hand-close
    assert by[110]["closed_how"] == "manual" and by[110]["close_source"] == "hand"
    assert A._how_cell(by[110]) == "manual (hand)"
    # commit pushed straight to master, no PR
    assert by[120]["closed_how"] == "manual"
    assert by[120]["close_source"] == "timeline-commit-only"
    assert by[120]["close_commit"] == "deadbeef00000000"
    assert A._how_cell(by[120]) == "manual (commit deadbee, no PR)"
    # no timeline record
    assert by[130]["closed_how"] == "manual" and by[130]["close_source"] == "none"
    assert A._how_cell(by[130]) == "manual"
    # stale record (event far from closedAt) is never trusted — and is distinguishable
    assert by[140]["closed_how"] == "manual"
    assert by[140]["close_source"] == "timeline-stale"
    assert A._how_cell(by[140]) == "manual (stale timeline record)"
    for n in (110, 120, 130, 140):
        assert by[n]["closing_pr"] == "" and by[n]["guard_would_have_fired"] is False
        assert A._guard_cell(by[n]) == "n/a (manual)"


def test_timeline_last_closed_event_wins():
    _s, by = _tl_rows()
    # PR-closed, reopened, hand-closed: the final close is manual (#474 shape)
    assert by[160]["closed_how"] == "manual" and by[160]["close_source"] == "hand"


def test_timeline_merged_gating_and_nearest_pr_selection():
    _s, by = _tl_rows()
    # only an UNMERGED associated PR -> not attributed; commit-only
    assert by[170]["closed_how"] == "manual"
    assert by[170]["close_source"] == "timeline-commit-only"
    assert by[170]["closing_pr"] == ""
    # two merged PRs: the one merged nearest closedAt wins
    assert by[180]["closed_how"] == "merged-pr" and by[180]["closing_pr"] == "#182"
    assert by[180]["merge_delta_s"] == 1
    # equal Δ: lower PR number wins (deterministic tie-break)
    assert by[190]["closed_how"] == "merged-pr" and by[190]["closing_pr"] == "#191"
    # a PullRequest closer that is not merged is a present-but-unusable record
    assert by[220]["closed_how"] == "manual"
    assert by[220]["close_source"] == "timeline-unmerged-pr"
    assert A._how_cell(by[220]) == "manual (unmerged PR closer)"


def test_timeline_stale_guard_boundary_and_sign():
    _s, by = _tl_rows()
    # exactly --merge-window (120 s) BEFORE closedAt is still accepted
    assert (
        by[200]["closed_how"] == "merged-pr"
        and by[200]["close_source"] == "timeline-pr"
    )
    # 8 h BEFORE is stale (abs(), not a one-sided check)
    assert (
        by[210]["closed_how"] == "manual"
        and by[210]["close_source"] == "timeline-stale"
    )
    # 8 h AFTER (fixture #140) is stale too
    assert by[140]["close_source"] == "timeline-stale"
    # a tighter window flips the boundary case
    _s2, by2 = _tl_rows(window_s=119)
    assert by2[200]["close_source"] == "timeline-stale"


def _fake_gh(responses):
    """subprocess.run stand-in: pops one canned (stdout, returncode) per call and
    records the argv so the test can check batching and variables."""
    calls = []

    def run(cmd, **_kw):
        calls.append(cmd)
        stdout, rc = responses.pop(0)

        class R:
            pass

        r = R()
        r.stdout = stdout
        r.returncode = rc
        r.stderr = "boom" if rc else ""
        return r

    return run, calls


def test_fetch_closed_events_keys_batching_and_not_found(monkeypatch):
    node5 = _tl_node(5, T9, None)
    batch1 = {"data": {"repository": {"i5": node5, "i7": None}}}
    batch2 = {
        "data": {"repository": {"i999": None}},
        "errors": [
            {
                "type": "NOT_FOUND",
                "path": ["repository", "i999"],
                "message": "Could not resolve to an Issue",
            }
        ],
    }
    run, calls = _fake_gh([(json.dumps(batch1), 0), (json.dumps(batch2), 0)])
    monkeypatch.setattr(A.subprocess, "run", run)
    monkeypatch.setattr(A, "TIMELINE_BATCH", 2)
    out = A.fetch_closed_events("x/y", [7, 5, 999, 5])  # unsorted, duplicate
    assert out == {"5": node5}  # string keys; missing alias absent; NOT_FOUND skipped
    assert len(calls) == 2  # 3 unique numbers / batch 2 -> 2 calls
    assert calls[0][:3] == ["gh", "api", "graphql"]
    assert (
        "owner=x" in calls[0] and "name=y" in calls[0]
    )  # variables, not interpolation
    q = [a for a in calls[0] if a.startswith("query=")][0]
    assert "i5: issue(number: 5)" in q and "i7: issue(number: 7)" in q
    q2 = [a for a in calls[1] if a.startswith("query=")][0]
    assert "i999" not in q and "i999" in q2


def test_fetch_closed_events_hard_error_aborts(monkeypatch):
    err = {"errors": [{"type": "RATE_LIMITED", "message": "API rate limit exceeded"}]}
    run, _calls = _fake_gh([(json.dumps(err), 1)])
    monkeypatch.setattr(A.subprocess, "run", run)
    with pytest.raises(SystemExit) as e:
        A.fetch_closed_events("x/y", [5])
    assert "RATE_LIMITED" in str(e.value)
    run2, _ = _fake_gh([("", 1)])  # gh died with no JSON at all
    monkeypatch.setattr(A.subprocess, "run", run2)
    with pytest.raises(SystemExit) as e2:
        A.fetch_closed_events("x/y", [5])
    assert "boom" in str(e2.value)


def test_timeline_cross_repo_pr_is_qualified():
    _s, by = _tl_rows()
    r = by[150]
    assert r["closed_how"] == "merged-pr" and r["closing_pr"] == "x/other#8"
    assert r["closing_pr_repo"] == "x/other" and r["closing_pr_cross_repo"] is True
    assert r["closing_pr_has_keyword"] is None  # PR not in the merged payload
    assert r["guard_would_have_fired"] is False
    assert "another repo" in A._guard_cell(r)


def test_bulk_attributed_rows_unchanged_by_timeline():
    _s0, without = _rows(issues=TL_ISSUES, merged=TL_MERGED)
    _s1, with_tl = _tl_rows()
    for n in (10, 20, 30, 40, 50, 60, 70, 80):
        a, b = without[n], with_tl[n]
        for k in (
            "closed_how",
            "closing_pr",
            "closing_pr_repo",
            "merge_delta_s",
            "closing_pr_has_keyword",
            "guard_would_have_fired",
            "flagged",
        ):
            assert a[k] == b[k], (n, k)
    # non-empty references + bulk match: pr-window, even with a contradicting record
    assert with_tl[10]["close_source"] == "pr-window"
    assert (
        with_tl[10]["closed_how"] == "merged-pr" and with_tl[10]["closing_pr"] == "#11"
    )
    assert with_tl[30]["close_source"] == "pr-window"
    # bulk-manual rows without a record: `none` (and `hand` is never guessed)
    assert (
        with_tl[20]["close_source"] == "none" and with_tl[50]["close_source"] == "none"
    )
    # without a timeline, nothing is attributed by it
    assert all(r["close_source"] in ("pr-window", "none") for r in without.values())


def test_timeline_not_applied_without_merged_payload():
    r = A.audit(TL_ISSUES, repo=REPO, merged=None, timeline=TIMELINE)
    assert all(row["closed_how"] == "unknown" for row in r["rows"])
    assert all(row["close_source"] == "none" for row in r["rows"])


def test_bulk_manual_numbers_is_the_fallback_set():
    nums = A.bulk_manual_numbers(TL_ISSUES, TL_MERGED, REPO, A.DEFAULT_MERGE_WINDOW_S)
    # #60 is NOT here: PR #61 names it in closingIssuesReferences (bulk pass)
    assert nums == [20, 40, 50, 80] + list(range(90, 230, 10))
    assert A.bulk_manual_numbers(
        TL_ISSUES, TL_MERGED, REPO, A.DEFAULT_MERGE_WINDOW_S, since="2026-09-09"
    ) == list(range(90, 230, 10))


def test_timeline_query_shape():
    q = A._timeline_query([5, 7])
    assert q.startswith(
        "query($owner: String!, $name: String!) { repository(owner: $owner, name: $name) {"
    )
    assert "i5: issue(number: 5)" in q and "i7: issue(number: 7)" in q
    assert "itemTypes: [CLOSED_EVENT]" in q and "associatedPullRequests" in q


def test_timeline_summary_counts():
    s, by = _tl_rows()
    assert s["timeline_used"] is True and s["timeline_records"] == len(TIMELINE)
    assert s["close_source_counts"] == {
        "pr-window": 4,  # 10, 30, 60, 70
        "timeline-pr": 2,  # 100, 200
        "timeline-commit-pr": 4,  # 90, 150, 180, 190
        "timeline-commit-only": 2,  # 120, 170
        "timeline-unmerged-pr": 1,  # 220
        "timeline-stale": 2,  # 140, 210
        "hand": 2,  # 110, 160
        "none": 5,  # 20, 40, 50, 80, 130
    }
    assert s["closed_by_merged_pr"] == 10 and s["closed_manually"] == 12
    assert s["closed_by_merged_pr_via_timeline"] == 6
    assert s["flagged_closed_by_merged_pr_via_timeline"] == 2  # 90, 150 (others clean)
    assert s["closed_by_commit_no_pr"] == 2
    assert s["flagged_merged_pr_keyword_in_commit_only"] == 1  # 90 (150 is cross-repo)
    assert s["flagged_merged_pr_no_keyword"] == 2  # 60 (manual link) + 90
    # the partition still holds
    assert (
        s["closed_by_merged_pr"] + s["closed_manually"] + s["closed_unknown"]
        == s["scanned"]
    )
    s_off, _ = _rows(issues=TL_ISSUES, merged=TL_MERGED)
    assert s_off["timeline_used"] is False and s_off["timeline_records"] == 0
    assert s_off["closed_by_merged_pr"] == 4 and s_off["closed_manually"] == 18


def test_markdown_render_timeline_sections():
    res = A.audit(TL_ISSUES, repo=REPO, merged=TL_MERGED, timeline=TIMELINE)
    md = A.render_markdown(res, REPO, "2026-10-23", note="payload is a replay")
    assert "**Timeline fallback (#739).**" in md
    assert "**Note.** payload is a replay" in md
    assert (
        "| … … of which attributed by the timeline fallback (#739: commit-message keyword) | 2 |"
        in md
    )
    assert "merged-pr #91 (Δ2s) via commit c0ffee0" in md
    assert "manual (commit deadbee, no PR)" in md
    assert (
        "PR-time guard blind; post-merge backstop reopen-falsely-closed.yml covers"
        in md
    )
    assert "manual (stale timeline record)" in md
    md_off = A.render_markdown(
        A.audit(TL_ISSUES, repo=REPO, merged=TL_MERGED), REPO, "2026-10-23"
    )
    assert "**Timeline fallback (#739) not run**" in md_off
    assert "**Note.**" not in md_off


# ----------------------------------------------------------------------- CLI


def _cli(*extra):
    return [sys.executable, os.path.join(HERE, "audit_closed_acs.py"), *extra]


def test_cli_from_caches_is_idempotent(tmp_path):
    cache = tmp_path / "issues.json"
    cache.write_text(json.dumps(ISSUES), encoding="utf-8")
    mcache = tmp_path / "merged.json"
    mcache.write_text(json.dumps(MERGED), encoding="utf-8")
    out = tmp_path / "sub" / "report-2026-10-17.md"
    cmd = _cli(
        "--repo",
        REPO,
        "--from-cache",
        str(cache),
        "--from-merged-cache",
        str(mcache),
        "--out",
        str(out),
    )
    r1 = subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert "scanned=8 flagged_unticked_ac=5" in r1.stdout
    assert "guard_would_have_fired=1" in r1.stdout
    md1 = out.read_bytes()
    js1 = (tmp_path / "sub" / "report-2026-10-17.json").read_bytes()
    subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert out.read_bytes() == md1
    assert (tmp_path / "sub" / "report-2026-10-17.json").read_bytes() == js1
    data = json.loads(js1)
    assert data["report_date"] == "2026-10-17"  # taken from the --out stem
    assert data["summary"]["flagged_closed_by_merged_pr"] == 3
    # nothing written outside --out paths
    assert sorted(p.name for p in (tmp_path / "sub").iterdir()) == [
        "report-2026-10-17.json",
        "report-2026-10-17.md",
    ]


def test_cli_three_caches_is_idempotent_and_reclassifies(tmp_path):
    cache = tmp_path / "issues.json"
    cache.write_text(json.dumps(TL_ISSUES), encoding="utf-8")
    mcache = tmp_path / "merged.json"
    mcache.write_text(json.dumps(TL_MERGED), encoding="utf-8")
    tcache = tmp_path / "timeline.json"
    tcache.write_text(json.dumps(TIMELINE), encoding="utf-8")
    out = tmp_path / "sub" / "report-2026-10-23.md"
    cmd = _cli(
        "--repo",
        REPO,
        "--from-cache",
        str(cache),
        "--from-merged-cache",
        str(mcache),
        "--from-timeline-cache",
        str(tcache),
        "--note",
        "replay note",
        "--out",
        str(out),
    )
    r1 = subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert (
        "timeline=on(records=14, merged_pr_via_timeline=6, commit_no_pr=2)" in r1.stdout
    )
    md1 = out.read_bytes()
    js1 = (tmp_path / "sub" / "report-2026-10-23.json").read_bytes()
    subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert out.read_bytes() == md1
    assert (tmp_path / "sub" / "report-2026-10-23.json").read_bytes() == js1
    data = json.loads(js1)
    assert data["note"] == "replay note" and data["summary"]["timeline_used"] is True
    by = {row["number"]: row for row in data["rows"]}
    assert (
        by[90]["closed_how"] == "merged-pr"
        and by[90]["close_source"] == "timeline-commit-pr"
    )
    assert by[110]["closed_how"] == "manual" and by[110]["close_source"] == "hand"
    assert b"**Note.** replay note" in md1
    # the timeline cache is read, never rewritten, and nothing else is written
    assert json.loads(tcache.read_text(encoding="utf-8")) == TIMELINE
    assert sorted(p.name for p in (tmp_path / "sub").iterdir()) == [
        "report-2026-10-23.json",
        "report-2026-10-23.md",
    ]


def test_cli_replay_without_timeline_cache_leaves_bulk_attribution(tmp_path):
    cache = tmp_path / "issues.json"
    cache.write_text(json.dumps(TL_ISSUES), encoding="utf-8")
    mcache = tmp_path / "merged.json"
    mcache.write_text(json.dumps(TL_MERGED), encoding="utf-8")
    out = tmp_path / "r.md"
    r = subprocess.run(
        _cli(
            "--repo",
            REPO,
            "--from-cache",
            str(cache),
            "--from-merged-cache",
            str(mcache),
            "--out",
            str(out),
        ),
        capture_output=True,
        text=True,
        check=True,
    )
    # no gh call is made (offline replay); the fallback is reported as not run
    assert (
        "timeline=off(records=0, merged_pr_via_timeline=0, commit_no_pr=0)" in r.stdout
    )
    assert "timeline fallback was NOT run" in r.stderr
    data = json.loads((tmp_path / "r.json").read_text(encoding="utf-8"))
    assert data["summary"]["timeline_used"] is False
    by = {row["number"]: row for row in data["rows"]}
    assert by[90]["closed_how"] == "manual" and by[90]["close_source"] == "none"
    assert "**Timeline fallback (#739) not run**" in out.read_text(encoding="utf-8")


def test_cli_issues_only_cache_gives_unknown_attribution(tmp_path):
    cache = tmp_path / "issues.json"
    cache.write_text(json.dumps(ISSUES), encoding="utf-8")
    out = tmp_path / "r.md"
    r = subprocess.run(
        _cli("--repo", REPO, "--from-cache", str(cache), "--out", str(out)),
        capture_output=True,
        text=True,
        check=True,
    )
    assert "unknown=5" in r.stdout
    data = json.loads((tmp_path / "r.json").read_text(encoding="utf-8"))
    assert data["summary"]["closed_unknown"] == 8


def test_cli_rejects_bad_since(tmp_path):
    r = subprocess.run(
        _cli(
            "--from-cache",
            os.devnull,
            "--since",
            "yesterday",
            "--out",
            str(tmp_path / "r.md"),
        ),
        capture_output=True,
        text=True,
    )
    assert r.returncode != 0
    assert "--since must be YYYY-MM-DD" in r.stderr


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
