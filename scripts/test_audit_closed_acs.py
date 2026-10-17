#!/usr/bin/env python3
"""Tests for scripts/audit_closed_acs.py (#543 closed-issue AC sweep).

Run: python3 -m pytest scripts/test_audit_closed_acs.py -v

Covers the box parser on fixture bodies (unticked / ticked / nil-strikethrough /
nested / non-AC "Test plan" boxes / fenced code / empty), agreement with the
forward guard's `count_unchecked_acs`, closed-by classification, the --since
filter, sort order, and byte-identical idempotent output from --from-cache.
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
    row = A.audit([_issue(1, TEST_PLAN)])["rows"][0]
    assert row["flagged"] is False


def test_unbolded_ac_is_other():
    c = counts(MIXED_OTHER)
    assert c["ac_total"] == 0
    assert (c["other_unticked"], c["other_total"]) == (2, 3)
    assert c["guard_unticked"] == 0


def test_fenced_code_is_skipped():
    c = counts(FENCED)
    assert (c["ac_unticked"], c["ac_total"]) == (1, 1)


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
    for body in (UNTICKED, TICKED, TEST_PLAN, MIXED_OTHER, EMPTY):
        assert counts(body)["ac_unticked"] == count_unchecked_acs(body), body


def test_documented_divergence_star_and_numbered_bullets():
    """The guard regex only knows `-` bullets; the sweep also reads `*` and `1.`
    boxes. Dash-only nesting agrees; the star/numbered boxes are the delta."""
    dash_only = "\n".join(
        l for l in NESTED.splitlines() if "* [" not in l and "1. [" not in l
    )
    assert counts(dash_only)["ac_unticked"] == count_unchecked_acs(dash_only) == 2
    assert counts(NESTED)["ac_unticked"] == 4 and count_unchecked_acs(NESTED) == 2


def test_documented_divergence_fenced_code():
    """The guard's `count_unchecked_acs` does not strip fenced code (only its
    `closing_refs` does), so a box quoted in a ``` block over-counts there —
    conservative for a guard, but the sweep skips it as documentation."""
    assert counts(FENCED)["ac_unticked"] == 1 and count_unchecked_acs(FENCED) == 2


# ----------------------------------------------------------------------- audit


def _issue(n, body, closed_at="2026-10-01T00:00:00Z", prs=(), reason="COMPLETED"):
    return {
        "number": n,
        "title": f"issue {n} | with pipe",
        "body": body,
        "closedAt": closed_at,
        "url": f"https://github.com/x/y/issues/{n}",
        "stateReason": reason,
        "labels": [{"name": "housekeeping"}],
        "closedByPullRequestsReferences": [
            {
                "number": p,
                "url": f"https://github.com/x/y/pull/{p}",
                "repository": {"name": "y", "owner": {"login": "x"}},
            }
            for p in prs
        ],
    }


FIXTURE = [
    _issue(
        10, UNTICKED, "2026-09-01T00:00:00Z", prs=(11,)
    ),  # flagged, PR, guard catches
    _issue(20, UNTICKED, "2026-09-02T00:00:00Z"),  # flagged, manual
    _issue(30, TICKED, "2026-09-03T00:00:00Z", prs=(31, 32)),  # clean
    _issue(40, TEST_PLAN, "2026-09-04T00:00:00Z"),  # other-only
    _issue(50, NIL, "2026-09-05T00:00:00Z", prs=(51,)),  # not flagged; guard disagrees
    _issue(60, EMPTY, "2026-09-05T00:00:00Z", reason="NOT_PLANNED"),  # clean
]
CROSS = dict(_issue(70, UNTICKED, "2026-09-06T00:00:00Z", prs=(7,)))
CROSS["closedByPullRequestsReferences"][0]["repository"] = {
    "name": "other",
    "owner": {"login": "x"},
}


def test_audit_summary_and_closed_by():
    r = A.audit(FIXTURE, repo="x/y")
    s = r["summary"]
    assert s["scanned"] == 6
    assert s["flagged_unticked_ac"] == 2
    assert s["flagged_closed_by_pr"] == 1
    assert s["flagged_closed_manually"] == 1
    assert s["flagged_pr_guard_would_catch"] == 1
    assert s["any_unticked_box"] == 3
    assert s["other_only_unticked"] == 1
    assert s["clean"] == 3
    assert s["closed_by_pr"] == 3 and s["closed_manually"] == 3
    by_num = {row["number"]: row for row in r["rows"]}
    assert by_num[30]["closing_prs"] == ["#31", "#32"]
    assert by_num[20]["closed_by"] == "manual"
    # nil'd issue #50: not flagged by the sweep, but the guard regex would catch it
    assert by_num[50]["flagged"] is False and by_num[50]["guard_would_catch"] is True


def test_cross_repo_closing_pr_is_qualified():
    row = A.audit([CROSS], repo="x/y")["rows"][0]
    assert row["closed_by"] == "pr" and row["closing_prs"] == ["x/other#7"]
    md = A.render_markdown(A.audit([CROSS], repo="x/y"), "x/y", "2026-10-17")
    assert "PR x/other#7" in md


def test_sort_closed_at_desc_then_number_desc():
    nums = [row["number"] for row in A.audit(FIXTURE)["rows"]]
    assert nums == [60, 50, 40, 30, 20, 10]


def test_since_filter():
    r = A.audit(FIXTURE, since="2026-09-03")
    assert [row["number"] for row in r["rows"]] == [60, 50, 40, 30]
    assert r["summary"]["since"] == "2026-09-03"


def test_markdown_escapes_pipes_and_lists_flagged_rows():
    md = A.render_markdown(A.audit(FIXTURE, repo="x/y"), "x/y", "2026-10-17")
    assert "issue 10 \\| with pipe" in md
    assert "| #10 |" in md and "| #20 |" in md
    assert "PR #11" in md and "| manual |" in md
    assert "| #40 |" in md  # context section
    assert "| #30 |" not in md  # clean rows are not listed


# ----------------------------------------------------------------------- CLI


def test_cli_from_cache_is_idempotent(tmp_path):
    cache = tmp_path / "payload.json"
    cache.write_text(json.dumps(FIXTURE), encoding="utf-8")
    out = tmp_path / "sub" / "report-2026-10-17.md"
    cmd = [
        sys.executable,
        os.path.join(HERE, "audit_closed_acs.py"),
        "--from-cache",
        str(cache),
        "--out",
        str(out),
    ]
    r1 = subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert "scanned=6 flagged_unticked_ac=2" in r1.stdout
    md1 = out.read_bytes()
    js1 = (tmp_path / "sub" / "report-2026-10-17.json").read_bytes()
    subprocess.run(cmd, capture_output=True, text=True, check=True)
    assert out.read_bytes() == md1
    assert (tmp_path / "sub" / "report-2026-10-17.json").read_bytes() == js1
    data = json.loads(js1)
    assert data["report_date"] == "2026-10-17"  # taken from the --out stem
    assert data["summary"]["flagged_unticked_ac"] == 2
    # nothing written outside --out paths
    assert sorted(p.name for p in (tmp_path / "sub").iterdir()) == [
        "report-2026-10-17.json",
        "report-2026-10-17.md",
    ]


def test_cli_rejects_bad_since(tmp_path):
    r = subprocess.run(
        [
            sys.executable,
            os.path.join(HERE, "audit_closed_acs.py"),
            "--from-cache",
            os.devnull,
            "--since",
            "yesterday",
            "--out",
            str(tmp_path / "r.md"),
        ],
        capture_output=True,
        text=True,
    )
    assert r.returncode != 0
    assert "--since must be YYYY-MM-DD" in r.stderr


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
