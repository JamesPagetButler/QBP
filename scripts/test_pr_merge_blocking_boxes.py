#!/usr/bin/env python3
"""Tests for scripts/pr_merge_blocking_boxes.py (#507 §4/§7, §2.2 contract).

Run: python3 scripts/test_pr_merge_blocking_boxes.py
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pr_merge_blocking_boxes as m  # noqa: E402

SCRIPT = os.path.join(HERE, "pr_merge_blocking_boxes.py")


def test_canonical_s22_block():
    body = """## §I4 review
Sign-off required (merge-blocking):
- [ ] @qbp-architecture — coherence
- [x] @cth-implementor — eval-side
Informational readers (non-blocking):
- [ ] @qbp-oppenheimer — theory shape
"""
    r = m.parse(body)
    assert r["unticked"] == ["@qbp-architecture — coherence"], r
    assert r["ticked"] == ["@cth-implementor — eval-side"], r


def test_sentinel_region_and_close():
    body = """Reviewers
<!-- merge-blocking -->
- [ ] @a sign
- [x] @b sign
<!-- /merge-blocking -->
- [ ] informational thing
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a sign"], r
    assert r["ticked"] == ["@b sign"], r


def test_heading_ends_region():
    body = """Sign-off required (merge-blocking):
- [ ] @a

## Test Plan
- [ ] Formal proofs pass
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a"], r


def test_blank_then_prose_ends_region():
    body = """Sign-off required (merge-blocking):
- [ ] @a

Some prose paragraph here.
- [ ] not counted: outside the region
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a"], r


def test_nil_boxes_not_counted_as_unticked():
    body = """Sign-off required (merge-blocking):
- [ ] ~~schema-axis co-sign~~ ⊘ n/a
- [ ] ⊘ two-axis
- [ ] @a real one
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a real one"], r
    assert len(r["nil"]) == 2, r


def test_outside_region_ignored():
    body = """## Verification
- [ ] Lean proofs compile
- [ ] Physical interpretation validated
## Checklist
- [ ] Theory aligns with QBP axioms
"""
    r = m.parse(body)
    assert r == {"ticked": [], "unticked": [], "nil": [], "region": "absent"}, r


def test_code_fence_ignored():
    body = """Sign-off required (merge-blocking):
```
- [ ] inside a code block, not a box
```
- [ ] @a
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a"], r


def test_informational_word_in_box_text_does_not_close_region():
    body = """Sign-off required (merge-blocking):
- [ ] @a — includes informational notes
- [ ] @b
"""
    r = m.parse(body)
    assert r["unticked"] == ["@a — includes informational notes", "@b"], r


def test_cli_output():
    body = "Sign-off required (merge-blocking):\n- [ ] @a\n- [x] @b\n"
    r = subprocess.run(
        [sys.executable, SCRIPT], input=body, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr
    assert "unticked=1 ticked=1 nil=0 region=present" in r.stdout, r.stdout
    assert r.stdout.startswith("unticked=1 "), r.stdout  # first-line contract
    assert "UNTICKED: @a" in r.stdout, r.stdout
    r2 = subprocess.run(
        [sys.executable, SCRIPT, "--json"], input=body, capture_output=True, text=True
    )
    assert '"unticked": ["@a"]' in r2.stdout, r2.stdout
    assert '"region": "present"' in r2.stdout, r2.stdout


def test_never_edits_anything():
    """The parser has no write path: the module exposes parse/main only, and main only prints."""
    src = open(SCRIPT, encoding="utf-8").read()
    assert "gh pr edit" not in src and "open(" not in src.replace(
        "open(args.body_file", ""
    )


# ── Red Team round 1 (PR #731) regression cases ───────────────────────────────
def test_heading_form_opener_counts_boxes():  # G1 (BLOCKING)
    body = "## Sign-off required (merge-blocking)\n- [ ] @a\n- [x] @b\n\n## Informational\n- [ ] @c\n"
    r = m.parse(body)
    assert r["unticked"] == ["@a"] and r["ticked"] == ["@b"], r


def test_prose_mention_does_not_open_region():  # G2
    body = "Not merge-blocking: FYI.\n- [ ] informational\nThis is not merge-blocking either.\n- [ ] also informational\n"
    r = m.parse(body)
    assert r == {"ticked": [], "unticked": [], "nil": [], "region": "absent"}, r


def test_bold_label_line_opens_region():  # G2 (label forms)
    body = "**Merge-blocking:**\n- [ ] @a\n"
    assert m.parse(body)["unticked"] == ["@a"]


def test_struck_fragment_in_live_ask_stays_unticked():  # G3
    body = "Sign-off required (merge-blocking):\n- [ ] @a — ~~old~~ still owed\n- [ ] ~~whole option struck~~\n- [ ] ~~x~~ ⊘ reason\n"
    r = m.parse(body)
    assert r["unticked"] == ["@a — ~~old~~ still owed"], r
    assert len(r["nil"]) == 2, r


def test_sign_off_spelling_variants():
    for label in (
        "Sign off required:",
        "Signoff required:",
        "Sign-off required (merge-blocking):",
    ):
        assert m.parse(label + "\n- [ ] @a\n")["unticked"] == ["@a"], label


def test_heading_informational_closes_region():
    body = "## Sign-off required (merge-blocking)\n- [ ] @a\n## Informational readers (non-blocking)\n- [ ] @b\n"
    assert m.parse(body)["unticked"] == ["@a"]


# ── qbp-architecture §I4 concern (PR #731 @ b045a28): no-region case must FAIL CLOSED ──
def test_no_region_reports_absent():
    """A body using neither §2.2 form: unticked=0 is NOT "nothing owed" — region=absent."""
    body = """## Summary
Some change.

## Test plan
- [ ] CI green
- [x] unit tests
"""
    r = m.parse(body)
    assert r["region"] == "absent", r
    assert r["unticked"] == [] and r["ticked"] == [], r


def test_empty_body_reports_absent():
    assert m.parse("")["region"] == "absent"


def test_label_form_reports_present():
    body = "Sign-off required (merge-blocking):\n- [x] @a\n"
    r = m.parse(body)
    assert r["region"] == "present" and r["unticked"] == [], r


def test_heading_form_reports_present():
    assert (
        m.parse("## Sign-off required (merge-blocking)\n- [x] @a\n")["region"]
        == "present"
    )


def test_sentinel_form_reports_present():
    body = "<!-- merge-blocking -->\n- [x] @a\n<!-- /merge-blocking -->\n"
    r = m.parse(body)
    assert r["region"] == "present" and r["unticked"] == [], r


def test_present_even_when_region_holds_no_boxes():
    """An opener with nothing under it is still an assessable (empty) region."""
    assert (
        m.parse("Sign-off required (merge-blocking):\n\nnothing here\n")["region"]
        == "present"
    )


def test_other_shape_reviewer_boxes_are_absent_and_not_counted():
    """inter-style boxes (`- [ ] **§I4 @seat** (sign-off required)`) are NOT a §2.2 region:
    region=absent, and they are neither ticked-off nor counted as unticked."""
    body = """## Reviewers
- [ ] **§I4 @qbp-architecture** (sign-off required)
- [x] **§I4 @cth-implementor** (sign-off required)
- [ ] merge-blocking: @herschel
"""
    r = m.parse(body)
    assert r == {"ticked": [], "unticked": [], "nil": [], "region": "absent"}, r


def test_prose_mention_is_absent():
    """A prose sentence mentioning the words opens nothing and leaves region=absent (G2)."""
    assert m.parse("This is not merge-blocking.\n- [ ] x\n")["region"] == "absent"


def test_cli_region_absent_line():
    r = subprocess.run(
        [sys.executable, SCRIPT],
        input="- [ ] **§I4 @a** (sign-off required)\n",
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stderr
    assert (
        r.stdout.splitlines()[0] == "unticked=0 ticked=0 nil=0 region=absent"
    ), r.stdout
    r2 = subprocess.run(
        [sys.executable, SCRIPT, "--json"], input="", capture_output=True, text=True
    )
    assert '"region": "absent"' in r2.stdout, r2.stdout


def test_backticked_sentinel_mention_does_not_open_region():
    """A PR that DOCUMENTS the sentinel (in an inline code span) has no real region:
    region=absent, and following boxes are not counted (found on #731's own body)."""
    body = """| §4 | use the `<!-- merge-blocking -->` sentinel or `<!-- /merge-blocking -->` |
- [ ] not a sign-off box
"""
    r = m.parse(body)
    assert r == {"ticked": [], "unticked": [], "nil": [], "region": "absent"}, r


def test_sentinel_at_end_of_prose_line_still_opens():
    body = "Reviewers <!-- merge-blocking -->\n- [ ] @a\n"
    r = m.parse(body)
    assert r["region"] == "present" and r["unticked"] == ["@a"], r


def test_backticked_close_sentinel_does_not_close_region():
    body = "<!-- merge-blocking -->\n- [ ] @a — see `<!-- /merge-blocking -->` docs\n- [ ] @b\n"
    assert m.parse(body)["unticked"] == [
        "@a — see `<!-- /merge-blocking -->` docs",
        "@b",
    ]


if __name__ == "__main__":
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failed = 0
    for t in tests:
        try:
            t()
            print(f"PASS {t.__name__}")
        except AssertionError as e:
            failed += 1
            print(f"FAIL {t.__name__}: {e}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    sys.exit(1 if failed else 0)
