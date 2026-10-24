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
    assert r == {"ticked": [], "unticked": [], "nil": []}, r


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
    assert "unticked=1 ticked=1 nil=0" in r.stdout, r.stdout
    assert "UNTICKED: @a" in r.stdout, r.stdout
    r2 = subprocess.run(
        [sys.executable, SCRIPT, "--json"], input=body, capture_output=True, text=True
    )
    assert '"unticked": ["@a"]' in r2.stdout, r2.stdout


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
    assert r == {"ticked": [], "unticked": [], "nil": []}, r


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
