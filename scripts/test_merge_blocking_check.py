#!/usr/bin/env python3
"""Tests for scripts/merge_blocking_check.py (#507 §7 required check — exit codes + output).

Run: python3 scripts/test_merge_blocking_check.py   (also pytest-collectable)
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import merge_blocking_check as c  # noqa: E402

SCRIPT = os.path.join(HERE, "merge_blocking_check.py")

ALL_TICKED = "## §I4 review\nSign-off required (merge-blocking):\n- [x] @a\n- [X] @b\n"
ONE_UNTICKED = (
    "Sign-off required (merge-blocking):\n- [ ] @qbp-architecture — coherence\n"
    "- [x] @cth-implementor — eval-side\nInformational readers (non-blocking):\n"
    "- [ ] @qbp-oppenheimer — theory shape\n"
)
ABSENT = "## Summary\nx\n\n## Test plan\n- [ ] CI green\n- [x] unit tests\n"
NILD = (
    "<!-- merge-blocking -->\n- [x] @a\n- [ ] ~~schema co-sign~~ ⊘ n/a\n"
    "- [ ] ⊘ two-axis\n<!-- /merge-blocking -->\n- [ ] informational\n"
)


def run(body, *flags):
    return subprocess.run(
        [sys.executable, SCRIPT, *flags], input=body, capture_output=True, text=True
    )


def test_all_ticked_passes():
    r = run(ALL_TICKED)
    assert r.returncode == 0, r.stdout
    assert r.stdout.startswith("unticked=0 ticked=2 nil=0 region=present"), r.stdout
    assert "::notice::" in r.stdout and "::error::" not in r.stdout, r.stdout


def test_one_unticked_fails_and_names_the_box():
    r = run(ONE_UNTICKED)
    assert r.returncode == 1, r.stdout
    assert "::error::unticked merge-blocking box: @qbp-architecture — coherence" in (
        r.stdout
    ), r.stdout
    assert "- [ ] @qbp-architecture — coherence" in r.stdout, r.stdout
    assert "@qbp-oppenheimer" not in r.stdout.split("::error::", 1)[1], r.stdout
    assert c.DOC_URL in r.stdout and "⊘-nil" in r.stdout, r.stdout


def test_absent_region_passes_with_warning():
    r = run(ABSENT)
    assert r.returncode == 0, r.stdout
    assert "region=absent" in r.stdout.splitlines()[0], r.stdout
    assert "::warning::" in r.stdout and "::error::" not in r.stdout, r.stdout
    assert "Sign-off required (merge-blocking):" in r.stdout, r.stdout
    assert "<!-- merge-blocking -->" in r.stdout, r.stdout


def test_absent_region_blocks_with_flip():
    r = run(ABSENT, "--absent-blocks")
    assert r.returncode == 1, r.stdout
    assert "::error::" in r.stdout and "::warning::" not in r.stdout, r.stdout


def test_nil_boxes_pass():
    r = run(NILD)
    assert r.returncode == 0, r.stdout
    assert r.stdout.startswith("unticked=0 ticked=1 nil=2 region=present"), r.stdout


def test_empty_body_is_absent_not_fail():
    assert run("").returncode == 0
    assert run("", "--absent-blocks").returncode == 1


def test_mixed_counts_every_unticked_box():
    body = "Sign-off required (merge-blocking):\n- [ ] @a\n- [x] @b\n- [ ] @c\n"
    r = run(body)
    assert r.returncode == 1
    assert r.stdout.count("::error::") == 2, r.stdout
    assert "unticked=2 ticked=1 nil=0 region=present" in r.stdout, r.stdout


def test_unticked_outside_region_does_not_fail():
    body = (
        "Sign-off required (merge-blocking):\n- [x] @a\n\n## Test plan\n- [ ] later\n"
    )
    assert run(body).returncode == 0


def test_annotations_are_single_line():
    body = "Sign-off required (merge-blocking):\n- [ ] @a\n"
    for line in run(body).stdout.splitlines():
        if line.startswith("::"):
            assert "\n" not in line and line.count("::") >= 2, line


def test_body_file_and_unreadable_file():
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(ONE_UNTICKED)
    try:
        assert run("", "--body-file", fh.name).returncode == 1
    finally:
        os.unlink(fh.name)
    r = run("", "--body-file", fh.name)  # now missing
    assert r.returncode == 2 and "::error::" in r.stdout, r.stdout


def test_check_function_parity_with_cli():
    import contextlib
    import io

    for body, want in ((ALL_TICKED, 0), (ONE_UNTICKED, 1), (ABSENT, 0), (NILD, 0)):
        with contextlib.redirect_stdout(io.StringIO()):
            assert c.check(body) == want == run(body).returncode, body


def test_never_edits_anything():
    src = open(SCRIPT, encoding="utf-8").read()
    assert "gh pr edit" not in src and "gh api" not in src
    assert src.count("open(") == 1 and "open(args.body_file" in src


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
