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


def test_annotation_escapes_percent_and_newline():
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        c._annot("error", "100% done\r\nsecond line")
    assert buf.getvalue() == "::error::100%25 done%0D%0Asecond line\n", buf.getvalue()
    body = "Sign-off required (merge-blocking):\n- [ ] @a — 50% coverage\n"
    r = run(body)
    assert r.returncode == 1 and "50%25 coverage" in r.stdout, r.stdout
    assert "- [ ] @a — 50% coverage" in r.stdout, r.stdout  # human listing unescaped


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


# ---- verdict source: the judge is the BASE copy, never the PR head (arch §I4, PR #780)

import merge_blocking_verdict_source as vs  # noqa: E402

SELECTOR = os.path.join(HERE, "merge_blocking_verdict_source.py")
WORKFLOW = os.path.join(
    os.path.dirname(HERE), ".github", "workflows", "merge-blocking-boxes.yml"
)
TAMPERED_CHECK = (
    "#!/usr/bin/env python3\n"
    "import sys\n"
    "print('unticked=0 ticked=0 nil=0 region=present')\n"
    "sys.exit(0)  # a 'simplified' check that always passes\n"
)


def _tree(root, files):
    """Create `root/scripts/<name>` for each (name, text) pair."""
    os.makedirs(os.path.join(root, "scripts"), exist_ok=True)
    for name, text in files.items():
        with open(os.path.join(root, "scripts", name), "w", encoding="utf-8") as fh:
            fh.write(text)


def _real(name):
    return open(os.path.join(HERE, name), encoding="utf-8").read()


def _run_selector(base, head, env_extra=None):
    env = dict(os.environ)
    env.pop("GITHUB_OUTPUT", None)
    env.update(env_extra or {})
    return subprocess.run(
        [sys.executable, SELECTOR, "--base", base, "--head", head],
        capture_output=True,
        text=True,
        env=env,
    )


def test_verdict_source_prefers_base_when_both_exist():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        both = {
            n: _real(n)
            for n in ("merge_blocking_check.py", "pr_merge_blocking_boxes.py")
        }
        _tree(base, both)
        _tree(head, both)
        assert vs.select(base, head) == ("base", base, [])
        out = os.path.join(d, "gh_out")
        r = _run_selector(base, head, {"GITHUB_OUTPUT": out})
        assert r.returncode == 0, r.stdout + r.stderr
        assert (
            "verdict-source=base" in r.stdout and "::warning::" not in r.stdout
        ), r.stdout
        assert open(out).read() == f"source=base\ndir={base}\n", open(out).read()


def test_verdict_source_bootstraps_to_head_only_when_base_lacks_a_script():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        _tree(base, {"pr_merge_blocking_boxes.py": _real("pr_merge_blocking_boxes.py")})
        _tree(
            head,
            {
                n: _real(n)
                for n in ("merge_blocking_check.py", "pr_merge_blocking_boxes.py")
            },
        )
        src, chosen, missing = vs.select(base, head)
        assert (src, chosen, missing) == (
            "head(bootstrap)",
            head,
            ["scripts/merge_blocking_check.py"],
        )
        r = _run_selector(base, head)
        assert (
            r.returncode == 0 and "verdict-source=head(bootstrap)" in r.stdout
        ), r.stdout
        assert (
            "::warning::" in r.stdout and "scripts/merge_blocking_check.py" in r.stdout
        ), r.stdout


def test_verdict_source_fails_closed_when_neither_can_judge():
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        _tree(base, {})
        _tree(head, {"pr_merge_blocking_boxes.py": _real("pr_merge_blocking_boxes.py")})
        r = _run_selector(base, head)
        assert r.returncode == 1 and "::error::" in r.stdout, r.stdout


def test_head_side_edit_cannot_flip_the_verdict():
    """A PR that 'simplifies' the check to always-pass is still judged by the base copy."""
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        base, head = os.path.join(d, "base"), os.path.join(d, "head")
        _tree(
            base,
            {
                n: _real(n)
                for n in ("merge_blocking_check.py", "pr_merge_blocking_boxes.py")
            },
        )
        _tree(
            head,
            {
                "merge_blocking_check.py": TAMPERED_CHECK,
                "pr_merge_blocking_boxes.py": _real("pr_merge_blocking_boxes.py"),
            },
        )
        src, chosen, _ = vs.select(base, head)
        assert src == "base" and chosen == base
        judge = os.path.join(chosen, "scripts", "merge_blocking_check.py")
        r = subprocess.run(
            [sys.executable, judge], input=ONE_UNTICKED, capture_output=True, text=True
        )
        assert (
            r.returncode == 1 and "::error::unticked merge-blocking box" in r.stdout
        ), r.stdout
        # the tampered head copy WOULD have passed — which is exactly why it must not judge
        tampered = os.path.join(head, "scripts", "merge_blocking_check.py")
        t = subprocess.run(
            [sys.executable, tampered],
            input=ONE_UNTICKED,
            capture_output=True,
            text=True,
        )
        assert t.returncode == 0, t.stdout


def test_workflow_runs_the_verdict_from_the_base_checkout():
    """Wiring guard: the YAML checks out base.sha into base/ and the verdict uses the selected dir."""
    import yaml

    wf = yaml.safe_load(open(WORKFLOW, encoding="utf-8"))
    steps = wf["jobs"]["merge-blocking-boxes"]["steps"]
    base_co = [
        s
        for s in steps
        if s.get("uses", "").startswith("actions/checkout")
        and s.get("with", {}).get("path") == "base"
    ]
    assert len(base_co) == 1, steps
    assert (
        base_co[0]["with"]["ref"] == "${{ github.event.pull_request.base.sha }}"
    ), base_co
    sel = [s for s in steps if s.get("id") == "src"]
    assert len(sel) == 1 and "merge_blocking_verdict_source.py" in sel[0]["run"], steps
    verdict = steps[-1]
    assert "merge_blocking_check.py" in verdict["run"], verdict
    assert (
        verdict["run"]
        .strip()
        .startswith('python3 "$SRC_DIR/scripts/merge_blocking_check.py"')
    ), verdict
    assert verdict["env"]["SRC_DIR"] == "${{ steps.src.outputs.dir }}", verdict
    # no step runs the verdict from a bare head path
    for s in steps:
        run = s.get("run", "")
        assert "python3 scripts/merge_blocking_check.py" not in run, s


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
