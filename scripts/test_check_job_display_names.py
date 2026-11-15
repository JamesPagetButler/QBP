#!/usr/bin/env python3
"""Tests for scripts/check_job_display_names.py (#757 AC2).

Run: python3 scripts/test_check_job_display_names.py   (or under pytest)
"""

import os
import subprocess
import sys
import tempfile
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_job_display_names.py")
REPO_WORKFLOWS = os.path.join(HERE, "..", ".github", "workflows")


def write(d, name, text):
    p = os.path.join(d, name)
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(textwrap.dedent(text))
    return p


def run(d):
    r = subprocess.run(
        [sys.executable, SCRIPT, "--workflows-dir", d],
        capture_output=True,
        text=True,
    )
    return r.returncode, r.stdout + r.stderr


def test_in_sync():
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  pull_request:\njobs:\n  build:\n    runs-on: x\n",
        )
        write(
            d,
            "b.yml",
            "name: Beta\non: [push]\njobs:\n  build:\n    name: Beta build\n    runs-on: x\n",
        )
        write(
            d, "c.yaml", "name: Gamma\non:\n  push:\njobs:\n  test:\n    runs-on: x\n"
        )
        rc, out = run(d)
        assert rc == 0, out
        assert "unique" in out and "3 jobs in 3 workflow files" in out, out


def test_cross_workflow_id_collision():
    """Two workflows, same job id, no name: → one display name, must fail."""
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  pull_request:\njobs:\n  validate:\n    runs-on: x\n",
        )
        write(
            d,
            "b.yml",
            "name: Beta\non:\n  pull_request:\njobs:\n  validate:\n    runs-on: x\n",
        )
        rc, out = run(d)
        assert rc == 1, out
        assert "'validate' is defined 2 times" in out, out
        assert (
            "a.yml (Alpha) job `validate`" in out
            and "b.yml (Beta) job `validate`" in out
        ), out
        assert "COLLIDE: 1 name(s)" in out, out


def test_cross_workflow_name_vs_id_collision():
    """A `name:` in one workflow equal to a bare job id in another also collides."""
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  pull_request:\njobs:\n  lint:\n    runs-on: x\n",
        )
        write(
            d,
            "b.yml",
            "name: Beta\non:\n  pull_request:\njobs:\n  check:\n    name: lint\n    runs-on: x\n",
        )
        rc, out = run(d)
        assert rc == 1, out
        assert "'lint' is defined 2 times" in out, out


def test_same_workflow_name_collision():
    """Two job ids in ONE workflow rendering to the same `name:` must fail too."""
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            """\
            name: Alpha
            on:
              pull_request:
            jobs:
              one:
                name: Same thing
                runs-on: x
              two:
                name: Same thing
                runs-on: x
            """,
        )
        rc, out = run(d)
        assert rc == 1, out
        assert "'Same thing' is defined 2 times" in out, out
        assert "job `one`" in out and "job `two`" in out, out


def test_name_override_resolves_collision():
    """The #757 fix shape: same job id in two workflows, each with a distinct name:."""
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  pull_request:\njobs:\n  typecheck:\n    name: Alpha typecheck\n    runs-on: x\n",
        )
        write(
            d,
            "b.yml",
            "name: Beta\non:\n  pull_request:\njobs:\n  typecheck:\n    name: Beta typecheck\n    runs-on: x\n",
        )
        rc, out = run(d)
        assert rc == 0, out


def test_matrix_base_name_compared():
    """Matrix jobs render as `name (values)`; the lint compares the base name only."""
    with tempfile.TemporaryDirectory() as d:
        matrix = """\
            name: {wf}
            on:
              pull_request:
            jobs:
              test:
                name: Run tests
                runs-on: x
                strategy:
                  matrix:
                    py: ['3.10', '3.11']
            """
        write(d, "a.yml", matrix.format(wf="Alpha"))
        write(d, "b.yml", matrix.format(wf="Beta"))
        rc, out = run(d)
        assert rc == 1, out
        assert "'Run tests' is defined 2 times" in out, out
    with tempfile.TemporaryDirectory() as d:
        # a single matrix job is fine (its own expansions are not a repo-wide collision)
        write(d, "a.yml", matrix.format(wf="Alpha"))
        rc, out = run(d)
        assert rc == 0, out


def test_bare_on_parsed_as_true():
    """PyYAML parses bare `on:` as the boolean True; the file must still be read."""
    with tempfile.TemporaryDirectory() as d:
        write(
            d, "a.yml", "name: Alpha\non:\n  push:\njobs:\n  build:\n    runs-on: x\n"
        )
        write(
            d, "b.yml", "name: Beta\n'on':\n  push:\njobs:\n  build:\n    runs-on: x\n"
        )
        rc, out = run(d)
        assert rc == 1, out  # both files read → the two `build` ids collide
        assert "'build' is defined 2 times" in out, out


def test_empty_name_falls_back_to_id():
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  push:\njobs:\n  build:\n    name: ''\n    runs-on: x\n",
        )
        write(d, "b.yml", "name: Beta\non:\n  push:\njobs:\n  build:\n    runs-on: x\n")
        rc, out = run(d)
        assert rc == 1, out
        assert "'build' is defined 2 times" in out, out


def test_yaml_parse_error_is_exit_2():
    with tempfile.TemporaryDirectory() as d:
        write(
            d, "a.yml", "name: Alpha\non:\n  push:\njobs:\n  build:\n    runs-on: x\n"
        )
        write(d, "bad.yml", "name: Broken\non: [\njobs: {}\n")
        rc, out = run(d)
        assert rc == 2, out
        assert "YAML parse error" in out, out


def test_missing_dir_is_usage_error():
    with tempfile.TemporaryDirectory() as d:
        r = subprocess.run(
            [sys.executable, SCRIPT, "--workflows-dir", os.path.join(d, "nope")],
            capture_output=True,
            text=True,
        )
        assert r.returncode == 2, r.stdout + r.stderr


def test_no_jobs_is_usage_error():
    with tempfile.TemporaryDirectory() as d:
        write(d, "a.yml", "name: Alpha\non:\n  push:\n")
        rc, out = run(d)
        assert rc == 2, out
        assert "no workflow jobs found" in out, out


def test_reusable_workflow_uses_job():
    """A `uses:` job (reusable-workflow call, no runs-on/steps) follows the same rule."""
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  pull_request:\njobs:\n  shared:\n    uses: org/repo/.github/workflows/x.yml@main\n",
        )
        write(
            d,
            "b.yml",
            "name: Beta\non:\n  pull_request:\njobs:\n  shared:\n    uses: org/repo/.github/workflows/y.yml@main\n",
        )
        rc, out = run(d)
        assert rc == 1, out  # same job id, no name: → collision, not a crash
        assert "'shared' is defined 2 times" in out, out
    with tempfile.TemporaryDirectory() as d:
        write(
            d,
            "a.yml",
            "name: Alpha\non:\n  pull_request:\njobs:\n  shared:\n    name: Alpha shared\n    uses: org/repo/.github/workflows/x.yml@main\n",
        )
        write(
            d,
            "b.yml",
            "name: Beta\non:\n  pull_request:\njobs:\n  shared:\n    uses: org/repo/.github/workflows/y.yml@main\n",
        )
        rc, out = run(d)
        assert rc == 0, out


def test_expression_name_compared_literally():
    """`name:` with a `${{ }}` expression is compared as its literal template, never evaluated."""
    with tempfile.TemporaryDirectory() as d:
        expr = """\
            name: {wf}
            on:
              pull_request:
            jobs:
              t:
                name: Lint ${{{{ matrix.os }}}}
                runs-on: x
                strategy:
                  matrix:
                    os: [ubuntu, macos]
            """
        write(d, "a.yml", expr.format(wf="Alpha"))
        write(d, "b.yml", expr.format(wf="Beta"))
        rc, out = run(d)
        assert rc == 1, out
        assert "'Lint ${{ matrix.os }}' is defined 2 times" in out, out
    with tempfile.TemporaryDirectory() as d:
        # two DIFFERENT templates are distinct base names (documented limit: the
        # lint does not evaluate expressions, so render-time equality is not seen)
        write(d, "a.yml", expr.format(wf="Alpha"))
        write(d, "b.yml", expr.format(wf="Beta").replace("matrix.os", "matrix.py"))
        rc, out = run(d)
        assert rc == 0, out


def test_live_repo_in_sync():
    """Every job display name in this repo's .github/workflows must be unique (#757 AC1)."""
    r = subprocess.run(
        [sys.executable, SCRIPT, "--workflows-dir", REPO_WORKFLOWS],
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stdout + r.stderr


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
