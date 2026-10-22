#!/usr/bin/env python3
"""Tests for scripts/check_notifier_workflow_list.py (#507 §3).

Run: python3 scripts/test_check_notifier_workflow_list.py
"""

import os
import subprocess
import sys
import tempfile
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_notifier_workflow_list.py")
REPO_WORKFLOWS = os.path.join(HERE, "..", ".github", "workflows")


def write(d, name, text):
    p = os.path.join(d, name)
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(textwrap.dedent(text))
    return p


def notifier(listed):
    if listed:
        wf = "\n".join(f"      - {n}" for n in listed)
        block = "    workflows:\n" + wf
    else:
        block = "    workflows: []"
    return (
        "name: PR check-status notifier\n"
        "on:\n"
        "  workflow_run:\n" + block + "\n    types: [completed]\n"
        "  pull_request:\n"
        "    types: [opened]\n"
        "jobs: {}\n"
    )


def run(d):
    r = subprocess.run(
        [sys.executable, SCRIPT, "--workflows-dir", d],
        capture_output=True,
        text=True,
    )
    return r.returncode, r.stdout + r.stderr


def test_in_sync():
    with tempfile.TemporaryDirectory() as d:
        write(d, "a.yml", "name: Alpha\non:\n  pull_request:\njobs: {}\n")
        write(d, "b.yml", "name: Beta\non: [push, pull_request]\njobs: {}\n")
        write(d, "c.yml", "name: PushOnly\non:\n  push:\njobs: {}\n")  # not required
        write(d, "pr-check-status.yml", notifier(["Alpha", "Beta"]))
        rc, out = run(d)
        assert rc == 0, out
        assert "in sync" in out and "2 PR-triggered" in out, out


def test_missing_pr_workflow_is_drift():
    with tempfile.TemporaryDirectory() as d:
        write(d, "a.yml", "name: Alpha\non:\n  pull_request:\njobs: {}\n")
        write(d, "b.yml", "name: Beta\non:\n  pull_request_target:\njobs: {}\n")
        write(d, "pr-check-status.yml", notifier(["Alpha"]))
        rc, out = run(d)
        assert rc == 1, out
        assert "'Beta' is not in" in out, out
        assert "1 missing, 0 stale" in out, out


def test_push_only_workflow_not_required():
    with tempfile.TemporaryDirectory() as d:
        write(
            d, "c.yml", "name: PushOnly\non:\n  push:\n  workflow_dispatch:\njobs: {}\n"
        )
        write(d, "pr-check-status.yml", notifier([]))
        rc, out = run(d)
        assert rc == 0, out


def test_stale_listed_name_is_drift():
    with tempfile.TemporaryDirectory() as d:
        write(d, "a.yml", "name: Alpha\non:\n  pull_request:\njobs: {}\n")
        write(d, "pr-check-status.yml", notifier(["Alpha", "Ghost"]))
        rc, out = run(d)
        assert rc == 1, out
        assert "'Ghost' matches no workflow" in out, out


def test_notifier_itself_exempt():
    with tempfile.TemporaryDirectory() as d:
        # the notifier has a pull_request trigger but must not be required to list itself
        write(d, "pr-check-status.yml", notifier([]))
        rc, out = run(d)
        assert rc == 0, out


def test_quoted_names_match():
    with tempfile.TemporaryDirectory() as d:
        write(d, "a.yml", 'name: "Link Checker"\non:\n  pull_request:\njobs: {}\n')
        write(d, "pr-check-status.yml", notifier(["Link Checker"]))
        rc, out = run(d)
        assert rc == 0, out


def test_nameless_pr_workflow_is_drift():
    with tempfile.TemporaryDirectory() as d:
        write(d, "anon.yml", "on:\n  pull_request:\njobs: {}\n")
        write(d, "pr-check-status.yml", notifier([]))
        rc, out = run(d)
        assert rc == 1, out
        assert "anon.yml" in out, out


def test_missing_notifier_is_usage_error():
    with tempfile.TemporaryDirectory() as d:
        write(d, "a.yml", "name: Alpha\non:\n  pull_request:\njobs: {}\n")
        rc, out = run(d)
        assert rc == 2, out


def test_live_repo_in_sync():
    """The committed notifier must list every PR-triggered workflow in this repo."""
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
