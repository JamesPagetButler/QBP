"""Tests for scripts/ledger_version.py (QBP#817 variant A).

Builds a throwaway git repo per test, since merge order is derived from
`git log`, not from anything inside a fragment file.
"""

import json
import os
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ledger_fragment as lf  # noqa: E402
import ledger_version as lv  # noqa: E402


def _git(repo, *args, env=None):
    full_env = None
    if env:
        full_env = dict(os.environ, **env)
    subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, env=full_env
    )


def _init_repo(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "t@example.com")
    _git(repo, "config", "user.name", "t")
    ledger_dir = repo / "data/ledgerdir"
    ledger_dir.mkdir(parents=True)
    ledger_path = ledger_dir / "ledger.json"
    ledger_path.write_text(
        json.dumps({"version": "6.24.0", "anchors": []}, indent=2) + "\n"
    )
    (repo / ".gitignore").write_text("")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "init")
    return repo, ledger_path


def _add_fragment_commit(
    repo, changes_dir, issue, slug, pr, note, touched_ids, env=None
):
    lf.write_fragment(
        issue=issue,
        slug=slug,
        pr=pr,
        encoder="scripts/x.py",
        note=note,
        touched_ids=touched_ids,
        changes_dir=changes_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", f"merge #{pr}", env=env)


def test_frozen_base_version_reads_the_ledger_field(tmp_path):
    _, ledger_path = _init_repo(tmp_path)
    assert lv.frozen_base_version(ledger_path) == "6.24.0"


def test_bump_minor():
    assert lv.bump_minor("6.24.0", 0) == "6.24.0"
    assert lv.bump_minor("6.24.0", 1) == "6.25.0"
    assert lv.bump_minor("6.24.0", 2) == "6.26.0"


def test_current_version_with_no_fragments_is_the_frozen_base(tmp_path):
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    assert lv.current_version(ledger_path, changes_dir, repo) == "6.24.0"


def test_current_version_bumps_once_per_merged_fragment_in_merge_order(tmp_path):
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    _add_fragment_commit(repo, changes_dir, 100, "first", 900, "first change", ["A"])
    assert lv.current_version(ledger_path, changes_dir, repo) == "6.25.0"
    _add_fragment_commit(repo, changes_dir, 101, "second", 901, "second change", ["B"])
    assert lv.current_version(ledger_path, changes_dir, repo) == "6.26.0"


def test_fragment_versions_acceptance_check(tmp_path):
    """The beekeeper's literal acceptance check on QBP#817: after two merges it
    shows 6.25.0 and 6.26.0 IN ORDER, with issue/PR links, and neither PR's
    diff touched this view (we never write to the view here at all)."""
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    _add_fragment_commit(repo, changes_dir, 100, "first", 900, "first change", ["A"])
    _add_fragment_commit(repo, changes_dir, 101, "second", 901, "second change", ["B"])
    rows = lv.fragment_versions(ledger_path, changes_dir, repo)
    assert [r["derived_version"] for r in rows] == ["6.25.0", "6.26.0"]
    assert [r["data"]["issue"] for r in rows] == [100, 101]
    assert [r["data"]["pr"] for r in rows] == [900, 901]


def test_fragment_versions_orders_by_commit_not_filename(tmp_path):
    """A fragment named to sort alphabetically AFTER another must still land in
    true merge (commit) order, not filename order."""
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    _add_fragment_commit(
        repo, changes_dir, 999, "zzz-later-alphabetically", 900, "n1", ["A"]
    )
    _add_fragment_commit(
        repo, changes_dir, 1, "aaa-earlier-alphabetically", 901, "n2", ["B"]
    )
    rows = lv.fragment_versions(ledger_path, changes_dir, repo)
    # commit order (999 first, 1 second), NOT alphabetical filename order
    assert [r["data"]["issue"] for r in rows] == [999, 1]
    assert [r["derived_version"] for r in rows] == ["6.25.0", "6.26.0"]


def test_true_merge_commit_does_not_renumber_an_already_issued_version(tmp_path):
    """D2 (qbp-oppenheimer, QBP#817 PR-1 review, 2026-11-17), reproduced exactly
    as described: branch X commits its fragment (and is authored) BEFORE branch
    Y's, but Y actually merges to master FIRST and X merges SECOND. Plain `git
    log --reverse` orders by each fragment commit's own date (X, then Y) — X
    would get B+1 and Y B+2, even though Y was the one that landed on master
    first and was ALREADY ISSUED B+1 before X ever merged. `--first-parent -m`
    must walk true master arrival order (Y, then X), so Y keeps B+1 and X gets
    B+2 — a derived version must never move after it's merged."""
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"

    _git(repo, "checkout", "-q", "-b", "branchX")
    _add_fragment_commit(
        repo,
        changes_dir,
        100,
        "fragment-x",
        900,
        "x",
        ["X"],
        env={
            "GIT_AUTHOR_DATE": "2026-11-02T00:00:00",
            "GIT_COMMITTER_DATE": "2026-11-02T00:00:00",
        },
    )

    _git(repo, "checkout", "-q", "master")
    _git(repo, "checkout", "-q", "-b", "branchY")
    _add_fragment_commit(
        repo,
        changes_dir,
        101,
        "fragment-y",
        901,
        "y",
        ["Y"],
        env={
            "GIT_AUTHOR_DATE": "2026-11-03T00:00:00",
            "GIT_COMMITTER_DATE": "2026-11-03T00:00:00",
        },
    )

    # Y merges to master FIRST (2026-11-04), despite being authored AFTER X.
    _git(repo, "checkout", "-q", "master")
    _git(
        repo,
        "merge",
        "--no-ff",
        "-q",
        "branchY",
        "-m",
        "merge y",
        env={
            "GIT_AUTHOR_DATE": "2026-11-04T00:00:00",
            "GIT_COMMITTER_DATE": "2026-11-04T00:00:00",
        },
    )

    # X merges SECOND (2026-11-05), even though its own commit is dated earlier.
    _git(
        repo,
        "merge",
        "--no-ff",
        "-q",
        "branchX",
        "-m",
        "merge x",
        env={
            "GIT_AUTHOR_DATE": "2026-11-05T00:00:00",
            "GIT_COMMITTER_DATE": "2026-11-05T00:00:00",
        },
    )

    rows = lv.fragment_versions(ledger_path, changes_dir, repo)
    # Y merged first -> B+1; X merged second -> B+2. Y's commit date is LATER
    # than X's, so this only passes under true first-parent merge order.
    assert [r["data"]["issue"] for r in rows] == [101, 100]
    assert [r["derived_version"] for r in rows] == ["6.25.0", "6.26.0"]
