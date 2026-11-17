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


def _git(repo, *args):
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


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


def _add_fragment_commit(repo, changes_dir, issue, slug, pr, note, touched_ids):
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
    _git(repo, "commit", "-q", "-m", f"merge #{pr}")


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
