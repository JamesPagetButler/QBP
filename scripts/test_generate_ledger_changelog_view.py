"""Tests for scripts/generate_ledger_changelog_view.py (QBP#817, beekeeper's
added changelog-view requirement)."""

import json
import os
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generate_ledger_changelog_view as glcv  # noqa: E402
import ledger_fragment as lf  # noqa: E402


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


def test_render_empty(tmp_path):
    _, ledger_path = _init_repo(tmp_path)
    out = glcv.render(ledger_path)
    assert "no merged fragments yet" in out
    assert "6.24.0" in out  # the frozen base is still named


def test_render_acceptance_check(tmp_path):
    """Beekeeper's literal QBP#817 acceptance check: two merges show two new
    consecutive derived versions in merge order, with issue/PR links."""
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    _add_fragment_commit(repo, changes_dir, 100, "first", 900, "first change", ["A"])
    _add_fragment_commit(repo, changes_dir, 101, "second", 901, "second change", ["B"])
    out = glcv.render(ledger_path)
    v25 = out.index("6.25.0")
    v26 = out.index("6.26.0")
    assert v25 < v26  # merge order preserved in the rendered table
    assert "issues/100" in out and "pull/900" in out
    assert "issues/101" in out and "pull/901" in out


def test_render_is_deterministic_for_the_same_state(tmp_path):
    _repo, ledger_path = _init_repo(tmp_path)
    assert glcv.render(ledger_path) == glcv.render(ledger_path)


def test_render_changes_once_a_new_fragment_merges(tmp_path):
    """D1 (qbp-oppenheimer, QBP#817 PR-1 review): this is exactly why the view
    is never committed -- a fresh render legitimately differs the moment a new
    fragment merges, so a `--check`-against-a-committed-copy would fail on
    every later PR for a reason that isn't that PR's own change."""
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    before = glcv.render(ledger_path)
    _add_fragment_commit(repo, changes_dir, 100, "first", 900, "n", ["A"])
    assert glcv.render(ledger_path) != before


def test_step_summary_appends_to_the_env_var_path(tmp_path, monkeypatch):
    _repo, ledger_path = _init_repo(tmp_path)
    summary = tmp_path / "summary.md"
    summary.write_text("PRE-EXISTING CONTENT\n")
    monkeypatch.setattr(glcv, "LEDGER", ledger_path)
    monkeypatch.setenv("GITHUB_STEP_SUMMARY", str(summary))
    monkeypatch.setattr(
        sys, "argv", ["generate_ledger_changelog_view.py", "--step-summary"]
    )
    glcv.main()
    out = summary.read_text()
    assert out.startswith("PRE-EXISTING CONTENT\n")  # appended, not overwritten
    assert "no merged fragments yet" in out


def test_step_summary_without_env_var_refuses(tmp_path, monkeypatch):
    _repo, ledger_path = _init_repo(tmp_path)
    monkeypatch.setattr(glcv, "LEDGER", ledger_path)
    monkeypatch.delenv("GITHUB_STEP_SUMMARY", raising=False)
    monkeypatch.setattr(
        sys, "argv", ["generate_ledger_changelog_view.py", "--step-summary"]
    )
    with pytest.raises(SystemExit, match="GITHUB_STEP_SUMMARY"):
        glcv.main()
