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


def test_check_mode_passes_on_fresh_write(tmp_path):
    _repo, ledger_path = _init_repo(tmp_path)
    out_md = tmp_path / "view.md"
    rendered = glcv.render(ledger_path)
    out_md.write_text(rendered)
    assert out_md.read_text() == glcv.render(ledger_path)


def test_check_mode_detects_drift(tmp_path):
    repo, ledger_path = _init_repo(tmp_path)
    changes_dir = repo / "data/ledgerdir/changes.d"
    out_md = tmp_path / "view.md"
    out_md.write_text(glcv.render(ledger_path))
    _add_fragment_commit(repo, changes_dir, 100, "first", 900, "n", ["A"])
    # out_md is now stale relative to a fresh render (a new fragment merged)
    assert out_md.read_text() != glcv.render(ledger_path)
