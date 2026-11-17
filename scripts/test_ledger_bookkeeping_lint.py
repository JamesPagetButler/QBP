"""Tests for scripts/ledger_bookkeeping_lint.py (QBP#817 variant A)."""

import json
import os
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ledger_bookkeeping_lint as lbl  # noqa: E402
import ledger_fragment as lf  # noqa: E402

LEDGER_REL = lbl.LEDGER_REL
CHANGES_DIR_REL = lbl.CHANGES_DIR_REL


def _git(repo, *args):
    return subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, text=True
    ).stdout


def _init_repo(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "master")
    _git(repo, "config", "user.email", "t@example.com")
    _git(repo, "config", "user.name", "t")
    # Derived from the imported LEDGER_REL/CHANGES_DIR_REL constants (not retyped
    # as a literal here) so this fixture's layout always matches what
    # ledger_bookkeeping_lint.py itself expects on the real repo.
    ledger_rel_path = repo / LEDGER_REL
    ledger_rel_path.parent.mkdir(parents=True, exist_ok=True)
    ledger = {
        "version": "6.24.0",
        "changelog": [
            {"version": "6.24.0", "date": "2026-01-01T00:00:00Z", "note": "n"}
        ],
        "last_updated": "2026-01-01T00:00:00Z",
        "anchors": [
            {"id": "PRED-a", "status": "untested"},
            {"id": "PRED-b", "status": "untested"},
        ],
    }
    ledger_rel_path.write_text(json.dumps(ledger, indent=2) + "\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "init")
    monkeypatch.setattr(lbl, "REPO_ROOT", repo)
    return repo


def _ledger_path(repo):
    return repo / LEDGER_REL


def _checkout_branch(repo, name):
    _git(repo, "checkout", "-q", "-b", name)


def test_clean_pr_with_one_fragment_passes(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["PRED-a"],
        changes_dir=repo / CHANGES_DIR_REL,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = (
        lbl.check_frozen_fields("master", "feature")
        + lbl.check_fragment_count("master", "feature")
        + lbl.check_fragment_claims_diff("master", "feature")
    )
    assert errors == []


def test_touching_version_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["version"] = "6.25.0"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_frozen_fields("master", "feature")
    assert any("'version' differs" in e for e in errors)


def test_touching_changelog_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["changelog"].append({"version": "6.25.0", "date": "x", "note": "y"})
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_frozen_fields("master", "feature")
    assert any("'changelog' differs" in e for e in errors)


def test_ledger_change_with_no_fragment_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_count("master", "feature")
    assert any("0 fragment(s)" in e for e in errors)


def test_two_fragments_in_one_pr_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    changes_dir = repo / CHANGES_DIR_REL
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=changes_dir,
    )
    lf.write_fragment(
        issue=2,
        slug="b",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["Y"],
        changes_dir=changes_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_count("master", "feature")
    assert any("more than one fragment" in e for e in errors)


def test_modifying_an_existing_fragment_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    changes_dir = repo / CHANGES_DIR_REL
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=changes_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "fragment on master")

    _checkout_branch(repo, "feature")
    frag_path = changes_dir / "1-a.json"
    data = json.loads(frag_path.read_text())
    data["note"] = "edited after the fact"
    frag_path.write_text(json.dumps(data, indent=2))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_count("master", "feature")
    assert any("append-only" in e for e in errors)


def test_fragment_under_claiming_touched_ids_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    L["anchors"][1]["status"] = "coherent"  # changed too, but not claimed below
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["PRED-a"],
        changes_dir=repo / CHANGES_DIR_REL,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_claims_diff("master", "feature")
    assert any("missing touched_ids for ['PRED-b']" in e for e in errors)


def test_fragment_over_claiming_touched_ids_is_rejected(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["PRED-a", "PRED-b"],  # PRED-b never actually changed
        changes_dir=repo / CHANGES_DIR_REL,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_claims_diff("master", "feature")
    assert any("claims touched_ids ['PRED-b']" in e for e in errors)


def test_partial_rename_of_an_existing_fragment_is_rejected(tmp_path, monkeypatch):
    """D4 (qbp-oppenheimer, QBP#817 PR-1 review): a partial-content rename
    (git's "R087", not the byte-identical "R100" the original check only
    caught) must still be rejected -- append-only means append-only."""
    repo = _init_repo(tmp_path, monkeypatch)
    changes_dir = repo / CHANGES_DIR_REL
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n" * 50,
        touched_ids=["X"],
        changes_dir=changes_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "fragment on master")

    _checkout_branch(repo, "feature")
    old_path = changes_dir / "1-a.json"
    data = json.loads(old_path.read_text())
    data["note"] = "n" * 40 + " slightly different"  # similar but not identical
    old_path.unlink()
    (changes_dir / "1-renamed.json").write_text(json.dumps(data, indent=2))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    rows = lbl._diff_status("master", "feature", CHANGES_DIR_REL)
    assert any(
        s.startswith("R") and s != "R100" for s, _ in rows
    ), f"test setup didn't produce a partial-similarity rename: {rows}"
    errors = lbl.check_fragment_count("master", "feature")
    assert any("append-only" in e for e in errors)


def test_committed_changelog_view_is_rejected(tmp_path, monkeypatch):
    """D1 (qbp-oppenheimer, QBP#817 PR-1 review): the changelog view is never
    committed -- a PR that hand-adds it must fail, even though in real usage
    the file never exists on either ref to begin with."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    view_path = repo / lbl.CHANGELOG_VIEW_REL
    view_path.parent.mkdir(parents=True, exist_ok=True)
    view_path.write_text("# hand-committed changelog view\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_changelog_view_not_committed("master", "feature")
    assert any("must never be committed" in e for e in errors)


def test_changelog_view_absent_on_both_refs_passes(tmp_path, monkeypatch):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["PRED-a"],
        changes_dir=repo / CHANGES_DIR_REL,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")
    assert lbl.check_changelog_view_not_committed("master", "feature") == []


def test_main_exits_nonzero_on_any_failure(tmp_path, monkeypatch, capsys):
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["version"] = "6.25.0"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    monkeypatch.setattr(sys, "argv", ["lint", "--base", "master", "--head", "feature"])
    with pytest.raises(SystemExit) as exc:
        lbl.main()
    assert exc.value.code == 1
