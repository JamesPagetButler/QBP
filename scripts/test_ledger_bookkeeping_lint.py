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


def test_non_json_file_in_changes_dir_is_never_treated_as_a_fragment(
    tmp_path, monkeypatch
):
    """Real bug, found by running this lint against this PR's own diff
    against master (not by any throwaway-repo test): changes.d/README.md
    documents the convention and is not a fragment, but the original code
    filtered `_diff_status` by status ("A") only, with no path/extension
    check -- so adding README.md alongside a real `.json` fragment (exactly
    what this PR's own first commit did) made `added` contain TWO paths
    (`['...changes.d/1-a.json', '...changes.d/README.md']`), tripping the
    "more than one fragment" check, and `check_fragment_claims_diff` would
    try (and crash) `json.loads()`-ing the Markdown file if README.md were
    ever the only or last "A" row. A content PR must still pass cleanly when
    changes.d/README.md is introduced alongside its one real fragment."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    changes_dir = repo / CHANGES_DIR_REL
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["PRED-a"],
        changes_dir=changes_dir,
    )
    changes_dir.mkdir(parents=True, exist_ok=True)
    (changes_dir / "README.md").write_text("# fragment convention\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = (
        lbl.check_frozen_fields("master", "feature")
        + lbl.check_fragment_count("master", "feature")
        + lbl.check_fragment_claims_diff("master", "feature")
        + lbl.check_changelog_view_not_committed("master", "feature")
    )
    assert errors == []


def test_fragment_with_no_ledger_change_at_all_is_rejected(tmp_path, monkeypatch):
    """F2 (qbp-architecture, QBP#817 PR-1 review, 2026-11-17): a PR that adds a
    fragment claiming touched_ids, but never actually changes the ledger,
    used to slip past this check entirely (it early-returned whenever the
    ledger was byte-identical at base/head). touched_ids can never
    legitimately be non-empty with zero real changes, so this must always be
    an over-claim, not a silent pass."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    # the ledger itself is NOT touched on this branch at all
    lf.write_fragment(
        issue=1,
        slug="bogus",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["NOT-A-REAL-ID"],
        changes_dir=repo / CHANGES_DIR_REL,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_claims_diff("master", "feature")
    assert any("claims touched_ids ['NOT-A-REAL-ID']" in e for e in errors)


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
        s.startswith("R") and s != "R100" for s, _, _ in rows
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


def test_base_ahead_of_merge_base_does_not_falsely_fail_append_only(
    tmp_path, monkeypatch
):
    """qbp-oppenheimer, QBP#817 PR-1 re-confirm nit, 2026-11-17: a two-dot
    `base..head` diff compares literal trees, so if `--base` (e.g.
    origin/master) has moved further ahead than this branch's own merge-base
    -- gaining its OWN fragments in the meantime -- those fragments look like
    they were "modified or removed" relative to head's tree, even though this
    branch never touched them. Three-dot (merge-base) diff must not."""
    repo = _init_repo(tmp_path, monkeypatch)
    changes_dir = repo / CHANGES_DIR_REL

    _checkout_branch(repo, "feature")
    lf.write_fragment(
        issue=1,
        slug="mine",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=changes_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature fragment")

    # master gains its OWN later fragment that `feature` never saw.
    _git(repo, "checkout", "-q", "master")
    lf.write_fragment(
        issue=2,
        slug="masters-own",
        pr=2,
        encoder="e",
        note="n",
        touched_ids=["Y"],
        changes_dir=changes_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "unrelated master fragment")

    errors = lbl.check_fragment_count("master", "feature")
    assert errors == []


def test_main_resolves_merge_base_so_an_unrelated_master_ledger_edit_does_not_false_fail(
    tmp_path, monkeypatch, capsys
):
    """F4' (qbp-architecture, QBP#817 PR-1 review, 2026-11-17): `_show(base,
    ...)` used to read `--base`'s literal tip, same bug class as the two-dot
    diff fix (F4) but not yet applied to the frozen-field/touched_ids content
    comparisons. A branch that never touched the ledger, run against a
    `--base` that has since gained an unrelated ledger edit, must still pass
    -- `main()` now resolves the merge-base once and uses it everywhere."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    # feature touches nothing ledger-related at all
    (repo / "unrelated.txt").write_text("x\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature, unrelated to the ledger")

    # master, meanwhile, gets its OWN unrelated ledger edit that feature never saw
    _git(repo, "checkout", "-q", "master")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "unrelated master-side ledger edit")

    monkeypatch.setattr(sys, "argv", ["lint", "--base", "master", "--head", "feature"])
    lbl.main()  # must not raise SystemExit
    assert "OK:" in capsys.readouterr().out


def test_renaming_an_issued_fragment_out_of_json_is_still_an_append_only_violation(
    tmp_path, monkeypatch
):
    """E1 (qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17): renaming an
    already-merged fragment to `.json.bak` (or `.md`) must still be caught as
    a touch of an existing fragment. The old filter checked only whether the
    diff row's string ended in `.json`, which for a rename row was really
    only checking the NEW path's suffix -- so a rename OUT of `.json` read as
    "not a fragment at all" and silently vanished from the append-only
    check, exactly the gap that (in a throwaway repo) moved a derived
    version backwards."""
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
    old_path = changes_dir / "1-a.json"
    old_path.rename(changes_dir / "1-a.json.bak")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature renames the fragment out of .json")

    errors = lbl.check_fragment_count("master", "feature")
    assert any("append-only" in e for e in errors)


def test_fragment_added_in_a_subdirectory_of_changes_dir_is_rejected(
    tmp_path, monkeypatch
):
    """E2 (qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17): a fragment
    added under changes.d/sub/ passes every diff-based check (the pathspec
    is recursive) but ledger_fragment.read_fragments() only globs
    changes.d/*.json directly, so it is invisible to version derivation and
    the changelog view even though CI said the PR was clean."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    L = json.loads(_ledger_path(repo).read_text())
    L["anchors"][0]["status"] = "coherent"
    _ledger_path(repo).write_text(json.dumps(L, indent=2) + "\n")
    sub_dir = repo / CHANGES_DIR_REL / "sub"
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["PRED-a"],
        changes_dir=sub_dir,
    )
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature")

    errors = lbl.check_fragment_count("master", "feature")
    assert any("not named" in e for e in errors)


def test_non_ascii_fragment_filename_is_rejected_not_silently_invisible(
    tmp_path, monkeypatch
):
    """E3 (qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17): git's
    default `--name-status` C-style-quotes a non-ASCII path (wrapping it in
    literal double quotes and octal-escaping the character), so a bogus
    `changes.d/2-é.json` -- claiming an id with the ledger UNCHANGED --
    used to never show up as a `.json` row at all, passing the lint while
    `ledger_fragment.read_fragments()`'s real filesystem glob still picked it
    up and gave it a real derived version. `-z` output has no quoting, and
    the filename must now match the real naming convention exactly, so this
    must be rejected on both counts: an invalid name AND (since it's still
    recognized as "added" now) an over-claim against an unchanged ledger."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    # the ledger itself is NOT touched on this branch at all
    changes_dir = repo / CHANGES_DIR_REL
    changes_dir.mkdir(parents=True, exist_ok=True)
    bogus = {
        "issue": 2,
        "slug": "e9",
        "pr": 2,
        "encoder": "e",
        "note": "n",
        "touched_ids": ["NOT-A-REAL-ID"],
        "version": None,
        "date": None,
    }
    (changes_dir / "2-é.json").write_text(json.dumps(bogus, indent=2))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature adds a non-ASCII-named bogus fragment")

    count_errors = lbl.check_fragment_count("master", "feature")
    assert any("not named" in e for e in count_errors)
    claims_errors = lbl.check_fragment_claims_diff("master", "feature")
    assert any("claims touched_ids ['NOT-A-REAL-ID']" in e for e in claims_errors)


def test_readme_added_alone_with_no_ledger_change_passes_cleanly(tmp_path, monkeypatch):
    """Kills the J1b mutant (qbp-architecture): deleting `_fragment_rows`'s
    README.md exemption SURVIVED all 18 pre-E3 tests, because every existing
    README-adjacent test also added a real fragment, which already produced
    an error of its own (two "A" rows) independent of whether README.md was
    exempted. Isolated here with NOTHING else changing: changes.d/README.md
    is added on its own, with the ledger untouched and no other fragment in
    the diff at all. Without the exemption, README.md itself would be
    treated as an "added" row and immediately fail `_is_fragment_path`
    (wrong name, wrong pattern) -- this must still pass cleanly."""
    repo = _init_repo(tmp_path, monkeypatch)
    _checkout_branch(repo, "feature")
    changes_dir = repo / CHANGES_DIR_REL
    changes_dir.mkdir(parents=True, exist_ok=True)
    (changes_dir / "README.md").write_text("# fragment convention\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "feature adds only the README")

    errors = (
        lbl.check_frozen_fields("master", "feature")
        + lbl.check_fragment_count("master", "feature")
        + lbl.check_fragment_claims_diff("master", "feature")
        + lbl.check_changelog_view_not_committed("master", "feature")
    )
    assert errors == []


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
