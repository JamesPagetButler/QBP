"""Tests for scripts/ledger_fragment.py (QBP#817 variant A)."""

import json
import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ledger_fragment as lf  # noqa: E402


def test_build_fragment_shape():
    f = lf.build_fragment(
        issue=817,
        slug="example",
        pr=900,
        encoder="scripts/foo.py",
        note="did a thing",
        touched_ids=["PRED-b", "PRED-a"],
    )
    assert f == {
        "issue": 817,
        "slug": "example",
        "pr": 900,
        "encoder": "scripts/foo.py",
        "note": "did a thing",
        "touched_ids": ["PRED-a", "PRED-b"],  # sorted
        "version": None,
        "date": None,
    }


def test_build_fragment_rejects_empty_note():
    with pytest.raises(lf.FragmentError, match="note"):
        lf.build_fragment(
            issue=1, slug="s", pr=1, encoder="e", note="  ", touched_ids=["X"]
        )


def test_build_fragment_rejects_empty_touched_ids():
    with pytest.raises(lf.FragmentError, match="touched_ids"):
        lf.build_fragment(
            issue=1, slug="s", pr=1, encoder="e", note="n", touched_ids=[]
        )


def test_fragment_path_rejects_non_kebab_slug():
    with pytest.raises(lf.FragmentError, match="kebab-case"):
        lf.fragment_path(1, "Not_Kebab")


def test_write_fragment_round_trips(tmp_path):
    path = lf.write_fragment(
        issue=817,
        slug="example",
        pr=900,
        encoder="scripts/foo.py",
        note="did a thing",
        touched_ids=["PRED-a"],
        changes_dir=tmp_path,
    )
    assert path == tmp_path / "817-example.json"
    data = json.loads(path.read_text())
    assert data["issue"] == 817 and data["version"] is None


def test_write_fragment_refuses_to_overwrite(tmp_path):
    lf.write_fragment(
        issue=817,
        slug="example",
        pr=900,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=tmp_path,
    )
    with pytest.raises(lf.FragmentError, match="already exists"):
        lf.write_fragment(
            issue=817,
            slug="example",
            pr=901,
            encoder="e",
            note="n2",
            touched_ids=["Y"],
            changes_dir=tmp_path,
        )


def test_write_fragment_dry_run_writes_nothing(tmp_path):
    path = lf.write_fragment(
        issue=1,
        slug="s",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=tmp_path,
        dry_run=True,
    )
    assert not path.exists()


def test_read_fragments_empty_dir_is_empty_list(tmp_path):
    assert lf.read_fragments(tmp_path / "nonexistent") == []


def test_read_fragments_validates_each_file(tmp_path):
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=tmp_path,
    )
    bad = tmp_path / "2-b.json"
    bad.write_text(json.dumps({"issue": 2}))  # missing required keys
    with pytest.raises(lf.FragmentError, match="missing required key"):
        lf.read_fragments(tmp_path)


def test_read_fragments_returns_path_and_data_pairs(tmp_path):
    lf.write_fragment(
        issue=1,
        slug="a",
        pr=1,
        encoder="e",
        note="n",
        touched_ids=["X"],
        changes_dir=tmp_path,
    )
    rows = lf.read_fragments(tmp_path)
    assert len(rows) == 1
    path, data = rows[0]
    assert path.name == "1-a.json" and data["issue"] == 1


def test_validate_fragment_rejects_extra_keys():
    data = lf.build_fragment(
        issue=1, slug="s", pr=1, encoder="e", note="n", touched_ids=["X"]
    )
    data["extra"] = "nope"
    with pytest.raises(lf.FragmentError, match="unexpected key"):
        lf.validate_fragment(data)


def test_is_fragment_accepts_the_real_shape():
    assert lf.is_fragment("817-example.json", "100644") is True


def test_is_fragment_rejects_a_symlink_mode():
    """N2 (qbp-architecture, QBP#817 PR-1 re-confirm, 2026-11-17): a
    correctly-named entry with any mode but 100644 (a symlink's 120000
    above all) is never a fragment -- a dangling symlink must never reach
    read_fragments()'s json.loads() at all."""
    assert lf.is_fragment("1-a.json", "120000") is False


def test_is_fragment_rejects_an_executable_mode():
    assert lf.is_fragment("1-a.json", "100755") is False


def test_is_fragment_rejects_a_subdirectory_path():
    assert lf.is_fragment("sub/1-a.json", "100644") is False


def test_is_fragment_rejects_a_trailing_newline_in_the_name():
    """N1: a bare `.match(pattern + "$")` lets a filename with a trailing
    newline through, because `$` matches just before a final trailing
    newline too. `is_fragment` uses `re.fullmatch`, which requires the
    match to consume the entire string -- the stray `\\n` can't be
    consumed by a zero-width assertion, so this must be rejected."""
    assert lf.is_fragment("1-a.json\n", "100644") is False


def test_is_fragment_rejects_a_non_ascii_name():
    assert lf.is_fragment("2-é.json", "100644") is False


def test_is_fragment_rejects_a_leading_zero_or_zero_issue_number():
    """Gemini real-API review, PR #819, 2026-11-18: a bare `[0-9]+` accepted
    a leading-zero or zero-valued issue number as a valid fragment name --
    more permissive than write_fragment() ever produces (Python int
    formatting never pads) and no real GitHub issue is numbered 0."""
    assert lf.is_fragment("007-a.json", "100644") is False
    assert lf.is_fragment("0-a.json", "100644") is False


def test_fs_mode_distinguishes_file_symlink_and_executable(tmp_path):
    regular = tmp_path / "1-a.json"
    regular.write_text("{}")
    assert lf._fs_mode(regular) == "100644"

    executable = tmp_path / "2-b.json"
    executable.write_text("{}")
    executable.chmod(executable.stat().st_mode | 0o111)
    assert lf._fs_mode(executable) == "100755"

    link = tmp_path / "3-c.json"
    link.symlink_to(tmp_path / "nonexistent-target")
    assert lf._fs_mode(link) == "120000"


def test_read_fragments_skips_a_dangling_symlink_instead_of_crashing(tmp_path):
    """N2: a dangling symlink named like a real fragment must never reach
    json.loads() -- confirmed by reverting is_fragment's mode check and
    seeing this test fail with FileNotFoundError instead of returning []."""
    (tmp_path / "1-a.json").symlink_to(tmp_path / "does-not-exist")
    assert lf.read_fragments(tmp_path) == []


def test_read_fragments_skips_a_trailing_newline_named_file(tmp_path):
    bad_name = "2-b.json\n"
    (tmp_path / bad_name).write_text(
        json.dumps(
            {
                "issue": 2,
                "slug": "b",
                "pr": 1,
                "encoder": "e",
                "note": "n",
                "touched_ids": ["X"],
                "version": None,
                "date": None,
            }
        )
    )
    assert lf.read_fragments(tmp_path) == []
