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
