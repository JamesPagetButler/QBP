"""Tests for scripts/encode_791_desi_fit_ac3.py (QBP#791 AC3)."""

import json
import sys

import pytest

sys.path.insert(0, "scripts")
import encode_791_desi_fit_ac3 as m  # noqa: E402


def _write_canonical_ledger(path, ledger):
    path.write_text(
        json.dumps(ledger, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


def _ledger_with_target_anchor():
    return {
        "programme": "test",
        "version": "1.0.0",
        "last_updated": "2026-01-01T00:00:00Z",
        "changelog": [],
        "axioms": [],
        "anchors": [
            {
                "id": m.ANCHOR_ID,
                "name": "test fixture",
                "tier": 1,
                "provenance": "T",
                "status": "marginal",
                "description": "w > -1 at z < z_t, w < -1 at z > z_t (test fixture)",
                "prediction_chain": [],
                "notes": "Shared prefix (test fixture).",
            }
        ],
        "chains": [],
    }


def test_main_writes_e_axis_review_flag_evidence_ref_and_one_fragment(
    tmp_path, monkeypatch
):
    ledger_path = tmp_path / "ledger.json"
    _write_canonical_ledger(ledger_path, _ledger_with_target_anchor())
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "encode_791_desi_fit_ac3.py",
            "--ledger",
            str(ledger_path),
            "--pr",
            "900",
        ],
    )
    m.main()

    after = json.loads(ledger_path.read_text())
    assert after["version"] == "1.0.0"  # frozen — never touched
    assert after["changelog"] == []  # frozen — never touched
    anchor = next(a for a in after["anchors"] if a["id"] == m.ANCHOR_ID)
    assert anchor["e_axis"] == {"value": "falsified", "post_hoc": True}
    assert anchor["review_flag"] == m.REVIEW_FLAG
    assert anchor["evidence_ref"] == m.EVIDENCE_REF
    assert anchor["notes"].startswith("Shared prefix (test fixture).")
    assert m.NOTES_ADDITION in anchor["notes"]

    fragments = list(changes_dir.glob("*.json"))
    assert len(fragments) == 1
    frag = json.loads(fragments[0].read_text())
    assert frag["issue"] == 791
    assert frag["pr"] == 900
    assert frag["touched_ids"] == [m.ANCHOR_ID]
    assert frag["encoder"] == "scripts/encode_791_desi_fit_ac3.py"


def test_main_second_run_is_an_idempotent_no_op(tmp_path, monkeypatch):
    ledger_path = tmp_path / "ledger.json"
    _write_canonical_ledger(ledger_path, _ledger_with_target_anchor())
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "encode_791_desi_fit_ac3.py",
            "--ledger",
            str(ledger_path),
            "--pr",
            "900",
        ],
    )
    m.main()
    after_first = ledger_path.read_text()
    fragments_after_first = list(changes_dir.glob("*.json"))
    assert len(fragments_after_first) == 1

    with pytest.raises(SystemExit, match="already applied"):
        m.main()

    assert ledger_path.read_text() == after_first  # byte-identical — no 2nd write
    assert list(changes_dir.glob("*.json")) == fragments_after_first  # no 2nd fragment


def test_main_refuses_a_ledger_without_the_target_anchor(tmp_path, monkeypatch):
    ledger_path = tmp_path / "ledger.json"
    ledger = _ledger_with_target_anchor()
    ledger["anchors"] = []
    _write_canonical_ledger(ledger_path, ledger)

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--pr", "900"],
    )
    with pytest.raises(SystemExit, match=m.ANCHOR_ID):
        m.main()
    assert json.loads(ledger_path.read_text()) == ledger


def test_main_without_pr_refuses_before_writing_ledger_or_fragment(
    tmp_path, monkeypatch
):
    ledger_path = tmp_path / "ledger.json"
    _write_canonical_ledger(ledger_path, _ledger_with_target_anchor())
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys, "argv", ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path)]
    )
    with pytest.raises(SystemExit, match="--pr"):
        m.main()

    assert json.loads(ledger_path.read_text()) == _ledger_with_target_anchor()
    assert not changes_dir.exists()


def test_dry_run_changes_neither_ledger_nor_filesystem(tmp_path, monkeypatch):
    ledger_path = tmp_path / "ledger.json"
    _write_canonical_ledger(ledger_path, _ledger_with_target_anchor())
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--dry-run"],
    )
    m.main()

    assert json.loads(ledger_path.read_text()) == _ledger_with_target_anchor()
    assert not changes_dir.exists()
