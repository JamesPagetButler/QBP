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


def test_main_on_partial_drift_corrects_fields_without_duplicating_notes(
    tmp_path, monkeypatch
):
    """Gemini real-API review, PR #821: `already_applied()` is an all-or-
    nothing check across four fields, so a steward hand-edit to just one of
    them (here: `review_flag`, after a correction) makes it return False even
    though `notes` already carries NOTES_ADDITION from an earlier run. A
    naive unconditional `notes = notes + NOTES_ADDITION` would duplicate the
    addition in that case. Must correct the drifted field and leave `notes`
    with exactly one copy."""
    ledger_path = tmp_path / "ledger.json"
    ledger = _ledger_with_target_anchor()
    anchor = ledger["anchors"][0]
    anchor["e_axis"] = dict(m.E_AXIS)
    anchor["evidence_ref"] = [dict(e) for e in m.EVIDENCE_REF]
    anchor["notes"] = anchor["notes"] + m.NOTES_ADDITION
    anchor["review_flag"] = "a stale, hand-edited flag text"  # the drift
    _write_canonical_ledger(ledger_path, ledger)
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--pr", "900"],
    )
    m.main()

    after = json.loads(ledger_path.read_text())
    fixed = next(a for a in after["anchors"] if a["id"] == m.ANCHOR_ID)
    assert fixed["review_flag"] == m.REVIEW_FLAG  # drift corrected
    assert fixed["notes"].count(m.NOTES_ADDITION) == 1  # not duplicated
    assert len(list(changes_dir.glob("*.json"))) == 1  # fragment still written


def test_main_rewrites_an_existing_fragment_in_place_without_erroring_or_duplicating(
    tmp_path, monkeypatch
):
    """oppenheimer theory re-confirm fix round, PR #821 (issuecomment-
    7047925804): a fix round that corrects the fragment's own `note` text
    must not hit `write_fragment`'s "already exists" refusal (the fragment
    was already added by this same open, unmerged PR) and must not write a
    second file (ledger_bookkeeping_lint.py's "exactly one fragment" rule is
    repo-wide, not per-commit)."""
    ledger_path = tmp_path / "ledger.json"
    ledger = _ledger_with_target_anchor()
    anchor = ledger["anchors"][0]
    anchor["e_axis"] = dict(m.E_AXIS)
    anchor["evidence_ref"] = [dict(e) for e in m.EVIDENCE_REF]
    anchor["review_flag"] = m.REVIEW_FLAG
    anchor["notes"] = anchor["notes"] + m.OLD_NOTES_ADDITION_V2  # stale text
    _write_canonical_ledger(ledger_path, ledger)
    changes_dir = tmp_path / "changes.d"
    changes_dir.mkdir()
    stale_fragment = m.build_fragment(
        issue=m.FRAGMENT_ISSUE,
        slug=m.FRAGMENT_SLUG,
        pr=900,
        encoder="scripts/encode_791_desi_fit_ac3.py",
        note="a stale, pre-fix-round note",
        touched_ids=[m.ANCHOR_ID],
    )
    fragment_file = m.fragment_path(m.FRAGMENT_ISSUE, m.FRAGMENT_SLUG, changes_dir)
    fragment_file.write_text(m.canonical_dump(stale_fragment), encoding="utf-8")

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--pr", "900"],
    )
    m.main()  # must not raise FragmentError("already exists")

    fragments = list(changes_dir.glob("*.json"))
    assert len(fragments) == 1  # never a second file
    frag = json.loads(fragments[0].read_text())
    assert frag["note"] != "a stale, pre-fix-round note"  # content actually fixed
    assert "candidate" in frag["note"].lower()

    after = json.loads(ledger_path.read_text())
    fixed = next(a for a in after["anchors"] if a["id"] == m.ANCHOR_ID)
    assert m.OLD_NOTES_ADDITION_V2 not in fixed["notes"]
    assert fixed["notes"].count(m.NOTES_ADDITION) == 1


def test_main_replaces_the_v1_superseded_text_directly(tmp_path, monkeypatch):
    """Belt: a ledger that never saw the V2 intermediate text (e.g. restored
    from the original PR #821 real-run head, 05ff9ea) must still replace
    cleanly straight to the current NOTES_ADDITION -- SUPERSEDED_NOTES_
    ADDITIONS must not assume the chain was applied in order."""
    ledger_path = tmp_path / "ledger.json"
    ledger = _ledger_with_target_anchor()
    anchor = ledger["anchors"][0]
    anchor["e_axis"] = dict(m.E_AXIS)
    anchor["evidence_ref"] = [dict(e) for e in m.EVIDENCE_REF]
    anchor["review_flag"] = m.REVIEW_FLAG
    anchor["notes"] = anchor["notes"] + m.OLD_NOTES_ADDITION_V1
    _write_canonical_ledger(ledger_path, ledger)
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--pr", "900"],
    )
    m.main()

    after = json.loads(ledger_path.read_text())
    fixed = next(a for a in after["anchors"] if a["id"] == m.ANCHOR_ID)
    assert m.OLD_NOTES_ADDITION_V1 not in fixed["notes"]
    assert fixed["notes"].count(m.NOTES_ADDITION) == 1
    assert len(list(changes_dir.glob("*.json"))) == 1


def test_main_replaces_the_v3_candidate_text_once_the_review_passes(
    tmp_path, monkeypatch
):
    """oppenheimer seq5627: once the QBP#772 kill-condition review is
    recorded AND PASSING, the "FALSIFIED CANDIDATE" qualifier clause (V3,
    written while the review was still pending) overstates the remaining
    uncertainty and must be dropped entirely, not just have its kill-
    condition sentence updated in place."""
    ledger_path = tmp_path / "ledger.json"
    ledger = _ledger_with_target_anchor()
    anchor = ledger["anchors"][0]
    anchor["e_axis"] = dict(m.E_AXIS)
    anchor["evidence_ref"] = [dict(e) for e in m.EVIDENCE_REF]
    anchor["review_flag"] = m.REVIEW_FLAG
    anchor["notes"] = anchor["notes"] + m.OLD_NOTES_ADDITION_V3
    _write_canonical_ledger(ledger_path, ledger)
    changes_dir = tmp_path / "changes.d"

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--pr", "900"],
    )
    m.main()

    after = json.loads(ledger_path.read_text())
    fixed = next(a for a in after["anchors"] if a["id"] == m.ANCHOR_ID)
    assert m.OLD_NOTES_ADDITION_V3 not in fixed["notes"]
    assert "FALSIFIED CANDIDATE" not in fixed["notes"]
    assert fixed["notes"].count(m.NOTES_ADDITION) == 1
    assert len(list(changes_dir.glob("*.json"))) == 1


def test_main_removes_every_superseded_text_present_at_once(tmp_path, monkeypatch):
    """Gemini real-API review, PR #821 (final pass): the superseded-text
    cleanup must not stop after its first match -- a hand-edited ledger that
    somehow carries more than one stale text at once (never produced by this
    script's own normal operation, but not ruled out by anything the schema
    enforces) must still end up with exactly the current NOTES_ADDITION and
    none of the superseded texts, not just whichever one the loop hit first."""
    ledger_path = tmp_path / "ledger.json"
    ledger = _ledger_with_target_anchor()
    anchor = ledger["anchors"][0]
    anchor["e_axis"] = dict(m.E_AXIS)
    anchor["evidence_ref"] = [dict(e) for e in m.EVIDENCE_REF]
    anchor["review_flag"] = m.REVIEW_FLAG
    anchor["notes"] = (
        anchor["notes"] + m.OLD_NOTES_ADDITION_V1 + m.OLD_NOTES_ADDITION_V2
    )
    _write_canonical_ledger(ledger_path, ledger)

    monkeypatch.setattr(
        sys,
        "argv",
        ["encode_791_desi_fit_ac3.py", "--ledger", str(ledger_path), "--pr", "900"],
    )
    m.main()

    after = json.loads(ledger_path.read_text())
    fixed = next(a for a in after["anchors"] if a["id"] == m.ANCHOR_ID)
    assert m.OLD_NOTES_ADDITION_V1 not in fixed["notes"]
    assert m.OLD_NOTES_ADDITION_V2 not in fixed["notes"]
    assert fixed["notes"].count(m.NOTES_ADDITION) == 1


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
