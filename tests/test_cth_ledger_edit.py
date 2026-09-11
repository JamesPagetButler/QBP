"""Tests for scripts/cth_ledger_edit.py (issue #654 D7): a ledger write must be confined
to the declared records, must not be a silent no-op, and must not add formatting noise.
Also the guard: no top-level script in scripts/ may open the ledger for writing except
through this helper."""

import glob
import json
import os
import re
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import cth_ledger_edit as cle  # noqa: E402

LEDGER = os.path.join(
    ROOT, "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
)


def _mini(tmp_path):
    L = {
        "programme": "QBP",
        "meta_axiom": {"id": "META-1", "name": "m", "statement": "s"},
        "axioms": [
            {"id": "AXIOM-1", "name": "a", "statement": "s", "derivable": False}
        ],
        "anchors": [
            {"id": "PRED-a", "status": "untested", "prediction_chain": ["AXIOM-1"]},
            {"id": "PRED-b", "status": "untested", "prediction_chain": ["AXIOM-1"]},
        ],
        "changelog": [{"version": "1.0.0", "note": "n"}],
        "last_updated": "2026-01-01T00:00:00Z",
    }
    p = tmp_path / "ledger.json"
    p.write_text(cle.canonical_dump(L), encoding="utf-8")
    return str(p)


def test_confined_edit_writes_only_declared_records(tmp_path):
    p = _mini(tmp_path)
    with cle.ledger_edit(p) as e:
        e.record("anchors", "PRED-a")["status"] = "coherent"
        e.append(
            "anchors", {"id": "PRED-c", "status": "untested", "prediction_chain": []}
        )
        e.remove("axioms", "AXIOM-1")
        e.ledger["changelog"].append({"version": "1.1.0", "note": "x"})
        e.touch("changelog")
        e.ledger["last_updated"] = "2026-09-11T00:00:00Z"
        e.touch("last_updated")
    L = json.load(open(p))
    assert [a["id"] for a in L["anchors"]] == ["PRED-a", "PRED-b", "PRED-c"]
    assert L["anchors"][0]["status"] == "coherent" and L["axioms"] == []
    assert "PRED-a" in e.summary and "AXIOM-1" in e.summary


def test_undeclared_change_is_refused_and_nothing_written(tmp_path):
    p = _mini(tmp_path)
    before = open(p).read()
    with pytest.raises(cle.ConfinementError, match="UNDECLARED.*PRED-b"):
        with cle.ledger_edit(p) as e:
            e.record("anchors", "PRED-a")["status"] = "coherent"
            e.ledger["anchors"][1]["status"] = "coherent"  # not declared
    assert open(p).read() == before


def test_silent_noop_is_refused(tmp_path):
    p = _mini(tmp_path)
    before = open(p).read()
    with pytest.raises(cle.ConfinementError, match="silent no-op.*PRED-a"):
        with cle.ledger_edit(p) as e:
            e.record("anchors", "PRED-a")  # declared, never changed
    assert open(p).read() == before


def test_non_record_key_change_must_be_touched(tmp_path):
    p = _mini(tmp_path)
    with pytest.raises(cle.ConfinementError, match="UNDECLARED.*last_updated"):
        with cle.ledger_edit(p) as e:
            e.ledger["last_updated"] = "x"


def test_non_canonical_file_is_refused(tmp_path):
    p = tmp_path / "l.json"
    p.write_text(json.dumps({"anchors": [{"id": "PRED-a"}]}, indent=4))
    with pytest.raises(cle.ConfinementError, match="not in canonical form"):
        cle.LedgerEdit(str(p))


def test_dry_run_writes_nothing(tmp_path):
    p = _mini(tmp_path)
    before = open(p).read()
    with cle.ledger_edit(p, dry_run=True) as e:
        e.record("anchors", "PRED-a")["status"] = "coherent"
    assert open(p).read() == before and "PRED-a" in e.summary


def test_live_ledger_is_canonical():
    raw = open(LEDGER, encoding="utf-8").read()
    assert cle.canonical_dump(json.loads(raw)) == raw


def test_no_top_level_script_writes_the_ledger_directly():
    """D7 guard (#654 AC6): the only way to write the ledger from scripts/ is the helper.
    Applied one-shot encoders live under scripts/applied-encoders/ (history, do not re-run).
    """
    pat = re.compile(
        r"open\(\s*(LEDGER|ledger_path|args\.ledger|DEFAULT_LEDGER)\s*,\s*['\"]w"
    )
    offenders = []
    for f in glob.glob(os.path.join(ROOT, "scripts", "*.py")):
        src = open(f, encoding="utf-8").read()
        if os.path.basename(f) == "cth_ledger_edit.py":
            continue
        if pat.search(src) or re.search(
            r"json\.dump\(\s*(ledger|L)\s*,\s*open\(\s*LEDGER", src
        ):
            offenders.append(os.path.basename(f))
    assert (
        offenders == []
    ), f"scripts that write the ledger without cth_ledger_edit: {offenders}"
