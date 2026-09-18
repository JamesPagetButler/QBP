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
    """D7 guard (#654 AC6), AST + taint — a HEURISTIC, stated honestly (PR #658 round-2 NF-6):
    it catches the direct forms — open() with a write mode, Path(...).write_text/.write_bytes,
    json.dump into such an open() — on any path expression tainted by a ledger path (string
    constant naming the inventory, names assigned from it transitively, string concatenation).
    It does NOT catch indirection through getattr, shutil.copy/move, os.replace/os.open, a
    subprocess, or a path returned from a function; those are caught by review (the register
    diff and the confined helper's output are in every PR). A top-level scripts/*.py may not
    write to any tainted path expression through the forms it does catch."""
    import ast

    HINTS = ("cth-inventory", "confluent-trust-inventory")

    def tainted_expr(node, tainted):
        for sub in ast.walk(node):
            if (
                isinstance(sub, ast.Constant)
                and isinstance(sub.value, str)
                and any(h in sub.value for h in HINTS)
            ):
                return True
            if isinstance(sub, ast.Name) and sub.id in tainted:
                return True
        return False

    def write_mode(call):
        mode = None
        if len(call.args) > 1 and isinstance(call.args[1], ast.Constant):
            mode = call.args[1].value
        for kw in call.keywords:
            if kw.arg == "mode" and isinstance(kw.value, ast.Constant):
                mode = kw.value.value
        return isinstance(mode, str) and any(c in mode for c in "wa+")

    offenders = []
    for f in sorted(glob.glob(os.path.join(ROOT, "scripts", "*.py"))):
        base = os.path.basename(f)
        if base == "cth_ledger_edit.py":
            continue
        tree = ast.parse(open(f, encoding="utf-8").read())
        tainted = set()
        changed = True
        while changed:  # fixpoint over assignments
            changed = False
            for node in ast.walk(tree):
                targets = []
                if isinstance(node, ast.Assign):
                    targets, value = node.targets, node.value
                elif (
                    isinstance(node, (ast.AnnAssign, ast.AugAssign))
                    and node.value is not None
                ):
                    targets, value = [node.target], node.value
                else:
                    continue
                if tainted_expr(value, tainted):
                    for t in targets:
                        for n in ast.walk(t):
                            if isinstance(n, ast.Name) and n.id not in tainted:
                                tainted.add(n.id)
                                changed = True
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            fn = node.func
            name = fn.attr if isinstance(fn, ast.Attribute) else getattr(fn, "id", "")
            if (
                name == "open"
                and node.args
                and write_mode(node)
                and tainted_expr(node.args[0], tainted)
            ):
                offenders.append(f"{base}:{node.lineno} open(<ledger>, w)")
            elif (
                name in ("write_text", "write_bytes")
                and isinstance(fn, ast.Attribute)
                and tainted_expr(fn.value, tainted)
            ):
                offenders.append(f"{base}:{node.lineno} <ledger>.{name}()")
    assert (
        offenders == []
    ), f"scripts that write the ledger without cth_ledger_edit: {offenders}"


def test_reordering_records_is_an_undeclared_change(tmp_path):
    """PR #658 Red Team: reversing anchors[] was reported as confined. Order is content."""
    p = _mini(tmp_path)
    before = open(p).read()
    with pytest.raises(cle.ConfinementError, match="record order"):
        with cle.ledger_edit(p) as e:
            e.ledger["anchors"].reverse()
            e.record("anchors", "PRED-a")["status"] = "coherent"
    assert open(p).read() == before


def test_reordering_top_level_keys_is_an_undeclared_change(tmp_path):
    p = _mini(tmp_path)
    with pytest.raises(cle.ConfinementError, match="top-level key order"):
        with cle.ledger_edit(p) as e:
            v = e.ledger.pop("programme")
            e.ledger["programme"] = v  # same content, moved to the end
            e.record("anchors", "PRED-a")["status"] = "coherent"


def test_declared_append_does_not_trip_the_order_check(tmp_path):
    p = _mini(tmp_path)
    with cle.ledger_edit(p) as e:
        e.append(
            "anchors", {"id": "PRED-c", "status": "untested", "prediction_chain": []}
        )
        e.remove("anchors", "PRED-a")
    assert [a["id"] for a in json.load(open(p))["anchors"]] == ["PRED-b", "PRED-c"]


def test_intra_record_key_reorder_is_an_undeclared_change(tmp_path):
    """PR #658 round-2 NF-4: reordering keys inside a record writes a real diff."""
    p = _mini(tmp_path)
    with pytest.raises(cle.ConfinementError, match="UNDECLARED.*PRED-b"):
        with cle.ledger_edit(p) as e:
            rec = e.ledger["anchors"][1]
            items = list(rec.items())[::-1]
            rec.clear()
            rec.update(items)
            e.record("anchors", "PRED-a")["status"] = "coherent"


def test_order_sentinels_cannot_be_declared(tmp_path):
    p = _mini(tmp_path)
    with pytest.raises(cle.ConfinementError, match="cannot be declared"):
        with cle.ledger_edit(p) as e:
            e.touch("anchors", "<record order>")


def test_declared_new_top_level_key_is_not_a_reorder(tmp_path):
    """A new top-level record list (e.g. retired_axioms) appended and declared is an addition,
    not a key reorder (found by the AXIOM-2 encode PR against the #658 order check)."""
    p = _mini(tmp_path)
    with cle.ledger_edit(p) as e:
        e.ledger["retired_axioms"] = [{"id": "AXIOM-9", "statement": "s"}]
        e.touch("retired_axioms", "AXIOM-9")
        e.touch("retired_axioms")  # the new KEY is a change of its own
    L = json.load(open(p))
    assert L["retired_axioms"][0]["id"] == "AXIOM-9"
    assert list(L.keys())[:-1] == [
        "programme",
        "meta_axiom",
        "axioms",
        "anchors",
        "changelog",
        "last_updated",
    ]


def test_undeclared_new_empty_top_level_key_is_refused(tmp_path):
    """PR #662 Red Team A7: an undeclared new (even empty) top-level key is not confined."""
    p = _mini(tmp_path)
    before = open(p).read()
    with pytest.raises(cle.ConfinementError, match="UNDECLARED.*sneaky"):
        with cle.ledger_edit(p) as e:
            e.ledger["sneaky"] = []
            e.record("anchors", "PRED-a")["status"] = "coherent"
    assert open(p).read() == before
