"""Tests for scripts/root_audit.py (issue #654 D1/D2) — the gate must be absolute,
whole-population, baseline-free, and its only escape a shrink-only issue-linked register.
Synthetic ledgers first; the live ledger + committed register last."""

import copy
import json
import os
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import root_audit as ra  # noqa: E402


def _anchor(aid, chain, prov="T"):
    return {
        "id": aid,
        "name": aid,
        "tier": 1,
        "provenance": prov,
        "status": "untested",
        "description": "",
        "prediction_chain": chain,
    }


def _ledger():
    return {
        "meta_axiom": {"id": "META-1", "name": "m", "statement": "s"},
        "axioms": [
            {"id": "AXIOM-1", "name": "a", "statement": "s", "derivable": False},
            {
                "id": "POST-open",
                "name": "p",
                "statement": "s",
                "derivable": False,
                "kill_condition": "if X then dead",
                "decision_state": "open",
            },
            {
                "id": "POST-ruled",
                "name": "p",
                "statement": "s",
                "derivable": False,
                "decision_state": "ruled",
                "ruling": "https://github.com/JamesPagetButler/QBP/issues/647#issuecomment-1",
            },
            {
                "id": "POST-forced",
                "name": "p",
                "statement": "s",
                "derivable": False,
                "forced_by": ["PROOF-x"],
            },
        ],
        "derived_principles": [
            {
                "id": "DERIV-a",
                "name": "d",
                "statement": "s",
                "derived_from": ["AXIOM-1"],
            },
            {
                "id": "DERIV-b",
                "name": "d",
                "statement": "s",
                "derived_from": ["DERIV-a"],
            },
        ],
        "anchors": [
            _anchor("PROOF-x", []),
            _anchor("MEAS-y", ["DERIV-b"], prov="E"),
            _anchor("OBS-z", [], prov="E"),
            _anchor("PRED-p", ["DERIV-b", "OBS-z"]),
            _anchor("INSIGHT-i", []),
        ],
    }


def _run(ledger, open_roots=None, chain_debt=None):
    return ra.audit(ledger, open_roots or {}, chain_debt or {}, [])


def test_buckets_and_unsorted():
    res = _run(_ledger())
    b = {rid: v[1] for rid, v in res["roots"].items()}
    assert b["POST-forced"] == 1 and b["POST-ruled"] == 2 and b["POST-open"] == 3
    assert b["META-1"] is None and b["AXIOM-1"] is None
    unsorted = [f for f in res["failures"] if f.startswith("UNSORTED ROOT")]
    assert {f.split()[2] for f in unsorted} == {"META-1", "AXIOM-1"}
    # INSIGHT with an empty chain is reported, never gated (no derivation obligation)
    assert not any("INSIGHT-i" in f for f in res["failures"])
    assert res["ungated_dangling"]["INSIGHT"] == 1


def test_register_is_the_only_escape_and_is_shrink_only():
    L = _ledger()
    reg = {
        rid: {"id": rid, "issue": "https://github.com/x/y/issues/1"}
        for rid in ("META-1", "AXIOM-1")
    }
    assert not _run(L, open_roots=reg)["failures"]
    # a registered root that now sorts → stale entry → HARD FAIL (register only shrinks)
    L["axioms"][0].update({"kill_condition": "k", "decision_state": "open"})
    f = _run(L, open_roots=reg)["failures"]
    assert any(x.startswith("STALE REGISTER open_roots AXIOM-1") for x in f)
    # an entry for a root that does not exist is stale too
    f = _run(_ledger(), open_roots={**reg, "AXIOM-9": {"id": "AXIOM-9", "issue": "u"}})[
        "failures"
    ]
    assert any("AXIOM-9" in x and "STALE" in x for x in f)


def test_register_entry_needs_id_and_issue(tmp_path):
    p = tmp_path / "r.json"
    p.write_text(json.dumps({"open_roots": [{"id": "META-1"}], "chain_debt": []}))
    o, c, problems = ra.load_register(str(p))
    assert o == {} and problems and "without id+issue" in problems[0]


def test_ruled_root_needs_a_github_cite():
    L = _ledger()
    L["axioms"][2]["ruling"] = "the beekeeper said so"
    f = _run(L)["failures"]
    assert any("POST-ruled" in x and "cites no GitHub" in x for x in f)


def test_forced_by_must_resolve_and_be_proof_or_meas():
    L = _ledger()
    L["axioms"][3]["forced_by"] = ["PROOF-missing"]
    assert any(
        "POST-forced" in x and "do not resolve" in x for x in _run(L)["failures"]
    )
    L["axioms"][3]["forced_by"] = ["INSIGHT-i"]
    assert any("POST-forced" in x and "not a forcing" in x for x in _run(L)["failures"])


def test_smuggled_root_in_anchors_fails_without_carveout():
    L = _ledger()
    L["anchors"].append(_anchor("META-some-field", []))
    f = _run(L)["failures"]
    assert any(x.startswith("SMUGGLED ROOT META-some-field") for x in f)
    L["anchors"].append(_anchor("POST-hidden", []))
    assert any(x.startswith("SMUGGLED ROOT POST-hidden") for x in _run(L)["failures"])


def test_chain_resolution_gated_for_every_owner():
    L = _ledger()
    L["anchors"][1]["prediction_chain"] = [
        "DERIV-b",
        "DERIV-never-encoded",
    ]  # a MEAS owner
    f = _run(L)["failures"]
    assert any(x.startswith("CHAIN UNRESOLVED DERIV-never-encoded") for x in f)
    debt = {"DERIV-never-encoded": {"id": "DERIV-never-encoded", "issue": "u"}}
    assert not [x for x in _run(L, chain_debt=debt)["failures"] if "UNRESOLVED" in x]
    # fixing it without removing the entry → stale
    L["anchors"][1]["prediction_chain"] = ["DERIV-b"]
    assert any(
        "STALE REGISTER chain_debt DERIV-never-encoded" in x
        for x in _run(L, chain_debt=debt)["failures"]
    )


def test_termination_gated_for_derived_only_and_cycles_fail():
    L = _ledger()
    L["anchors"].append(_anchor("DERIV-dangling", []))
    L["anchors"].append(_anchor("PRED-via-ref", ["REF-r"]))
    L["anchors"].append(_anchor("REF-r", []))
    f = _run(L)["failures"]
    assert any(x.startswith("CHAIN DANGLING DERIV-dangling") for x in f)
    assert any(x.startswith("CHAIN DANGLING PRED-via-ref") for x in f)
    assert not any(
        "REF-r:" in x for x in f
    )  # REF is report-only (no derivation obligation)
    L["derived_principles"][0]["derived_from"] = ["DERIV-b"]  # a -> b -> a
    f = _run(L)["failures"]
    assert any("CHAIN CYCLE" in x and "DERIV-a -> DERIV-b -> DERIV-a" in x for x in f)


def test_terminal_owner_with_empty_chain_is_not_dangling():
    res = _run(_ledger())
    assert "PROOF-x" not in res["dangling"] and "OBS-z" not in res["dangling"]


def test_no_baseline_file_exists():
    for name in os.listdir(os.path.join(ROOT, "analysis")):
        assert "root-audit" not in name and "root_audit" not in name


def test_live_ledger_passes_with_committed_register():
    L = json.load(open(os.path.join(ROOT, ra.DEFAULT_LEDGER), encoding="utf-8"))
    o, c, p = ra.load_register(os.path.join(ROOT, ra.DEFAULT_REGISTER))
    assert not p
    assert _run(L, o, c)["failures"] == []
    for e in list(o.values()) + list(c.values()):
        assert e["issue"].startswith("https://github.com/JamesPagetButler/QBP/issues/")
