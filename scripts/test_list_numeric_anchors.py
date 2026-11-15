#!/usr/bin/env python3
"""Tests for scripts/list_numeric_anchors.py (QBP #479).

Per docs/cth/proof-anchor-best-practices.md ("a gate is judged by what it catches") the
centrepiece is a set of ADVERSARIAL synthetic ledgers: bools and string-numbers that must
NOT count as numeric, bookkeeping fields that must be excluded, a drifted override quote
that must raise, a chain cycle that must terminate, one record per OWN tag rule so the
precedence order is pinned, and a small chain fixture for the EFFECTIVE tag (AC4 Q4: a
SELECTED ancestor, a dangling ancestor, a clean FORCED chain, a neutral non-anchor node).
The real ledger is then checked for structural invariants only (every numeric anchor gets
exactly one own and one effective tag; effective ≤ own; overrides verify; the dangling report
is consistent with the collections) — counts are recorded in the proposal doc, not pinned
here, because the ledger moves.

Run: python3 scripts/test_list_numeric_anchors.py
(also pytest-collectible: python3 -m pytest scripts/test_list_numeric_anchors.py)
"""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
from typing import Any, Dict, List

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "list_numeric_anchors.py")


def _check(cond: bool, msg: str) -> None:
    """`assert` that survives `python3 -O`."""
    if not cond:
        raise AssertionError(msg)


def _load():
    spec = importlib.util.spec_from_file_location("list_numeric_anchors", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


M = _load()


def _anchor(aid: str, **kw: Any) -> Dict[str, Any]:
    base: Dict[str, Any] = {
        "id": aid,
        "name": aid,
        "tier": 2,
        "provenance": "T",
        "status": "untested",
        "description": "synthetic",
        "prediction_chain": [],
        "provenance_kind": "theory",
    }
    base.update(kw)
    return base


def _ledger(
    anchors: List[Dict[str, Any]], inputs=None, **collections: List[Dict[str, Any]]
) -> Dict[str, Any]:
    led: Dict[str, Any] = {
        "programme": "SYN",
        "version": "0.0.0",
        "schema_version": "v0.3",
        "anchors": anchors,
        "inputs": inputs or [],
    }
    led.update(collections)  # e.g. derived_principles=[{"id": "DERIV-x", ...}]
    return led


# ── numeric detection ────────────────────────────────────────────────────────


def test_numeric_detection_excludes_bool_string_empty_and_bookkeeping():
    _check(M.is_numeric_value(3) and M.is_numeric_value(2.5), "ints/floats are numeric")
    _check(not M.is_numeric_value(True), "bool is not numeric")
    _check(not M.is_numeric_value("128.05"), "string-typed number is not numeric")
    _check(
        not M.is_numeric_value([]) and not M.is_numeric_value({}), "empty containers"
    )
    _check(M.is_numeric_value([1, 2.0]), "numeric list")
    _check(
        M.is_numeric_value([1, "x"]), "mixed list with a numeric leaf IS numeric (G1)"
    )
    _check(not M.is_numeric_value(["x", {"a": "b"}]), "container with no numeric leaf")
    _check(
        M.is_numeric_value({"test_type": "IFU", "F_max_best_fit": 13.4}),
        "mixed experimental_backing dict counts (PRED-a0-redshift-linear case)",
    )
    _check(M.is_numeric_value({"a": {"b": 1}}), "nested numeric dict")
    a = _anchor("X-bookkeeping", tier=3, sorry_count=0, pa_local=2, pa_effective=1)
    _check(M.numeric_fields(a) == {}, "bookkeeping-only record is NOT numeric")
    b = _anchor("X-num", measured_value=1.0)
    _check(M.numeric_fields(b) == {"measured_value": 1.0}, "measured_value counts")
    led = _ledger([a, b])
    _check(
        [x["id"] for x in M.list_numeric_anchors(led)] == ["X-num"], "inclusion rule"
    )


# ── rule precedence ──────────────────────────────────────────────────────────


def _rows(led):
    return {r["id"]: r for r in M.classify_all(led)}


def test_rule_fit_beats_everything():
    led = _ledger(
        [
            _anchor("FIT-x", predicted_value=3.0, prediction_chain=["INST-p"]),
            _anchor(
                "PRED-y",
                predicted_value=1.0,
                independent=False,
                provenance_kind="proof",
            ),
        ],
        inputs=[{"id": "INST-p", "name": "p", "type": "input", "status": "measurable"}],
    )
    r = _rows(led)
    _check(
        r["FIT-x"]["tag"] == "SELECTED" and r["FIT-x"]["rule"] == "R-FIT", "FIT- prefix"
    )
    _check(r["PRED-y"]["rule"] == "R-FIT", "independent:false")
    _check(r["FIT-x"]["ac3_note"] == M.G2_TRIVIAL_NOTE, "AC3 note on SELECTED")


def test_effective_free_parameter_direct_and_inherited_with_dof():
    # AC4 Q4: a free parameter in the chain never changes the OWN tag; it sets the EFFECTIVE
    # tag to SELECTED (direct or inherited) and the closure-wide dof.
    led = _ledger(
        [
            _anchor(
                "MEAS-a", predicted_value=1.0, prediction_chain=["INST-p", "PROOF-q"]
            ),
            _anchor("MEAS-b", predicted_value=1.0, prediction_chain=["MEAS-a"]),
            _anchor(
                "MEAS-c", predicted_value=1.0, prediction_chain=["MEAS-a", "INST-r"]
            ),
            _anchor("PROOF-q", predicted_value=7),
        ],
        inputs=[
            {"id": "INST-p", "name": "p", "type": "input", "status": "measurable"},
            {"id": "INST-r", "name": "r", "type": "input", "status": "irreducible"},
        ],
    )
    r = _rows(led)
    for aid in ("MEAS-a", "MEAS-b", "MEAS-c"):
        _check(r[aid]["tag_effective"] == "SELECTED", f"{aid}: effective SELECTED")
        _check(r[aid]["ac3_note"] == M.G2_TRIVIAL_NOTE, f"{aid}: AC3 note on effective")
    # direct: the record's OWN chain names the input => own SELECTED (R-FREE)
    _check(
        r["MEAS-a"]["tag"] == "SELECTED"
        and r["MEAS-a"]["rule"] == "R-FREE"
        and r["MEAS-a"]["free_params_own"] == ["INST-p"]
        and r["MEAS-a"]["dof"] == 1
        and r["MEAS-a"]["effective_via"] == [],
        "direct INST => own SELECTED, nothing on the chain lowered it further",
    )
    # inherited only: own tag ignores the inheritance; the effective side carries it
    _check(
        r["MEAS-b"]["tag"] == "UNDECIDED"
        and r["MEAS-b"]["rule"] == "default"
        and r["MEAS-b"]["free_params_own"] == []
        and r["MEAS-b"]["dof"] == 1
        and r["MEAS-b"]["effective_via"] == ["INST-p", "MEAS-a"],
        "inherited INST: own UNDECIDED, effective SELECTED via MEAS-a and INST-p",
    )
    _check(
        r["MEAS-c"]["rule"] == "R-FREE"
        and r["MEAS-c"]["free_params_own"] == ["INST-r"]
        and r["MEAS-c"]["dof"] == 2
        and r["MEAS-c"]["free_params"] == ["INST-p", "INST-r"],
        "direct INST-r + inherited INST-p: dof=2",
    )
    _check(
        r["PROOF-q"]["tag"] == "UNDECIDED"
        and r["PROOF-q"]["tag_effective"] == "UNDECIDED"
        and r["PROOF-q"]["effective_via"] == [],
        "no chain: effective == own, nothing set it",
    )


def test_effective_cycle_terminates():
    led = _ledger(
        [
            _anchor("A-1", predicted_value=1, prediction_chain=["A-2"]),
            _anchor("A-2", predicted_value=1, prediction_chain=["A-1", "INST-p"]),
        ],
        inputs=[{"id": "INST-p", "name": "p", "type": "input", "status": "measurable"}],
    )
    r = _rows(led)
    _check(
        r["A-1"]["tag_effective"] == "SELECTED"
        and r["A-2"]["tag_effective"] == "SELECTED",
        "cycle-safe closure",
    )


def test_effective_weakest_link_fixture():
    """The AC4 Q4 fixture: SELECTED ancestor / dangling ancestor / clean FORCED chain /
    UNDECIDED ancestor / neutral non-anchor node. SELECTED < UNDECIDED < FORCED."""
    led = _ledger(
        [
            # leaves
            _anchor(
                "OBS-ext", measured_value=1.0, provenance_kind="experiment"
            ),  # FORCED R-EXT
            _anchor(
                "OBS-sel", predicted_value=1.0, independent=False
            ),  # SELECTED R-FIT
            _anchor("PRED-und", predicted_value=2.0),  # UNDECIDED default
            # (1) clean FORCED chain: measured-only over a FORCED leaf and resolved non-anchor
            #     terminals (a derived principle and an axiom) — neutral, never lowering
            _anchor(
                "Q-forced",
                measured_value=3.0,
                prediction_chain=["OBS-ext", "DERIV-neutral", "AXIOM-1"],
            ),
            # (2) SELECTED ancestor lowers a FORCED own tag to SELECTED
            _anchor(
                "Q-sel", measured_value=3.0, prediction_chain=["OBS-ext", "OBS-sel"]
            ),
            # (3) dangling ancestor lowers FORCED to UNDECIDED and is named
            _anchor("Q-dang", measured_value=3.0, prediction_chain=["PROOF-missing"]),
            # (4) UNDECIDED ancestor lowers FORCED to UNDECIDED
            _anchor("Q-und", measured_value=3.0, prediction_chain=["PRED-und"]),
            # (5) SELECTED own stays SELECTED over a dangling ancestor (min), dangling still named
            _anchor(
                "FIT-dang", predicted_value=1.0, prediction_chain=["PROOF-missing"]
            ),
            # (6) inherited through a non-numeric anchor
            _anchor("PROOF-nonnumeric", prediction_chain=["OBS-sel"]),
            _anchor(
                "Q-via-nonnum",
                measured_value=1.0,
                prediction_chain=["PROOF-nonnumeric"],
            ),
        ],
        derived_principles=[{"id": "DERIV-neutral", "statement": "neutral node"}],
        axioms=[{"id": "AXIOM-1", "statement": "root"}],
    )
    r = _rows(led)
    _check("PROOF-nonnumeric" not in r, "non-numeric anchor is not a row")
    rep = M.dangling_report(led)
    _check(
        {d["id"] for d in rep["dangling"]} == {"PROOF-missing"}
        and {e["id"]: e["collection"] for e in rep["resolved_elsewhere"]}
        == {"DERIV-neutral": "derived_principles", "AXIOM-1": "axioms"},
        "AXIOM-1 / DERIV-neutral resolve in their sections, not dangling",
    )
    q = r["Q-forced"]
    _check(
        q["tag"] == "FORCED"
        and q["tag_effective"] == "FORCED"
        and q["effective_via"] == []
        and q["dangling"] == []
        and q["dof"] == 0,
        "clean FORCED chain stays FORCED; AXIOM-1 and the DERIV node are terminals",
    )
    q = r["Q-sel"]
    _check(
        q["tag"] == "FORCED"
        and q["tag_effective"] == "SELECTED"
        and q["effective_via"] == ["OBS-sel"]
        and q["ac3_note"] == M.G2_TRIVIAL_NOTE,
        "SELECTED ancestor => effectively SELECTED (via named, AC3 note carried)",
    )
    q = r["Q-dang"]
    _check(
        q["tag"] == "FORCED"
        and q["tag_effective"] == "UNDECIDED"
        and q["effective_via"] == ["PROOF-missing"]
        and q["dangling"] == ["PROOF-missing"],
        "dangling ancestor => UNDECIDED-until-resolved, id named",
    )
    q = r["Q-und"]
    _check(
        q["tag_effective"] == "UNDECIDED" and q["effective_via"] == ["PRED-und"],
        "UNDECIDED ancestor lowers FORCED",
    )
    q = r["FIT-dang"]
    _check(
        q["tag"] == "SELECTED"
        and q["tag_effective"] == "SELECTED"
        and q["effective_via"] == []
        and q["dangling"] == ["PROOF-missing"],
        "SELECTED is already the minimum; dangling id still reported",
    )
    q = r["Q-via-nonnum"]
    _check(
        q["tag_effective"] == "SELECTED" and q["effective_via"] == ["OBS-sel"],
        "closure continues through a non-numeric anchor",
    )
    for x in r.values():
        _check(
            M.TAG_RANK[x["tag_effective"]] <= M.TAG_RANK[x["tag"]],
            f"{x['id']}: effective never stronger than own",
        )
    s = M.summarize(list(r.values()))
    _check(
        s["moves"] == {"FORCED→SELECTED": 2, "FORCED→UNDECIDED": 2},
        f"moves tally: {s['moves']}",
    )
    _check(
        s["dangling_ids_in_scope"] == {"PROOF-missing": 2}
        and s["rows_with_dangling_ancestor"] == 2,
        "dangling summary",
    )


def test_dangling_report_reconciles_not_in_anchors_vs_dangling():
    led = _ledger(
        [
            _anchor(
                "PRED-n",
                predicted_value=1.0,
                prediction_chain=["INST-p", "DERIV-d", "AX-1", "PROOF-gone", "PRED-m"],
            ),
            _anchor("PRED-m", predicted_value=1.0, prediction_chain=["PROOF-gone"]),
            # non-numeric anchor: its dangling ref is ledger-wide but NOT in numeric scope
            _anchor("NOTE-x", prediction_chain=["DERIV-orphan"]),
        ],
        inputs=[{"id": "INST-p", "name": "p", "type": "input", "status": "measurable"}],
        derived_principles=[{"id": "DERIV-d"}],
        axioms=[{"id": "AX-1"}],
    )
    resolv = M.resolvable_ids(led)
    _check(
        resolv["INST-p"] == "inputs"
        and resolv["DERIV-d"] == "derived_principles"
        and resolv["AX-1"] == "axioms"
        and resolv["PRED-n"] == "anchors"
        and "PROOF-gone" not in resolv,
        "ids resolve to their collection",
    )
    rep = M.dangling_report(led)
    dang = {d["id"]: d for d in rep["dangling"]}
    els = {e["id"]: e for e in rep["resolved_elsewhere"]}
    _check(set(dang) == {"PROOF-gone", "DERIV-orphan"}, f"dangling set: {set(dang)}")
    _check(set(els) == {"INST-p", "DERIV-d", "AX-1"}, f"resolved elsewhere: {set(els)}")
    _check(
        dang["PROOF-gone"]["refs"] == 2
        and dang["PROOF-gone"]["referrers"] == ["PRED-m", "PRED-n"]
        and dang["PROOF-gone"]["numeric_rows"] == ["PRED-m", "PRED-n"]
        and dang["PROOF-gone"]["in_numeric_scope"],
        "direct refs + numeric closure reach",
    )
    _check(
        dang["DERIV-orphan"]["refs"] == 1
        and not dang["DERIV-orphan"]["in_numeric_scope"],
        "a dangling id reached only by a non-numeric anchor is ledger-wide, not in scope",
    )
    _check(
        els["AX-1"]["collection"] == "axioms"
        and els["AX-1"]["numeric_rows"] == ["PRED-n"],
        "resolved-elsewhere rows carry their collection",
    )
    _check(
        rep["dangling"][0]["refs"] >= rep["dangling"][-1]["refs"],
        "sorted by ref count desc",
    )
    out = M.render_dangling(rep)
    _check(
        "2 ledger-wide, 1 reachable" in out and "total not-in-anchors = 5" in out,
        f"render header: {out.splitlines()[:2]}",
    )


def test_rule_ext_requires_empty_chain_external_kind_and_no_predicted_side():
    led = _ledger(
        [
            # S1 guard: empty chain + experiment kind BUT a QBP-side predicted number -> default
            _anchor(
                "OBS-e",
                measured_value=5.0,
                predicted_value=5.0,
                provenance_kind="experiment",
            ),
            _anchor("REF-t", predicted_value=100, provenance_kind="theory-external"),
            _anchor(
                "OBS-f",
                measured_value=5.0,
                predicted_value=5.0,
                provenance_kind="experiment",
                prediction_chain=["DERIV-z"],
            ),
            _anchor("OBS-g", measured_value=5.0, provenance_kind="theory"),
            # the genuine R-EXT shape: measured only, empty chain, external kind
            _anchor(
                "OBS-h",
                measured_value=5.0,
                measured_error=0.1,
                provenance_kind="experiment",
            ),
        ]
    )
    r = _rows(led)
    _check(r["OBS-e"]["rule"] == "default", "predicted-side number blocks R-EXT (S1)")
    _check(
        r["REF-t"]["rule"] == "default",
        "theory-external with a predicted number -> default",
    )
    _check(
        r["OBS-f"]["rule"] == "default",
        "non-empty chain with a predicted side => UNDECIDED",
    )
    _check(
        r["OBS-g"]["rule"] == "R-MEAS",
        "theory kind: R-EXT does not fire; measured only => R-MEAS",
    )
    _check(
        r["OBS-h"]["rule"] == "R-EXT" and r["OBS-h"]["tag"] == "FORCED",
        "measured only, empty chain, experiment => R-EXT",
    )


def test_rule_ext_guard_and_precedence_over_meas():
    led = _ledger(
        [
            # experiment kind, measured only, empty chain -> R-EXT (before R-MEAS)
            _anchor("OBS-p", measured_value=1.0, provenance_kind="experiment"),
            # S1: empty chain + external kind but a QBP-side predicted number -> UNDECIDED
            _anchor(
                "INSIGHT-q",
                measured_value=0.1111,
                predicted_value=0.1111,
                provenance_kind="theory-external",
            ),
        ]
    )
    r = _rows(led)
    _check(r["OBS-p"]["rule"] == "R-EXT", "R-EXT precedes R-MEAS")
    _check(
        r["INSIGHT-q"]["rule"] == "default", "predicted-side number blocks R-EXT (S1)"
    )


def test_forced_rows_never_carry_free_params():
    # K2 after the Q4 split: a FORCED OWN tag never names an own free parameter, and a
    # FORCED EFFECTIVE tag has dof 0. A FORCED override whose chain reaches a free
    # parameter keeps its own tag and becomes effectively SELECTED with that dof.
    real = M.load_ledger(M.DEFAULT_LEDGER)
    led = copy.deepcopy(real)
    for a in led["anchors"]:
        if a["id"] == "PROOF-stelle-no-linear":
            a["prediction_chain"] = ["INST-f0"]
    r = {x["id"]: x for x in M.classify_all(led)}["PROOF-stelle-no-linear"]
    _check(r["tag"] == "FORCED" and r["free_params_own"] == [], "own K2 invariant")
    _check(
        r["tag_effective"] == "SELECTED"
        and r["effective_via"] == ["INST-f0"]
        and r["free_params"] == ["INST-f0"]
        and r["dof"] == 1,
        "effective side carries the inherited parameter",
    )
    for x in M.classify_all(real):
        _check(
            x["tag_effective"] != "FORCED" or x["dof"] == 0,
            f"{x['id']}: FORCED-effective with dof>0",
        )


def test_rule_meas_needs_measured_and_no_predicted_side():
    led = _ledger(
        [
            _anchor(
                "Q-m", measured_value=2.2, measured_error=0.2, prediction_chain=["X"]
            ),
            _anchor(
                "Q-n",
                measured_value=2.2,
                predicted_value_lo=1.0,
                prediction_chain=["X"],
            ),
            _anchor("Q-o", discrepancy_pct=3.0, prediction_chain=["X"]),
        ]
    )
    r = _rows(led)
    _check(
        r["Q-m"]["rule"] == "R-MEAS" and r["Q-m"]["tag"] == "FORCED", "measured only"
    )
    _check(r["Q-n"]["rule"] == "default", "a predicted-side field blocks R-MEAS")
    _check(r["Q-o"]["rule"] == "default", "no measured_value => not R-MEAS")


def test_rule_thm_needs_proof_kind_lean_zero_sorry_verified():
    good = _anchor(
        "PRED-t",
        predicted_value=69.3,
        provenance_kind="proof",
        lean_theorem="T.thm",
        sorry_count=0,
        verification={"result": "verified"},
    )
    bad_sorry = dict(good, id="PRED-u", sorry_count=1)
    bad_kind = dict(good, id="PRED-v", provenance_kind="theory")
    bad_ver = dict(good, id="PRED-w", verification={"result": "pending"})
    r = _rows(_ledger([good, bad_sorry, bad_kind, bad_ver]))
    _check(
        r["PRED-t"]["rule"] == "R-THM" and r["PRED-t"]["tag"] == "UNDECIDED", "R-THM"
    )
    for aid in ("PRED-u", "PRED-v", "PRED-w"):
        _check(r[aid]["rule"] == "default", f"{aid} must fall to default")


# ── overrides ────────────────────────────────────────────────────────────────


def test_override_quote_drift_raises():
    real = M.load_ledger(M.DEFAULT_LEDGER)
    # Every override, not just the first (Red Team K7).
    for aid, (_tag, field, _quote, _p, _b) in M.OVERRIDES.items():
        drifted = copy.deepcopy(real)
        for a in drifted["anchors"]:
            if a["id"] == aid:
                a[field] = "text without the quote"
        errs, missing = M.verify_overrides(drifted)
        _check(any(aid in e for e in errs), f"{aid}: drifted quote must be reported")
        _check(missing == [], "a drifted quote is drift, not a missing anchor")
        try:
            M.classify_all(drifted)
        except ValueError as exc:
            _check(aid in str(exc), "classify_all raises naming the anchor")
        else:
            raise AssertionError(f"{aid}: classify_all must raise on override drift")


def test_override_missing_anchor_reported():
    led = _ledger([_anchor("X-1", predicted_value=1)])
    errs, missing = M.verify_overrides(led)
    _check(errs == [], "missing anchors are not drift errors")
    _check(sorted(missing) == sorted(M.OVERRIDES), "every override id reported missing")
    _check(
        len(M.classify_all(led)) == 1, "classify_all still runs on a synthetic ledger"
    )


def test_override_selected_introduces_free_parameter_for_dependents():
    real = M.load_ledger(M.DEFAULT_LEDGER)
    rows = {r["id"]: r for r in M.classify_all(real)}
    # PRED-f4-zero-vacuum-energy depends (via prediction_chain) on PRED-lambda-as-cross-term,
    # whose record declares z_t = 0.7 a calibrated INPUT.
    r = rows["PRED-f4-zero-vacuum-energy"]
    _check(
        r["tag"] == "UNDECIDED"
        and r["tag_effective"] == "SELECTED"
        and r["effective_via"] == ["PRED-lambda-as-cross-term"]
        and "z_t = 0.7 (calibrated input)" in r["free_params"]
        and r["free_params_own"] == [],
        "override-SELECTED node propagates its parameter along the chain (effective side)",
    )


# ── real ledger invariants ───────────────────────────────────────────────────


def test_real_ledger_invariants():
    real = M.load_ledger(M.DEFAULT_LEDGER)
    _check(
        M.verify_overrides(real) == ([], []),
        "all override quotes live in the real ledger",
    )
    rows = M.classify_all(real)
    numeric_ids = {a["id"] for a in M.list_numeric_anchors(real)}
    _check({r["id"] for r in rows} == numeric_ids, "one row per numeric anchor")
    _check(len(rows) == len(numeric_ids), "no duplicate rows")
    resolv = M.resolvable_ids(real)
    for r in rows:
        _check(r["tag"] in M.TAGS, f"{r['id']}: tag {r['tag']!r} not in enum")
        _check(r["tag_effective"] in M.TAGS, f"{r['id']}: effective tag not in enum")
        _check(
            M.TAG_RANK[r["tag_effective"]] <= M.TAG_RANK[r["tag"]],
            f"{r['id']}: effective stronger than own",
        )
        _check(
            (r["tag_effective"] != r["tag"]) == bool(r["effective_via"]),
            f"{r['id']}: effective_via iff the chain moved the tag",
        )
        _check(
            (r["ac3_note"] is not None) == (r["tag_effective"] == "SELECTED"),
            f"{r['id']}: AC3 note follows the effective tag",
        )
        _check(r["dof"] == len(r["free_params"]), f"{r['id']}: dof mismatch")
        _check(
            set(r["free_params_own"]) <= set(r["free_params"])
            or r["tag_effective"] == "FORCED",
            f"{r['id']}: own params are part of the closure params",
        )
        _check(
            r["tag"] != "FORCED" or r["free_params_own"] == [],
            f"{r['id']}: FORCED own with an own free parameter (K2)",
        )
        _check(
            r["tag_effective"] != "FORCED" or r["dof"] == 0,
            f"{r['id']}: FORCED effective with dof>0 (K2)",
        )
        _check(
            (r["tag"] == "FORCED")
            == r["basis"].startswith(("external-", "measurement-only")),
            f"{r['id']}: FORCED <-> external/measurement basis",
        )
        _check(
            r["tag"] != "SELECTED" or r["free_params_own"] or r["rule"] == "R-FIT",
            f"{r['id']}: SELECTED own without a named free parameter",
        )
        _check(
            r["tag_effective"] != "SELECTED" or r["dof"] >= 1 or r["rule"] == "R-FIT",
            f"{r['id']}: SELECTED effective without a free parameter in the closure",
        )
        for d in r["dangling"]:
            _check(d not in resolv, f"{r['id']}: {d} reported dangling but resolves")
        _check(
            not r["dangling"] or r["tag_effective"] != "FORCED",
            f"{r['id']}: FORCED effective over a dangling ancestor",
        )
    by_id = {r["id"]: r for r in rows}
    # K3: R-OVR wins over R-INST on the same anchor, and the inherited parameter is kept.
    r = by_id["PRED-inv-alpha-GUT-16pi"]
    _check(
        r["rule"] == "R-OVR"
        and r["tag"] == "SELECTED"
        and r["free_params_own"]
        == ["algebraic-expression choice (closest of candidates)"]
        and r["dof"] == 2,
        "R-OVR own parameter + inherited z_t on the effective side, dof 2",
    )
    # G1: the two mixed-container anchors are in the census.
    _check(
        {"PRED-a0-redshift-linear", "PRED-btfr-mass-correction"} <= set(by_id),
        "mixed experimental_backing anchors included (G1)",
    )
    s = M.summarize(rows)
    _check(sum(s["tags"].values()) == len(rows), "own tag counts sum to total")
    _check(
        sum(s["tags_effective"].values()) == len(rows), "effective counts sum to total"
    )
    _check(sum(s["tag_basis"].values()) == len(rows), "tag/basis counts sum to total")
    _check(
        s["free_choice_count"] == s["tags_effective"]["SELECTED"]
        and s["free_choice_count_own"] == s["tags"]["SELECTED"],
        "free-choice counts = SELECTED (effective / own)",
    )
    _check(
        sum(s["moves"].values())
        == sum(1 for r in rows if r["tag"] != r["tag_effective"]),
        "moves tally",
    )
    # Dangling report is consistent with the collections and with the rows.
    rep = M.dangling_report(real)
    dang_ids = {d["id"] for d in rep["dangling"]}
    chain_ids = {c for a in real["anchors"] for c in a.get("prediction_chain", [])}
    anchor_ids = {a["id"] for a in real["anchors"]}
    _check(
        dang_ids | {e["id"] for e in rep["resolved_elsewhere"]}
        == chain_ids - anchor_ids,
        "dangling + resolved-elsewhere = every chain id outside anchors[]",
    )
    _check(
        all(d not in resolv for d in dang_ids)
        and all(
            e["collection"] not in (None, "anchors") for e in rep["resolved_elsewhere"]
        ),
        "dangling resolve nowhere; the rest resolve in a non-anchor collection",
    )
    _check(
        set(s["dangling_ids_in_scope"])
        == {d["id"] for d in rep["dangling"] if d["in_numeric_scope"]},
        "rows' dangling ids == report's numeric-scope dangling ids",
    )
    # Known inclusion edge: the bookkeeping-only PROOF- anchors must NOT appear.
    for a in real["anchors"]:
        if a["id"] not in numeric_ids:
            _check(
                M.numeric_fields(a) == {}, f"{a['id']} excluded but has numeric fields"
            )


# ── CLI ──────────────────────────────────────────────────────────────────────


def test_discover_ledger_picks_latest_v03_only():
    with tempfile.TemporaryDirectory() as td:
        for name in (
            "confluent-trust-inventory-v5_3.json",  # legacy raw: must be ignored
            "confluent-trust-inventory-v5.13.json",  # legacy raw: must be ignored
            "confluent-trust-inventory-v5_3.v0.3.json",
            "confluent-trust-inventory-v6_0.v0.3.json",
        ):
            open(os.path.join(td, name), "w").close()
        picked = os.path.basename(M.discover_ledger(td))
        _check(
            picked == "confluent-trust-inventory-v6_0.v0.3.json",
            f"latest v0.3 picked: {picked}",
        )
    with tempfile.TemporaryDirectory() as empty:
        _check(
            M.discover_ledger(empty).endswith("v5_3.v0.3.json"),
            "fallback name when none",
        )
    _check(os.path.isfile(M.DEFAULT_LEDGER), "discovered default exists in the repo")
    _check(M.DEFAULT_LEDGER.endswith(".v0.3.json"), "default is the v0.3 ledger")


def test_cli_md_json_summary():
    out = subprocess.run(
        [sys.executable, SCRIPT, "--summary"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    _check("free-choice count (SELECTED tags):" in out, "summary line")
    js = subprocess.run(
        [sys.executable, SCRIPT, "--format", "json"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    data = json.loads(js)
    _check(
        len(data["rows"]) == data["summary"]["numeric_anchors"], "json rows == count"
    )
    _check(
        "effective tags:" in out and "own tags:" in out, "summary shows both columns"
    )
    _check(
        {"dangling", "resolved_elsewhere"} <= set(data["dangling"]),
        "json carries the dangling report",
    )
    md = subprocess.run(
        [sys.executable, SCRIPT], capture_output=True, text=True, check=True
    ).stdout
    _check(
        sum(1 for line in md.splitlines() if re.match(r"^\| \d+ \| `", line))
        == data["summary"]["numeric_anchors"],
        "one table row per anchor",
    )
    _check("| Own tag | Basis | Rule | Effective tag |" in md, "both tag columns")
    eff = subprocess.run(
        [sys.executable, SCRIPT, "--effective"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    _check(
        sum(1 for line in eff.splitlines() if re.match(r"^\| \d+ \| `", line))
        == data["summary"]["numeric_anchors"],
        "--effective: one row per anchor",
    )
    dang = subprocess.run(
        [sys.executable, SCRIPT, "--dangling"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    n_d = len(data["dangling"]["dangling"])
    _check(
        dang.startswith(f"Dangling `prediction_chain` ids")
        and f"{n_d} ledger-wide" in dang
        and sum(1 for line in dang.splitlines() if line.startswith("| `"))
        == n_d + len(data["dangling"]["resolved_elsewhere"]),
        "--dangling: header count + one table row per non-anchor chain id",
    )


def test_cli_fails_on_drifted_ledger():
    real = M.load_ledger(M.DEFAULT_LEDGER)
    aid, (_t, field, _q, _p, _b) = next(iter(M.OVERRIDES.items()))
    for a in real["anchors"]:
        if a["id"] == aid:
            a[field] = "drifted"
    with tempfile.TemporaryDirectory() as td:
        p = os.path.join(td, "l.json")
        with open(p, "w", encoding="utf-8") as fh:
            json.dump(real, fh)
        res = subprocess.run(
            [sys.executable, SCRIPT, "--ledger", p, "--summary"],
            capture_output=True,
            text=True,
        )
    _check(
        res.returncode == 1 and "OVERRIDES drifted" in res.stderr,
        "CLI exits 1 on drift",
    )
    res2 = subprocess.run(
        [sys.executable, SCRIPT, "--ledger", "/nonexistent/ledger.json", "--summary"],
        capture_output=True,
        text=True,
    )
    _check(
        res2.returncode == 2 and "cannot read ledger" in res2.stderr,
        "CLI exits 2 on bad path",
    )
    res3 = subprocess.run(
        [sys.executable, SCRIPT, "--summary", "--format", "json"],
        capture_output=True,
        text=True,
    )
    _check(res3.returncode == 2, "--summary and --format are mutually exclusive")
    res4 = subprocess.run(
        [sys.executable, SCRIPT, "--dangling", "--effective"],
        capture_output=True,
        text=True,
    )
    _check(res4.returncode == 2, "--dangling and --effective are mutually exclusive")


if __name__ == "__main__":
    tests = [
        v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)
    ]
    failed = 0
    for t in tests:
        try:
            t()
            print(f"PASS {t.__name__}")
        except Exception as exc:  # noqa: BLE001 — report every failure
            failed += 1
            print(f"FAIL {t.__name__}: {exc}")
    print(f"{len(tests) - failed}/{len(tests)} passed")
    sys.exit(1 if failed else 0)
