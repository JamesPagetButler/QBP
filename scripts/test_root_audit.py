"""Tests for root_audit.py's report-only PA surfacing (PR-2, Refs #692).

The whole point of this change is that it is REPORT-ONLY: it surfaces each PROOF-*/MEAS-
ground's proof-assurance grade (pa_local / pa_effective) next to the proof_state/status
verdict root_audit already uses, and feeds NOTHING — not sort_root, not the buckets, not
the chain-termination verdict, not the failures, not the exit code. These tests pin that
invariance (so a future edit that quietly turns it into a gate fails here), and check the
two surfacing helpers + the tally.
"""

import importlib.util
import pathlib

_spec = importlib.util.spec_from_file_location(
    "root_audit", pathlib.Path(__file__).resolve().parent / "root_audit.py"
)
ra = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ra)


def _anchor(aid, **kw):
    a = {"id": aid}
    a.update(kw)
    return a


def _anchors(*anchs):
    return {a["id"]: a for a in anchs}


# ---- report-only invariance: PA never changes the gate's decision --------------------


def test_sort_root_bucket_invariant_to_pa():
    """sort_root buckets a PROOF-forced root identically whatever the ground's PA is
    (or absent): the decision reads proof_state, never pa_*."""
    rec = {"id": "AXIOM-X", "forced_by": ["PROOF-y"]}
    mk = lambda **pa: _anchors(
        _anchor("PROOF-y", proof_state="verified", status="coherent", **pa)
    )
    b0, _ = ra.sort_root(rec, mk(pa_local=0, pa_effective=0))
    b2, _ = ra.sort_root(rec, mk(pa_local=2, pa_effective=2))
    bN, _ = ra.sort_root(rec, mk())  # no pa fields at all
    assert b0 == b2 == bN == 1  # PROVED regardless of PA


def test_forces_flag_independent_of_pa():
    """Mutation sentinel: forcing_grounds_pa's `forces` must NOT depend on pa_effective.
    A PA-gate (the thing this PR deliberately does NOT do) would break this test."""
    mk = lambda pe: ra.forcing_grounds_pa(
        {"id": "AXIOM-X", "forced_by": ["PROOF-v"]},
        _anchors(
            _anchor(
                "PROOF-v", proof_state="verified", status="coherent", pa_effective=pe
            )
        ),
    )[0]["forces"]
    assert mk(0) is True and mk(2) is True and mk(None) is True


def test_audit_report_only_invariance():
    """End-to-end: audit()'s gate outputs (roots, failures) are byte-identical whether the
    forcing proof is PA-0, PA-2, or carries no PA field — while terminator_pa DOES reflect
    the PA value. This is the report-only guarantee at the top level."""

    def ledger(pe, with_pa=True):
        anc = {
            "id": "PROOF-y",
            "proof_state": "verified",
            "status": "coherent",
            "prediction_chain": [],
        }
        if with_pa:
            anc["pa_local"] = pe
            anc["pa_effective"] = pe
        return {
            "axioms": [{"id": "AXIOM-X", "forced_by": ["PROOF-y"]}],
            "anchors": [anc],
        }

    r0 = ra.audit(ledger(0), {}, {}, [])
    r2 = ra.audit(ledger(2), {}, {}, [])
    rN = ra.audit(ledger(0, with_pa=False), {}, {}, [])
    for key in ("roots", "failures"):
        assert r0[key] == r2[key] == rN[key], f"gate output {key} changed with PA"
    assert r0["roots"]["AXIOM-X"][1] == 1  # PROVED, forced by the verified proof
    assert not r0["failures"]
    # PA is nonetheless surfaced and tracks the value
    assert ra._pa_tally(r0["terminator_pa"])[0] == 1
    assert ra._pa_tally(r2["terminator_pa"])[2] == 1
    assert ra._pa_tally(rN["terminator_pa"])[None] == 1


# ---- forcing_grounds_pa: surfacing + the per-ground forces flag ----------------------


def test_forcing_grounds_pa_surfaces_and_flags():
    anchors = _anchors(
        _anchor(
            "PROOF-v",
            proof_state="verified",
            status="coherent",
            pa_local=0,
            pa_effective=0,
        ),
        _anchor(
            "PROOF-u",
            proof_state="unverified",
            status="coherent",
            pa_local=2,
            pa_effective=2,
        ),
        _anchor("MEAS-c", status="converged", pa_effective=1),
        _anchor("MEAS-x", status="marginal", pa_effective=2),
        _anchor("PROOF-dead", proof_state="verified", status="killed", pa_effective=2),
    )
    rec = {
        "id": "AXIOM-X",
        "forced_by": [
            "PROOF-v",
            "PROOF-u",
            "MEAS-c",
            "MEAS-x",
            "PROOF-dead",
            "DERIV-skip",
            "INSIGHT-skip",
        ],
    }
    by = {r["id"]: r for r in ra.forcing_grounds_pa(rec, anchors)}
    # only PROOF-*/MEAS- grounds are surfaced; DERIV-/INSIGHT- skipped
    assert set(by) == {"PROOF-v", "PROOF-u", "MEAS-c", "MEAS-x", "PROOF-dead"}
    assert by["PROOF-v"]["forces"] is True and by["PROOF-v"]["pa_effective"] == 0
    assert by["PROOF-u"]["forces"] is False  # unverified PROOF does not force
    assert by["MEAS-c"]["forces"] is True  # converged MEAS forces
    assert by["MEAS-x"]["forces"] is False  # marginal MEAS does not force
    assert by["PROOF-dead"]["forces"] is False  # dead anchor forces nothing


def test_forces_matches_sort_root():
    """Drift guard: the per-ground `forces` flag agrees with sort_root's bucketing, so a
    future change to sort_root's forcing rule that isn't mirrored here is caught."""
    v = _anchors(_anchor("PROOF-v", proof_state="verified", status="coherent"))
    u = _anchors(_anchor("PROOF-u", proof_state="unverified", status="coherent"))
    rec_v = {"id": "AXIOM-A", "forced_by": ["PROOF-v"]}
    rec_u = {"id": "AXIOM-B", "forced_by": ["PROOF-u"]}
    assert ra.sort_root(rec_v, v)[0] == 1
    assert ra.forcing_grounds_pa(rec_v, v)[0]["forces"] is True
    assert ra.sort_root(rec_u, u)[0] is None  # weak: unsorted
    assert ra.forcing_grounds_pa(rec_u, u)[0]["forces"] is False


def test_forcing_grounds_pa_missing_anchor():
    """A forced_by id that doesn't resolve in-ledger is still listed (forces False, PA None)
    — report-only never raises; sort_root is what fails the root for the missing id."""
    rows = ra.forcing_grounds_pa({"id": "AXIOM-X", "forced_by": ["PROOF-gone"]}, {})
    assert rows == [
        {"id": "PROOF-gone", "pa_local": None, "pa_effective": None, "forces": False}
    ]


# ---- terminator_pa: the full terminator pool -----------------------------------------


def test_terminator_pa_pool():
    anchors = _anchors(
        _anchor(
            "PROOF-a",
            proof_state="verified",
            status="coherent",
            pa_local=0,
            pa_effective=0,
        ),
        _anchor(
            "PROOF-b", proof_state="verified", status="killed", pa_effective=2
        ),  # dead
        _anchor("MEAS-c", status="converged", pa_effective=2),
        _anchor("DERIV-d", pa_effective=2),  # not a terminal prefix
        _anchor("AXIOM-e", pa_effective=2),  # not a terminal prefix
        _anchor("PROOF-n", proof_state="verified", status="coherent"),  # no pa field
    )
    by = {r["id"]: r for r in ra.terminator_pa(anchors)}
    # dead + non-terminal-prefix anchors are excluded (is_terminal rejects them)
    assert set(by) == {"PROOF-a", "MEAS-c", "PROOF-n"}
    assert by["PROOF-a"]["pa_effective"] == 0 and by["PROOF-a"]["pa_local"] == 0
    assert by["MEAS-c"]["status"] == "converged"
    assert by["PROOF-n"]["pa_effective"] is None  # missing field surfaces as None


def test_pa_tally():
    rows = [
        {"pa_effective": 0},
        {"pa_effective": 0},
        {"pa_effective": 2},
        {"pa_effective": None},
    ]
    t = ra._pa_tally(rows)
    assert t[0] == 2 and t[2] == 1 and t[None] == 1


if __name__ == "__main__":
    import sys

    import pytest

    sys.exit(pytest.main([__file__, "-v"]))
