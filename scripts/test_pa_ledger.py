#!/usr/bin/env python3
"""QBP#692 strike-2 — the REAL-LEDGER reconcile, driving the Go `pa-reconcile` gate.

Run: python3 -m pytest scripts/test_pa_ledger.py -v   (needs go, git, pyyaml)

Where `test_pa_encoder.py` pins the ENCODER (the writer) on fixtures, this pins the
real committed ledger against the Go `pa-reconcile` gate (the checker), on real data:

  AC2  CI `pa-reconcile` recomputes PA with the vendored CTH engine at the pinned ledger
       version and FAILS (exit 3) on any difference from a committed grade. The claims
       fed to the gate are built by the encoder's OWN claim-construction (grade_ledger →
       `out["_claims"]`), so checker and writer never diverge on how a claim is shaped.
       - test_real_ledger_reconciles_clean    : committed == recompute ⇒ exit 0, no diffs
       - test_planted_hand_edit_fails          : a hand-flipped committed grade ⇒ exit 3
  AC3  spot values on the real ledger at INTER_PIN: an internal-compute anchor grades 0,
       a derivation anchor at this pin grades 0, the Fano table grades 2.
  invariant  INTER_PIN (pa-reconcile.yml) == the store sha named in the latest dated
       backfill report — the pin moves atomically with the ledger (architect seq 2554).

The evidence store is `JamesPagetButler/inter:notary-evidence/` pinned by INTER_PIN
(public; the private `notary` repo stays record-of-origin — inter#168). CI checks inter
out at INTER_PIN and points INTER_EVIDENCE_DIR at it; locally, set INTER_EVIDENCE_DIR to
a checkout of inter `notary-evidence/` at that pin. Unset ⇒ the real-ledger tests skip
(the invariant test still runs — it needs no checkout).
"""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
ENGINE_DIR = ROOT / "tools/cth-pa"
WORKFLOW = ROOT / ".github/workflows/pa-reconcile.yml"
REPORT_DIR = ROOT / "analysis/692-pa-backfill"
HEX40 = re.compile(r"^[0-9a-f]{40}$")

# Spot anchors (AC3). Fano is the consumer-pinned proof; hessian is internal-compute.
FANO_ID = "PROOF-cd-structure-constant-tables"
HESSIAN_ID = "PROOF-hessian"

_HAVE_GO = shutil.which("go") is not None
_HAVE_GIT = shutil.which("git") is not None
try:  # pyyaml is needed by the encoder we import
    import yaml  # noqa: F401

    _HAVE_YAML = True
except Exception:  # noqa: BLE001
    _HAVE_YAML = False

pytestmark = pytest.mark.skipif(
    not (_HAVE_GO and _HAVE_GIT and _HAVE_YAML),
    reason="needs go, git and pyyaml",
)


def _encoder():
    """Import scripts/encode_pa_from_evidence.py as a module (reuse, never re-implement)."""
    path = ROOT / "scripts/encode_pa_from_evidence.py"
    spec = importlib.util.spec_from_file_location("encode_pa_from_evidence", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _evidence_dir():
    d = os.environ.get("INTER_EVIDENCE_DIR")
    if not d or not Path(d).is_dir():
        pytest.skip(
            "INTER_EVIDENCE_DIR unset — needs inter:notary-evidence checked out at INTER_PIN"
        )
    return Path(d)


def _reconcile_binary():
    """Build tools/cth-pa/cmd/pa-reconcile once (or use $CTH_PA_RECONCILE_BIN)."""
    env = os.environ.get("CTH_PA_RECONCILE_BIN")
    if env:
        return env
    out = Path(tempfile.mkdtemp(prefix="pa-reconcile-")) / "pa-reconcile"
    p = subprocess.run(
        ["go", "build", "-o", str(out), "./cmd/pa-reconcile"],
        cwd=ENGINE_DIR,
        capture_output=True,
        text=True,
    )
    if p.returncode != 0:
        raise RuntimeError(f"go build ./cmd/pa-reconcile failed:\n{p.stderr}")
    return str(out)


def _recompute(evidence_dir, pinned_master=None):
    """Recompute every target anchor via the encoder's own machinery.
    Returns (ledger_dict, results, engine_out). engine_out carries the engine-input
    claims (`_claims`) and edges (`_edges`) the gate will reconcile. pinned_master is the
    commit whose ledger + proofs we check — HEAD in CI (the PR commit), overridable via
    PINNED_MASTER for local runs against another rev."""
    pinned_master = pinned_master or os.environ.get("PINNED_MASTER", "HEAD")
    enc = _encoder()
    commit = enc.resolve_commit(ROOT, pinned_master)
    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    records, _ignored = enc.load_evidence(Path(evidence_dir))
    anchor_ids = {a["id"] for a in ledger["anchors"]}
    target_ids = {a["id"] for a in enc.target_anchors(ledger)}
    kinds = {a["id"]: a.get("provenance_kind") for a in ledger["anchors"]}
    by_claim, _un, _nt = enc.group_by_claim(records, anchor_ids, target_ids, kinds)
    results, engine_out = enc.grade_ledger(ledger, by_claim, ROOT, commit)
    return ledger, results, engine_out


def _reconcile_doc(ledger, engine_out, committed):
    """Build the pa-reconcile stdin doc for the graded+pinned subset.
    `committed` maps claim id -> {pa_local, pa_effective}; the strict gate needs a 40-hex
    pinned_sha, so the 146 un-pinned 0/0 anchors (nothing to verify) are out of the set —
    a hand-edit on THOSE is caught by the encoder reconcile in test_pa_encoder.py."""
    claims = [c for c in engine_out["_claims"] if HEX40.match(c.get("pinned_sha", ""))]
    ids = {c["claim"] for c in claims}
    edges = [e for e in engine_out["_edges"] if e["from"] in ids and e["to"] in ids]
    expect = {}
    for c in claims:
        cid = c["claim"]
        expect[cid] = {
            "required_pa": 0,  # reconcile test: the EMIT path (required_pa) is not exercised
            "committed_pa_local": committed[cid]["pa_local"],
            "committed_pa_effective": committed[cid]["pa_effective"],
            "source_ref": f"JamesPagetButler/QBP@{cid}",
            "pinning_consumer": [],
        }
    return {
        "policy": {"require_signature": False},
        "ledger_version": ledger.get("version", ""),
        "emitted_at": "2026-01-01T00:00:00Z",
        "claims": claims,
        "edges": edges,
        "expect": expect,
    }


def _run_reconcile(doc):
    p = subprocess.run(
        [_reconcile_binary()],
        input=json.dumps(doc),
        capture_output=True,
        text=True,
    )
    out = json.loads(p.stdout) if p.stdout.strip() else {}
    return p.returncode, out, p.stderr


def _committed_grades(ledger):
    return {
        a["id"]: {"pa_local": a["pa_local"], "pa_effective": a["pa_effective"]}
        for a in ledger["anchors"]
        if "pa_local" in a
    }


# --- AC2: the gate reconciles the real ledger clean, and bites on a hand edit ----------


def test_real_ledger_reconciles_clean():
    """The committed grades equal the recompute at INTER_PIN ⇒ gate exits 0, no diffs."""
    ev = _evidence_dir()
    ledger, _results, engine_out = _recompute(ev)
    committed = _committed_grades(ledger)
    doc = _reconcile_doc(ledger, engine_out, committed)
    assert doc["claims"], "expected at least one graded+pinned claim (the Fano anchors)"
    code, out, err = _run_reconcile(doc)
    assert (
        code == 0
    ), f"reconcile should be clean, got exit {code}; diffs={out.get('diffs')}; err={err}"
    assert out.get("diffs") == [], f"unexpected diffs: {out.get('diffs')}"


def test_planted_hand_edit_fails():
    """Flip a committed grade (a hand edit the engine never produced) ⇒ exit 3 + a diff."""
    ev = _evidence_dir()
    ledger, _results, engine_out = _recompute(ev)
    committed = _committed_grades(ledger)
    # pick a graded+pinned anchor (pa_effective >= 1) and plant a lower committed grade
    graded = [
        c["claim"]
        for c in engine_out["_claims"]
        if HEX40.match(c.get("pinned_sha", ""))
        and committed[c["claim"]]["pa_effective"] >= 1
    ]
    assert graded, "need a graded anchor to plant a hand edit on"
    victim = graded[0]
    tampered = copy.deepcopy(committed)
    tampered[victim]["pa_effective"] = tampered[victim]["pa_effective"] - 1  # 2 -> 1
    doc = _reconcile_doc(ledger, engine_out, tampered)
    code, out, err = _run_reconcile(doc)
    assert (
        code == 3
    ), f"a planted hand edit must fail the gate (exit 3), got {code}; err={err}"
    diffs = out.get("diffs", [])
    assert any(
        d["claim_id"] == victim and d["field"] == "pa_effective" for d in diffs
    ), f"expected a pa_effective diff on {victim}, got {diffs}"


# --- AC3: spot values on the real ledger at INTER_PIN ----------------------------------


def test_backfill_spot_values():
    """Internal-compute grades 0 (array never written); the Fano table grades 2."""
    ev = _evidence_dir()
    _ledger, results, _engine_out = _recompute(ev)
    assert results[HESSIAN_ID]["pa"] == 0, "internal-compute PROOF-hessian grades 0"
    assert results[HESSIAN_ID]["effective_pa"] == 0
    assert results[FANO_ID]["pa"] == 2, "the Fano structure-constant table grades PA 2"
    assert results[FANO_ID]["effective_pa"] == 2
    # a derivation anchor with no landed evidence at this pin grades 0 (sanity: the pin is
    # pre-cycle-9, so no PA-1 referent is expected here — that lands with the cycle-9 PR)
    dist = {}
    for r in results.values():
        dist[r["effective_pa"]] = dist.get(r["effective_pa"], 0) + 1
    assert (
        dist.get(2, 0) == 2
    ), f"exactly the two Fano anchors at PA2 at this pin; dist={dist}"


# --- AC2, complete: the WHOLE ledger (not just the pinned subset the Go gate sees) ------


def test_full_ledger_reconciles_clean():
    """Complete AC2: EVERY target anchor's committed grade (all 148, graded or not) equals
    the recompute — not only the graded+pinned subset the strict Go gate reconciles. This
    closes the gap where a hand-edit raising an UN-pinned 0/0 anchor (which carries no
    40-hex pinned_sha, so it is outside the gate's claim-set) would otherwise slip past.
    Uses the encoder's own plan_writes on the real committed ledger."""
    ev = _evidence_dir()
    enc = _encoder()
    ledger, results, _engine_out = _recompute(ev)
    plan = enc.plan_writes(ledger, results)
    changed = {cid: p for cid, p in plan.items() if p["changed"]}
    assert not changed, f"committed != recompute for: {sorted(changed)}"


def test_ungraded_hand_edit_caught_by_full_plan():
    """A hand edit raising an un-pinned 0/0 anchor to 2 with NO evidence IS caught by the
    full-ledger plan — the complement to test_planted_hand_edit_fails (which covers the
    graded subset through the Go gate)."""
    ev = _evidence_dir()
    enc = _encoder()
    ledger, results, _engine_out = _recompute(ev)
    ungraded = [
        cid for cid, r in results.items() if r["pa"] == 0 and r["effective_pa"] == 0
    ]
    assert ungraded, "need an ungraded target anchor to tamper"
    victim = ungraded[0]
    tampered = copy.deepcopy(ledger)
    for a in tampered["anchors"]:
        if a["id"] == victim:
            a["pa_local"] = 2
            a["pa_effective"] = 2
    plan = enc.plan_writes(tampered, results)
    assert plan[victim][
        "changed"
    ], f"a no-evidence hand edit on {victim} must be caught"


# --- the pin invariant (needs no checkout) ---------------------------------------------


def _inter_pin_from_workflow():
    text = WORKFLOW.read_text(encoding="utf-8")
    m = re.search(r"INTER_PIN:\s*([0-9a-f]{7,40})", text)
    return m.group(1) if m else None


def _latest_backfill_report_sha(report_dir=REPORT_DIR):
    """The inter store sha named in the most recent dated backfill report JSON, or None if
    there is no report or the latest one does not record it (report_dir is injectable so
    the fail-closed mutant can exercise the absent-field path)."""
    reports = sorted(report_dir.glob("backfill-*.json"))
    if not reports:
        return None
    rep = json.loads(reports[-1].read_text(encoding="utf-8"))
    for key in ("evidence_store_sha", "inter_pin", "evidence_pin", "store_sha"):
        if rep.get(key):
            return rep[key]
    return None


def _pin_invariant_ok(pin, report_sha):
    """FAIL-CLOSED (architect seq 2583): the invariant holds only when BOTH the pin and the
    store sha are present AND name the same commit (either may abbreviate the other). A
    missing pin or a missing store sha is a FAILURE, never a pass-by-absence — that was the
    type-B skip-when-input-absent gap. The sole matching rule, so a mutant flips it here.
    """
    if not pin or not report_sha:
        return False
    return pin == report_sha or report_sha.startswith(pin) or pin.startswith(report_sha)


def test_pin_invariant_bites():
    """Mutant 1 (architect seq 2554): the check REJECTS a mismatch, not waves it through."""
    assert (
        _pin_invariant_ok("333134c", "333134ca0b1c2d3e4f5061728394a5b6c7d8e9f0") is True
    )
    assert _pin_invariant_ok("333134c", "333134c") is True
    assert (
        _pin_invariant_ok("333134c", "e2ecce8f00ba12cd34ef5061728394a5b6c7d8e9")
        is False
    )


def test_pin_invariant_fails_closed_on_missing_store_sha(tmp_path):
    """Mutant 2 (architect seq 2583, the type-B guard): a dated report that does NOT record
    evidence_store_sha yields no store sha, and the invariant must be KILLED (fail), not
    skipped. Exercises the real _latest_backfill_report_sha path against such a report.
    """
    (tmp_path / "backfill-2099-01-01.json").write_text(
        json.dumps({"issue": "QBP#692", "ledger_version_after": "9.9.9"})
    )
    assert _latest_backfill_report_sha(tmp_path) is None
    assert _pin_invariant_ok("333134c", None) is False
    assert _pin_invariant_ok("333134c", _latest_backfill_report_sha(tmp_path)) is False
    assert _pin_invariant_ok("", "333134c") is False


@pytest.mark.skipif(not WORKFLOW.exists(), reason="pa-reconcile.yml not present")
def test_inter_pin_matches_latest_backfill_report():
    """INTER_PIN must equal the store sha in the latest dated backfill report (architect
    seq 2554 + 2583): the pin moves atomically with the ledger. FAIL-CLOSED — a report that
    does not record evidence_store_sha is a failure, not a skip. The mutant this kills is a
    pin bump without a re-backfill (or vice versa) — committed != recompute silently."""
    pin = _inter_pin_from_workflow()
    assert (
        pin
    ), "pa-reconcile.yml must declare INTER_PIN once the real-ledger step lands"
    report_sha = _latest_backfill_report_sha()
    assert report_sha, (
        "the latest dated backfill report MUST record evidence_store_sha (fail-closed, "
        "architect seq 2583): a missing store sha is a FAILURE, not a skip — otherwise the "
        "pin invariant is fail-open and a pin/ledger desync passes silently"
    )
    assert _pin_invariant_ok(
        pin, report_sha
    ), f"INTER_PIN {pin} != latest backfill report store sha {report_sha}"
