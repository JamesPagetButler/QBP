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


# The empty-closure manifest: git's empty-blob sha, i.e. `git hash-object --stdin` over
# empty input — the LITERAL manifest of an empty import closure (encoder §seq-2394), not a
# carve-out. A target with no proof file has an empty closure, so this is its correct
# staleness key at the gate boundary (architect seq 2651/2657/2663). Strict 3c is preserved:
# every gate claim's pinned_sha is a real 40-hex. The ledger keeps its empty value.
EMPTY_CLOSURE_MANIFEST = "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"


def _gate_pin(pinned_sha):
    """Map a claim's pinned_sha to its GATE-INPUT value (architect seq 2663), fail-closed:
    an EMPTY pin — None, a missing key, or "" — is the empty-closure manifest; a valid
    40-hex passes through; a NON-EMPTY non-40-hex value (a malformed / short sha) is NEVER
    mapped — it passes through unchanged so the gate rejects it (exit 2). Mapping any
    non-40-hex to the manifest would be the KILLED mutant."""
    s = pinned_sha or ""  # None / missing -> ""
    return EMPTY_CLOSURE_MANIFEST if s == "" else s


def _reconcile_doc(ledger, engine_out, committed):
    """Build the pa-reconcile stdin doc (ruling (c), architect seq 2651/2654/2657/2675;
    owner qbp-implementor). Feed the gate the **FULL claim set** — every target anchor — so
    the INDEPENDENT Go gate reconciles the whole ledger (all 148 at #701; 22 un-pinned sinks
    enter at the empty-closure manifest, all derivation edges fed). `plan_writes`
    (test_full_ledger) is then a SECOND line of defence, not the only check for an un-pinned,
    non-depended-on anchor (architect seq 2675: feeding only the pinned closure left those to
    the writer alone — option (a) for a subset). Un-pinned anchors enter as the encoder's own
    no-assistant claims with their gate pin mapped by _gate_pin; the engine folds EffectivePA
    independently (it keys on grades + edges, not pinned_sha — cth seq 2656), so alpha's edge
    to the un-pinned theory sink PROOF-quat-closure folds its effective to 0 (QBP#702/cycle-9;
    #701 was green by data, not construction)."""
    claims = []
    for c in engine_out["_claims"]:
        cid = c["claim"]
        if cid not in committed:
            # not a gradeable target with a committed grade; a dangling edge to it below
            # surfaces as a reconcile diff (fail-closed), never a silent pass.
            continue
        claims.append({**c, "pinned_sha": _gate_pin(c.get("pinned_sha"))})
    ids = {c["claim"] for c in claims}
    # Feed the FULL edge set — do NOT filter to `ids` (Gemini review, QBP#701). If a target
    # anchor's committed grade is DELETED (dropping it from `committed`, so its claim is
    # skipped above), filtering the edge to it would silently drop the fold and let the
    # source keep a fabricated-high effective. Feeding every edge instead makes that edge
    # DANGLE, and the gate rejects a dangling edge (exit 2) — fail-closed, not silent.
    edges = list(engine_out["_edges"])
    expect = {
        cid: {
            "required_pa": 0,  # reconcile test: the EMIT path (required_pa) is not exercised
            "committed_pa_local": committed[cid]["pa_local"],
            "committed_pa_effective": committed[cid]["pa_effective"],
            "source_ref": f"JamesPagetButler/QBP@{cid}",
            "pinning_consumer": [],
        }
        for cid in ids
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


def test_gate_catches_undepended_handedit():
    """Architect seq 2675: the INDEPENDENT Go gate — not only plan_writes — must catch a
    hand-edit on an un-pinned anchor that NO pinned claim depends on. Because the gate is fed
    the full claim set, raising such an anchor's committed grade to 1/1 diffs against the
    gate's own recompute (0/0, no evidence) => exit 3. Were the gate fed only the pinned
    closure, this anchor would be checked by the writer (plan_writes) alone — option (a) for
    a subset, which (c) rejects."""
    ev = _evidence_dir()
    ledger, results, engine_out = _recompute(ev)
    committed = _committed_grades(ledger)
    dep_targets = {e["to"] for e in engine_out["_edges"]}
    cand = [
        cid
        for cid, r in results.items()
        if r["pa"] == 0 and r["effective_pa"] == 0 and cid not in dep_targets
    ]
    assert cand, "need an un-pinned, non-depended-on anchor to tamper"
    victim = cand[0]
    tampered = copy.deepcopy(committed)
    tampered[victim] = {"pa_local": 1, "pa_effective": 1}
    code, out, err = _run_reconcile(_reconcile_doc(ledger, engine_out, tampered))
    assert (
        code == 3
    ), f"the gate must catch an un-depended-on hand edit (exit 3); got {code}; err={err}"
    assert any(
        d["claim_id"] == victim for d in out.get("diffs", [])
    ), f"expected a diff on {victim}; got {out.get('diffs')}"


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


# --- (c) un-pinned-sink folding: synthetic, so it holds by construction, not by data -----
# (QBP#702 cycle-9 ruling, architect seq 2651/2654/2657/2663.) A pinned claim P grades
# local 1; a derivation edge P->U into an un-pinned PA-0 sink U must fold P's effective to 0.

_CLEAN_HASH = "sha256:" + "1" * 64


def _syn_clean_claim(cid, pin):
    """A claim that grades PA1 — one clean lean4 assistant (source_sha == pin, kernel_clean,
    declared == derived, trust pass), modelled on tools/cth-pa/testdata/pa/01_lean_clean.
    Only engine pa.Claim/pa.Assistant fields (the gate decoder is DisallowUnknownFields).
    """
    return {
        "claim": cid,
        "consumer": "qbp#692-ci",
        "pinned_sha": pin,
        "proof_assistants": [
            {
                "assistant": "lean4",
                "evidence_ref": f"proofs/QBP/Syn/{cid}.lean@{pin[:7]}#t",
                "producer": "syn",
                "source_sha": pin,
                "trust_check": "pass",
                "declared": {
                    "mode": "decide",
                    "axioms": ["propext"],
                    "exit_code": 0,
                    "output_hash": _CLEAN_HASH,
                },
                "derived": {
                    "tactics_used": ["decide"],
                    "axioms": ["propext"],
                    "exit_code": 0,
                    "output_hash": _CLEAN_HASH,
                    "kernel_clean": True,
                },
            }
        ],
        "correspondence": {
            "corresponds": False,
            "basis": "",
            "checked_by": "",
            "checked_at": "",
        },
        "corroborated_by": [],
    }


def _syn_sink_claim(cid):
    """A no-assistant PA-0 sink with the empty-closure manifest pin (the un-pinned sink as
    the gate sees it under ruling (c))."""
    return {
        "claim": cid,
        "consumer": "qbp#692-ci",
        "pinned_sha": EMPTY_CLOSURE_MANIFEST,
        "proof_assistants": [],
        "correspondence": {
            "corresponds": False,
            "basis": "",
            "checked_by": "",
            "checked_at": "",
        },
        "corroborated_by": [],
    }


def _expect_term(cid, local, eff):
    return {
        "required_pa": 0,
        "committed_pa_local": local,
        "committed_pa_effective": eff,
        "source_ref": f"JamesPagetButler/QBP@{cid}",
        "pinning_consumer": [],
    }


def _syn_doc(claims, edges, expect):
    return {
        "policy": {"require_signature": False},
        "ledger_version": "syn",
        "emitted_at": "2026-01-01T00:00:00Z",
        "claims": claims,
        "edges": edges,
        "expect": expect,
    }


def test_edge_into_unpinned_sink_folds():
    """(c), the real gate: P (local 1) with a derivation edge into an un-pinned PA-0 sink U
    folds to effective 0 and reconciles CLEAN against committed 1/0. U enters with the
    empty-closure manifest, so 3c stays strict."""
    doc = _syn_doc(
        [_syn_clean_claim("SYN-P", "1" * 40), _syn_sink_claim("SYN-U")],
        [{"from": "SYN-P", "to": "SYN-U", "type": "derivation"}],
        {"SYN-P": _expect_term("SYN-P", 1, 0), "SYN-U": _expect_term("SYN-U", 0, 0)},
    )
    code, out, err = _run_reconcile(doc)
    assert (
        code == 0
    ), f"clean fold expected exit 0; got {code}; diffs={out.get('diffs')}; err={err}"
    assert out.get("diffs") == [], f"unexpected diffs: {out.get('diffs')}"


def test_mutant_drop_sink_edge_killed():
    """Mutant KILLED (herschel seq 2654): drop the edge into the un-pinned sink and the gate
    recomputes P effective = its local 1 != committed 0 => exit 3. The edge is load-bearing.
    """
    doc = _syn_doc(
        [_syn_clean_claim("SYN-P", "1" * 40), _syn_sink_claim("SYN-U")],
        [],  # the sink edge DROPPED — the mutation
        {"SYN-P": _expect_term("SYN-P", 1, 0), "SYN-U": _expect_term("SYN-U", 0, 0)},
    )
    code, out, err = _run_reconcile(doc)
    assert (
        code == 3
    ), f"a dropped sink edge must fail the gate (exit 3); got {code}; err={err}"
    assert any(
        d["claim_id"] == "SYN-P" and d["field"] == "pa_effective"
        for d in out.get("diffs", [])
    ), f"expected a pa_effective diff on SYN-P; got {out.get('diffs')}"


def test_mutant_omit_sink_claim_killed():
    """Mutant KILLED: omit the sink claim but keep the edge => a dangling edge => gate exit 2.
    The sink claim is load-bearing (an empty-pinned claim can't be dropped to "" either — 3c).
    """
    doc = _syn_doc(
        [_syn_clean_claim("SYN-P", "1" * 40)],  # SYN-U omitted — the mutation
        [{"from": "SYN-P", "to": "SYN-U", "type": "derivation"}],
        {"SYN-P": _expect_term("SYN-P", 1, 0)},
    )
    code, _out, err = _run_reconcile(doc)
    assert (
        code == 2
    ), f"a dangling edge (omitted sink) must be gate exit 2; got {code}; err={err}"


def test_reconcile_doc_feeds_dangling_edge_for_deleted_sink():
    """Gemini review (QBP#701), the sink-evasion hole: if a sink's committed grade is DELETED
    (dropping it from `committed`), _reconcile_doc skips its claim — but it must still FEED
    the edge into it, so the gate sees a DANGLING edge and fails closed (exit 2), rather than
    silently dropping the fold and letting the source keep a fabricated-high effective.
    Exercises _reconcile_doc's edge handling directly (the fix is `edges = all`, not filtered
    to `ids`)."""
    P = _syn_clean_claim("SYN-P", "1" * 40)
    edge = {"from": "SYN-P", "to": "SYN-U", "type": "derivation"}
    engine_out = {"_claims": [P], "_edges": [edge]}
    committed = {"SYN-P": {"pa_local": 1, "pa_effective": 0}}  # SYN-U deleted / absent
    doc = _reconcile_doc({}, engine_out, committed)
    assert (
        edge in doc["edges"]
    ), "the edge into the deleted sink must still be fed (dangling), not filtered out"
    code, _out, err = _run_reconcile(doc)
    assert (
        code == 2
    ), f"a dangling edge to a deleted sink must be gate exit 2; got {code}; err={err}"


def test_gate_pin_maps_empty_not_malformed():
    """_gate_pin (architect seq 2663), fail-closed: None / missing / "" all map to the
    empty-closure manifest; a valid 40-hex passes; a NON-EMPTY non-40-hex (malformed short
    sha) is NEVER mapped — the KILLED mutant is "map any non-40-hex to e69de29b"."""
    assert _gate_pin(None) == EMPTY_CLOSURE_MANIFEST
    assert _gate_pin("") == EMPTY_CLOSURE_MANIFEST
    assert _gate_pin("1" * 40) == "1" * 40
    assert _gate_pin("abc123") == "abc123"  # malformed, non-empty -> never mapped
    assert _gate_pin("deadbeef") == "deadbeef"


# --- the pin invariant (needs no checkout) ---------------------------------------------


def _inter_pin_from_workflow():
    text = WORKFLOW.read_text(encoding="utf-8")
    m = re.search(r"INTER_PIN:\s*([0-9a-f]{7,40})", text)
    return m.group(1) if m else None


def _latest_backfill_report(report_dir=REPORT_DIR):
    """The most-recently-GENERATED backfill report, chosen by its `generated` timestamp —
    NOT a lexical filename sort. A report named non-chronologically (e.g. a `-rekey` suffix
    or an un-zero-padded date) must not silently select an older report and make the pin
    invariant compare a stale store sha. ISO `generated` strings sort chronologically; the
    filename is the tiebreak / fallback when `generated` is absent or unparseable."""
    reports = list(report_dir.glob("backfill-*.json"))
    if not reports:
        return None

    def _key(p):
        try:
            gen = json.loads(p.read_text(encoding="utf-8")).get("generated", "")
        except Exception:  # noqa: BLE001 — a malformed report never wins the max
            gen = ""
        return (gen or "", p.name)

    return max(reports, key=_key)


def _latest_backfill_report_sha(report_dir=REPORT_DIR):
    """The inter store sha named in the most-recently-generated backfill report, or None if
    there is no report or the latest one does not record it (report_dir is injectable so
    the fail-closed mutant can exercise the absent-field path)."""
    rep_path = _latest_backfill_report(report_dir)
    if rep_path is None:
        return None
    rep = json.loads(rep_path.read_text(encoding="utf-8"))
    for key in ("evidence_store_sha", "inter_pin", "evidence_pin", "store_sha"):
        if rep.get(key):
            return rep[key]
    return None


def test_latest_report_picked_by_generated_not_filename(tmp_path):
    """Guards the sorted()[-1] fragility (the Gemini-review question, self-addressed while
    the Gemini leg is billing-blocked): the latest report is the most-recently-GENERATED
    one, so a filename that sorts LAST lexically but is OLDER cannot win and feed the pin
    invariant a stale store sha."""
    (tmp_path / "backfill-zzz-old.json").write_text(  # sorts last lexically, but older
        json.dumps(
            {"generated": "2026-01-01T00:00:00Z", "evidence_store_sha": "0" * 40}
        )
    )
    (tmp_path / "backfill-2026-10-10.json").write_text(  # sorts earlier, but newer
        json.dumps(
            {"generated": "2026-10-10T00:00:00Z", "evidence_store_sha": "a" * 40}
        )
    )
    assert _latest_backfill_report_sha(tmp_path) == "a" * 40


def _pin_invariant_ok(pin, report_sha):
    """FAIL-CLOSED (architect seq 2583; hardened per Gemini review, QBP#701): the invariant
    holds only when BOTH the pin and the store sha are **full 40-hex** AND exactly equal. A
    missing/empty value is a FAILURE (the type-B skip-when-input-absent gap), and so is a
    non-40-hex value — NO prefix match, so a short-sha report plus a crafted 40-hex pin that
    merely SHARES a prefix cannot collide. INTER_PIN is full-40-hex in the workflow and
    evidence_store_sha is full-40-hex from `git rev-parse`, so strict equality is exactly
    right. The sole matching rule, so a mutant flips it here."""
    if not (pin and report_sha and HEX40.match(pin) and HEX40.match(report_sha)):
        return False
    return pin == report_sha


_PIN_A = "333134cb61eb12a405c67203859f090f64750df1"
_PIN_B = "e2ecce84f00ba12cd34ef5061728394a5b6c7d8e9"


def test_pin_invariant_bites():
    """Mutant 1 (architect seq 2554): the check REJECTS a mismatch, not waves it through."""
    assert _pin_invariant_ok(_PIN_A, _PIN_A) is True
    assert _pin_invariant_ok(_PIN_A, _PIN_B) is False


def test_pin_invariant_rejects_prefix_match():
    """Mutant 3 (Gemini review): a short-sha report + a crafted full-40-hex pin that merely
    shares the short prefix must NOT match — the symmetric-startswith hazard is closed. Only
    full-40-hex exact equality passes; any non-40-hex (abbreviation) on either side fails.
    """
    short = "333134c"
    assert _pin_invariant_ok(_PIN_A, short) is False  # report abbreviated -> reject
    assert _pin_invariant_ok(short, _PIN_A) is False  # pin abbreviated -> reject
    assert _pin_invariant_ok(short, short) is False  # both abbreviated -> reject
    # a full pin sharing the short prefix must not be accepted against the abbreviation
    assert (
        _pin_invariant_ok(_PIN_A, "333134cffffffffffffffffffffffffffffffffff") is False
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
