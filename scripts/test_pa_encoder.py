#!/usr/bin/env python3
"""Tests for scripts/encode_pa_from_evidence.py + scripts/render_pa_badge.py (QBP#692).

Run: python3 -m pytest scripts/test_pa_encoder.py -v   (needs go, git, pyyaml, jsonschema)

Each test names the AC / ruling it pins:
  AC1  no grade can be passed in; prose records are never parsed for grades
  AC2  a second run with the same evidence cannot raise a grade; a hand edit is reverted
  3c   pinned_sha is never empty when grading evidence (refusal)
  3d   internal-compute anchors get grades, never a proof_assistants array
  seq 2299  pinned_sha = claim-source manifest hash (file-sensitive, commit-insensitive,
            every member of S counts)
  AC4  derivation edges lower effective PA (and only derivation edges, in the engine)
  AC5  badge golden (mutant: rendering an assistant count in place of pa_effective)
  seq 2342  evidence_ref grammar [<owner>/<repo>:]<path>@<commit>#<target>; cross-repo
            refs never enter S (RT C1)
  C2 / seq 2353  target-vs-headline filter: a companion's evidence cannot lift a headline;
            correspondence admits a foreign target only via a structured maps[] pair
  N3   never an empty proof_assistants array; evidence for non-target anchors is reported
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import encode_pa_from_evidence as enc  # noqa: E402
import render_pa_badge as badge  # noqa: E402
from cth_ledger_edit import canonical_dump  # noqa: E402

FIXTURES = ROOT / "tools/cth-pa/testdata/pa"
NON_CLAIM_FIXTURES = {"10_edges.json", "12_expected_pa_wrong.json"}
SIGNING_FIXTURES = {"11a_verified_wrong_role.json", "14_self_attested_signer.json"}

pytestmark = pytest.mark.skipif(
    shutil.which("go") is None or shutil.which("git") is None,
    reason="go + git required",
)


# ---------------------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------------------
def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=str(repo), capture_output=True, text=True, check=True
    ).stdout.strip()


def mk_repo(tmp_path: Path, files: dict) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    git(repo, "init", "-q")
    git(repo, "config", "user.email", "t@e.st")
    git(repo, "config", "user.name", "t")
    commit(repo, files, "c0")
    return repo


def commit(repo: Path, files: dict, msg: str) -> str:
    for rel, text in files.items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
    git(repo, "add", "-A")
    git(repo, "commit", "-q", "-m", msg)
    return git(repo, "rev-parse", "HEAD")


def anchor(aid, kind="proof", proof_file=None, chain=(), lean_theorem=None):
    a = {
        "id": aid,
        "name": aid,
        "tier": 1,
        "status": "coherent",
        "provenance_kind": kind,
        "proof_file": proof_file,
        "prediction_chain": list(chain),
    }
    if lean_theorem is not None:
        a["lean_theorem"] = lean_theorem
    return a


def mk_ledger(tmp_path: Path, anchors: list) -> Path:
    L = {
        "programme": "QBP",
        "version": "6.13.0",
        "anchors": anchors,
        "changelog": [
            {"version": "6.13.0", "date": "2026-09-30T00:00:00Z", "note": "n"}
        ],
        "last_updated": "2026-09-30T00:00:00Z",
    }
    p = tmp_path / "ledger.json"
    p.write_text(canonical_dump(L), encoding="utf-8")
    return p


def fixture(name: str) -> dict:
    return json.loads((FIXTURES / name).read_text(encoding="utf-8"))


def plant(evidence_dir: Path, name: str, doc: dict) -> Path:
    evidence_dir.mkdir(parents=True, exist_ok=True)
    p = evidence_dir / name
    p.write_text(json.dumps(doc, indent=2), encoding="utf-8")
    return p


def evidence_from_fixture(
    fx: str,
    claim: str,
    path: str,
    source_sha: str = "",
    drop_attestation=False,
    theorem: str | None = None,
    maps: list | None = None,
) -> dict:
    """A v2 record shaped exactly like fixture `fx`, re-pointed at `claim` / `path`.
    Oracles (expected_pa, flags, policy, attestation) are left in place unless asked —
    the encoder must drop them itself. `theorem` overrides every assistant's `#target`
    (the fixtures' targets are fictional; the target filter needs them to name the
    anchor's lean_theorem); `maps` is planted into the correspondence block."""
    doc = fixture(fx)
    doc["claim"] = claim
    for a in doc["proof_assistants"]:
        ref = a["evidence_ref"]
        t = theorem or (ref.split("#", 1)[1] if "#" in ref else "thm")
        a["evidence_ref"] = f"{path}@{source_sha or 'deadbeef'}#{t}"
        if source_sha:
            a["source_sha"] = source_sha
        if drop_attestation:
            a.pop("attestation", None)
    if maps is not None:
        doc.setdefault("correspondence", {})["maps"] = maps
    return doc


def run_encoder(ledger: Path, repo: Path, evidence_dir: Path, tmp_path: Path, **kw):
    evidence_dir.mkdir(parents=True, exist_ok=True)
    return enc.run(
        evidence_dir=evidence_dir,
        pinned_master="HEAD",
        ledger_path=ledger,
        repo=repo,
        dry_run=False,
        report_path=tmp_path / "report.md",
        today="2026-10-02T00:00:00Z",
        **kw,
    )


# ---------------------------------------------------------------------------------------
# AC1 — no grade argument; prose never parsed
# ---------------------------------------------------------------------------------------
def test_encoder_has_no_pa_argument():
    ap = enc.build_parser()
    opts = set(ap._option_string_actions)
    forbidden = {
        "--pa",
        "--pa-local",
        "--pa-effective",
        "--grade",
        "--set-pa",
        "--pa_local",
    }
    assert not (opts & forbidden), opts & forbidden
    # nothing in the parser accepts an integer grade at all
    for act in ap._actions:
        assert act.type is not int, act.option_strings
    # and the CLI refuses an injected grade
    with pytest.raises(SystemExit):
        ap.parse_args(["--pa", "2"])


def test_ignores_non_v2_records(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "theorem a : True := trivial\n"})
    ev = tmp_path / "ev"
    ev.mkdir()
    # a prose cycle record (the inter/notary-evidence shape) that even NAMES the anchor,
    # a trust tier and a VERIFIED outcome — none of it may become a grade
    (ev / "cycle-9-prose.yaml").write_text(
        "verification_evidence:\n"
        "  target_claim_node: PROOF-a\n"
        "  verification_outcome: VERIFIED\n"
        "  trust_tiers_achieved: [T0, T1, T2]\n"
        "  proof_assistants:\n"
        "    - assistant: lean4\n"
        "      trust_check: pass\n"
        "correction:\n"
        "  note: none\n",
        encoding="utf-8",
    )
    (ev / "README.md").write_text("not evidence\n", encoding="utf-8")
    ledger = mk_ledger(tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean")])
    out = run_encoder(ledger, repo, ev, tmp_path)
    rep = out["report"]
    assert rep["v2_record_count"] == 0
    assert [Path(i["file"]).name for i in rep["ignored_non_v2"]] == [
        "cycle-9-prose.yaml"
    ]
    L = json.loads(ledger.read_text())
    a = L["anchors"][0]
    assert a["pa_local"] == 0 and a["pa_effective"] == 0
    assert "proof_assistants" not in a
    # key order: the two new keys are appended at the END of the record
    assert list(a)[-2:] == ["pa_local", "pa_effective"]
    assert L["version"] == "6.14.0" and L["changelog"][-1]["version"] == "6.14.0"


def test_is_v2_record_shape():
    assert enc.is_v2_record(fixture("01_lean_clean.json"))
    assert not enc.is_v2_record({"claim": "x"})
    assert not enc.is_v2_record(
        {"claim": "x", "proof_assistants": [{"assistant": "lean4"}]}
    )
    assert not enc.is_v2_record({"verification_evidence": {"target_claim_node": "x"}})
    assert not enc.is_v2_record(["claim"])


def test_unmatched_claim_is_reported_not_graded(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "x\n"})
    ev = tmp_path / "ev"
    plant(
        ev,
        "r.json",
        evidence_from_fixture("01_lean_clean.json", "PROOF-nope", "proofs/A.lean"),
    )
    ledger = mk_ledger(tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean")])
    out = run_encoder(ledger, repo, ev, tmp_path)
    assert out["report"]["unmatched_claim"] == [
        {"file": str(ev / "r.json"), "claim": "PROOF-nope"}
    ]
    assert out["results"]["PROOF-a"]["evidence"] is None


# ---------------------------------------------------------------------------------------
# 3c — pinned_sha never empty when grading evidence
# ---------------------------------------------------------------------------------------
def test_refuses_empty_pinned_sha_with_evidence(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "x\n"})
    ev = tmp_path / "ev"
    # evidence names a path the pinned tree does not have
    plant(
        ev,
        "r.json",
        evidence_from_fixture("01_lean_clean.json", "PROOF-a", "proofs/Missing.lean"),
    )
    ledger = mk_ledger(
        tmp_path,
        [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="lemma_a")],
    )
    with pytest.raises(SystemExit, match="REFUSED.*does not exist at pinned master"):
        run_encoder(ledger, repo, ev, tmp_path)
    assert json.loads(ledger.read_text())["version"] == "6.13.0"  # nothing written

    # evidence names a real path but the anchor's declared proof_file is unresolvable
    shutil.rmtree(ev)
    plant(
        ev,
        "r.json",
        evidence_from_fixture("01_lean_clean.json", "PROOF-b", "proofs/A.lean"),
    )
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-b", proof_file="Hurwitz 1898", lean_theorem="lemma_a")]
    )
    with pytest.raises(SystemExit, match="REFUSED.*pinned_sha must never be empty"):
        run_encoder(ledger, repo, ev, tmp_path)


def test_no_evidence_no_proof_file_is_inert_zero(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "x\n"})
    ledger = mk_ledger(
        tmp_path,
        [
            anchor(
                "PROOF-born", kind="theory-external", proof_file="Hurwitz corollary"
            ),
            anchor("PROOF-fano", kind="theory", proof_file=None),
        ],
    )
    out = run_encoder(ledger, repo, tmp_path / "ev", tmp_path)
    for cid in ("PROOF-born", "PROOF-fano"):
        r = out["results"][cid]
        assert (
            r["pinned_sha"] == ""
            and r["pa"] == 0
            and "no_proof_file" in r["report_flags"]
        )


# ---------------------------------------------------------------------------------------
# 3d — internal-compute: grades yes, array never
# ---------------------------------------------------------------------------------------
def test_internal_compute_never_gets_proof_assistants(tmp_path):
    repo = mk_repo(
        tmp_path,
        {"proofs/Hessian.lean": "native_decide\n", "proofs/A.lean": "decide\n"},
    )
    head = git(repo, "rev-parse", "HEAD")
    hess = anchor(
        "PROOF-hessian",
        kind="internal-compute",
        proof_file="proofs/Hessian.lean",
        lean_theorem="hessian_psd",  # fixture 02's #target
    )
    clean = anchor(
        "PROOF-a", kind="proof", proof_file="proofs/A.lean", lean_theorem="lemma_a"
    )
    ledger = mk_ledger(tmp_path, [hess, clean])
    ev = tmp_path / "ev"
    # fixture 02 is literally the hessian shape (native_decide); give it a matching
    # source_sha so the only thing that can zero it is the engine's kernel rule
    pin_h, _, _ = enc.pinned_sha_for(
        hess, [{"evidence_ref": "proofs/Hessian.lean@x#h"}], repo, head
    )
    plant(
        ev,
        "hess.json",
        evidence_from_fixture(
            "02_lean_native_decide.json", "PROOF-hessian", "proofs/Hessian.lean", pin_h
        ),
    )
    pin_a, _, _ = enc.pinned_sha_for(
        clean, [{"evidence_ref": "proofs/A.lean@x#a"}], repo, head
    )
    plant(
        ev,
        "a.json",
        evidence_from_fixture("01_lean_clean.json", "PROOF-a", "proofs/A.lean", pin_a),
    )
    out = run_encoder(ledger, repo, ev, tmp_path)
    L = json.loads(ledger.read_text())
    by = {a["id"]: a for a in L["anchors"]}
    # hessian: evidence existed, grades written (0 — native_decide is not kernel-clean), NO array
    assert by["PROOF-hessian"]["pa_local"] == 0
    assert by["PROOF-hessian"]["pa_effective"] == 0
    assert "proof_assistants" not in by["PROOF-hessian"]
    assert (
        "array_refused_internal-compute"
        in out["results"]["PROOF-hessian"]["report_flags"]
    )
    assert "lean4:not_kernel_clean" in out["results"]["PROOF-hessian"]["flags"]
    # the proof anchor with the same kind of evidence DOES get the ledger-shape array
    assert by["PROOF-a"]["pa_local"] == 1 and by["PROOF-a"]["pa_effective"] == 1
    arr = by["PROOF-a"]["proof_assistants"]
    assert len(arr) == 1 and set(arr[0]) == {
        "assistant",
        "evidence_ref",
        "trust_check",
        "source_sha",
        "producer",
    }
    assert arr[0]["assistant"] == "lean4" and arr[0]["trust_check"] == "pass"
    assert arr[0]["source_sha"] == pin_a
    # nothing engine-internal leaked into the ledger record
    assert (
        "declared" not in arr[0]
        and "derived" not in arr[0]
        and "attestation" not in arr[0]
    )


# ---------------------------------------------------------------------------------------
# seq 2299 — pinned_sha manifest convention
# ---------------------------------------------------------------------------------------
def test_pinned_sha_follows_file_not_commit(tmp_path):
    repo = mk_repo(
        tmp_path, {"proofs/A.lean": "a0\n", "proofs/B.v": "b0\n", "README.md": "r0\n"}
    )
    a = anchor("PROOF-a", proof_file="proofs/A.lean")
    ev = [{"evidence_ref": "proofs/B.v@zzzz#thm"}]
    c0 = git(repo, "rev-parse", "HEAD")
    p0, s0, f0 = enc.pinned_sha_for(a, ev, repo, c0)
    assert len(p0) == 40 and f0 == []
    assert [s["path"] for s in s0] == ["proofs/A.lean", "proofs/B.v"]  # sorted S
    # unrelated commit: unchanged
    c1 = commit(repo, {"README.md": "r1\n"}, "unrelated")
    assert c1 != c0
    p1, _, _ = enc.pinned_sha_for(a, ev, repo, c1)
    assert p1 == p0
    # editing the proof_file member: changes
    c2 = commit(repo, {"proofs/A.lean": "a1\n"}, "edit A")
    p2, _, _ = enc.pinned_sha_for(a, ev, repo, c2)
    assert p2 != p0
    # editing the evidence_ref member: changes again
    c3 = commit(repo, {"proofs/B.v": "b1\n"}, "edit B")
    p3, _, _ = enc.pinned_sha_for(a, ev, repo, c3)
    assert p3 not in (p0, p2)
    # MUTANT GUARD: a manifest over only one member of S is not the pinned_sha
    only_a, _, _ = enc.pinned_sha_for(a, [], repo, c0)  # S = {A}
    only_b, _, _ = enc.pinned_sha_for(
        anchor("x", proof_file=None), ev, repo, c0
    )  # S = {B}
    assert only_a != p0 and only_b != p0
    # the git value equals an independent Python recomputation of the manifest blob
    lines = [f"{s['path']} {s['blob']}\n" for s in s0]
    assert enc.manifest_hash_py(lines) == p0
    # one rule even for a single-file S: the manifest form, not the bare blob
    blob_a = enc.blob_sha(repo, c0, "proofs/A.lean")
    assert (
        only_a == enc.manifest_hash_py([f"proofs/A.lean {blob_a}\n"])
        and only_a != blob_a
    )


def test_reference_manifest_hash_cd_structure_constant_tables():
    """Reference value from the ruling (live-test seq 2299): PROOF-cd-structure-constant-tables
    at master f452532 with S = {CDAlg.lean, FanoOrientationF3.lean}."""
    commit_sha = "f4525328cc5361ffa04e6e215a03f0ec45181032"
    if (
        subprocess.run(
            ["git", "cat-file", "-e", f"{commit_sha}^{{commit}}"],
            cwd=str(ROOT),
            capture_output=True,
        ).returncode
        != 0
    ):
        pytest.skip("reference commit not in this clone")
    a = anchor(
        "PROOF-cd-structure-constant-tables",
        proof_file="proofs/QBP/Foundations/CDAlg.lean",
    )
    ev = [
        {
            "evidence_ref": "proofs/QBP/Foundations/FanoOrientationF3.lean@x#fanoTableF4_eq_cayleyDickson"
        }
    ]
    pinned, sources, flags = enc.pinned_sha_for(a, ev, ROOT, commit_sha)
    assert flags == []
    assert sources == [
        {
            "path": "proofs/QBP/Foundations/CDAlg.lean",
            "blob": "f9181336cdfefad6e4550b2ddb0ad61db9a8d628",
        },
        {
            "path": "proofs/QBP/Foundations/FanoOrientationF3.lean",
            "blob": "4cd7a94f9b962ce49973d98be269ace7cc5b4387",
        },
    ]
    assert pinned == "be50573493f675d331606c3d752c3c9d15d8ffa4"
    assert pinned == enc.manifest_hash_py(
        [f"{s['path']} {s['blob']}\n" for s in sources]
    )


def test_evidence_ref_path_parse():
    assert enc.evidence_ref_path("proofs/QBP/A.lean@abc#thm") == "proofs/QBP/A.lean"
    assert enc.evidence_ref_path("proofs/QBP/A.lean#thm") == "proofs/QBP/A.lean"
    assert enc.evidence_ref_path("proofs/QBP/A.lean") == "proofs/QBP/A.lean"
    with pytest.raises(SystemExit):
        enc.evidence_ref_path("@abc#thm")
    with pytest.raises(SystemExit):
        enc.evidence_ref_path(None)


# ---------------------------------------------------------------------------------------
# engine parity — fixtures through the encoder's own grading path
# ---------------------------------------------------------------------------------------
def _flag_types(flags):
    return sorted({f.split(":", 1)[1] if ":" in f else f for f in flags})


def test_fixtures_reproduce_expected_pa():
    names = sorted(
        p.name
        for p in FIXTURES.glob("*.json")
        if p.name not in NON_CLAIM_FIXTURES and not p.name.startswith("notary-request")
    )
    stub_equivalent = [n for n in names if n not in SIGNING_FIXTURES]
    assert len(stub_equivalent) >= 27, stub_equivalent
    claims, policies = [], {}
    for n in stub_equivalent:
        fx = fixture(n)
        merged = enc.merge_claim_records(fx["claim"], [(FIXTURES / n, fx)])
        claims.append(
            (
                n,
                fx,
                enc.build_claim(
                    fx["claim"],
                    fx.get("pinned_sha", ""),
                    merged["assistants"],
                    merged["correspondence"],
                    merged["corroborated_by"],
                ),
            )
        )
        policies[n] = fx.get("policy", enc.POLICY)
    # one engine call per policy (11c flips require_signature) — the same run_engine the
    # backfill uses; claim ids in the fixtures are unique per file
    checked = 0
    for pol in ({"require_signature": False}, {"require_signature": True}):
        batch = [(n, fx, c) for n, fx, c in claims if policies[n] == pol]
        if not batch:
            continue
        out = enc.run_engine([c for _, _, c in batch], [], policy=pol)
        got = {c["claim_id"]: c for c in out["claims"]}
        for n, fx, c in batch:
            g = got[c["claim"]]
            assert g["pa"] == fx["expected_pa"], (n, g["flags"])
            assert g["effective_pa"] == g["pa"], n
            assert _flag_types(g["flags"]) == _flag_types(fx.get("flags", [])), (
                n,
                g["flags"],
            )
            checked += 1
    assert checked == len(stub_equivalent)


def test_fixture_12_true_grade_not_planted_expected_pa():
    fx = fixture("12_expected_pa_wrong.json")
    merged = enc.merge_claim_records(fx["claim"], [(FIXTURES / "12", fx)])
    out = enc.run_engine(
        [
            enc.build_claim(
                fx["claim"],
                "",
                merged["assistants"],
                merged["correspondence"],
                merged["corroborated_by"],
            )
        ],
        [],
    )
    assert out["claims"][0]["pa"] == fx["true_pa_do_not_read"] != fx["expected_pa"]


def test_engine_assistant_projection_drops_oracles_keeps_values():
    a = fixture("15_stale_source.json")["proof_assistants"][1]
    e = enc.engine_assistant(a)
    assert set(e) <= set(enc.ASSISTANT_KEYS) | {"declared", "derived"}
    assert "attestation" not in e
    assert e["source_sha"] == a["source_sha"] and e["trust_check"] == a["trust_check"]
    assert e["derived"]["tactics_used"] == a["derived"]["tactics_used"]
    assert set(e["declared"]) <= set(enc.DECLARED_KEYS) and set(e["derived"]) <= set(
        enc.DERIVED_KEYS
    )
    # a missing field stays missing (fail-closed in the engine), never filled in
    b = dict(a)
    del b["source_sha"]
    assert "source_sha" not in enc.engine_assistant(b)


# ---------------------------------------------------------------------------------------
# AC4 — derivation edges
# ---------------------------------------------------------------------------------------
def test_derivation_edge_lowers_effective(tmp_path):
    repo = mk_repo(
        tmp_path,
        {"proofs/A.lean": "a\n", "proofs/B.lean": "b\n", "proofs/C.lean": "c\n"},
    )
    head = git(repo, "rev-parse", "HEAD")
    # fixture targets: 10a lean `x` + coq `y` (correspondence), 10b `x`, 10c `z`
    A = anchor(
        "PROOF-chain-A",
        proof_file="proofs/A.lean",
        chain=["PROOF-chain-B"],
        lean_theorem="x",
    )
    B = anchor("PROOF-chain-B", proof_file="proofs/B.lean", lean_theorem="x")
    C = anchor("PROOF-chain-C", proof_file="proofs/C.lean", lean_theorem="z")
    ev = tmp_path / "ev"
    for fx, an, maps in (
        ("10a_chain_head_pa2.json", A, [{"target": "y", "lean_theorem": "x"}]),
        ("10b_chain_dep_pa1.json", B, None),
        ("10c_chain_relevance_pa0.json", C, None),
    ):
        pin, _, _ = enc.pinned_sha_for(
            an, [{"evidence_ref": an["proof_file"] + "@x#t"}], repo, head
        )
        plant(
            ev,
            fx,
            evidence_from_fixture(fx, an["id"], an["proof_file"], pin, maps=maps),
        )
    ledger = mk_ledger(tmp_path, [A, B, C])
    out = run_encoder(ledger, repo, ev, tmp_path)
    r = out["results"]
    assert (r["PROOF-chain-A"]["pa"], r["PROOF-chain-A"]["effective_pa"]) == (2, 1)
    assert (r["PROOF-chain-B"]["pa"], r["PROOF-chain-B"]["effective_pa"]) == (1, 1)
    assert (r["PROOF-chain-C"]["pa"], r["PROOF-chain-C"]["effective_pa"]) == (0, 0)
    assert out["report"]["derivation_edges"] == [
        {"from": "PROOF-chain-A", "to": "PROOF-chain-B", "type": "derivation"}
    ]
    # conservative rule: EVERY chain entry is a derivation edge today, so adding C lowers A to 0
    A2 = dict(A, prediction_chain=["PROOF-chain-B", "PROOF-chain-C"])
    (tmp_path / "two").mkdir()
    ledger2 = mk_ledger(tmp_path / "two", [A2, B, C])
    out2 = run_encoder(ledger2, repo, ev, tmp_path / "two")
    assert (
        out2["results"]["PROOF-chain-A"]["pa"],
        out2["results"]["PROOF-chain-A"]["effective_pa"],
    ) == (2, 0)
    # chain entries that are not target anchors (roots, DERIV-*) never become edges
    assert (
        enc.derivation_edges([dict(A, prediction_chain=["AXIOM-1", "DERIV-x"]), B])
        == []
    )


def test_engine_excludes_relevance_edges():
    """The engine's own rule (fixture 10): a relevance edge never lowers effective PA.
    The encoder does not emit relevance edges yet; this pins the engine contract it will
    rely on when the Phase-1 typed chain arrives."""
    claims = []
    for fx in (
        "10a_chain_head_pa2.json",
        "10b_chain_dep_pa1.json",
        "10c_chain_relevance_pa0.json",
    ):
        d = fixture(fx)
        m = enc.merge_claim_records(d["claim"], [(FIXTURES / fx, d)])
        claims.append(
            enc.build_claim(
                d["claim"],
                "",
                m["assistants"],
                m["correspondence"],
                m["corroborated_by"],
            )
        )
    edges = fixture("10_edges.json")["edges"]
    out = enc.run_engine(claims, edges)
    got = {c["claim_id"]: c for c in out["claims"]}
    assert (
        got["PROOF-chain-A"]["effective_pa"]
        == fixture("10_edges.json")["expected_effective_pa"]
        == 1
    )
    edges_all_deriv = [dict(e, type="derivation") for e in edges]
    assert {
        c["claim_id"]: c for c in enc.run_engine(claims, edges_all_deriv)["claims"]
    }["PROOF-chain-A"]["effective_pa"] == 0


# ---------------------------------------------------------------------------------------
# AC2 — no silent rise
# ---------------------------------------------------------------------------------------
def test_no_silent_pa_rise(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n", "proofs/B.lean": "b\n"})
    head = git(repo, "rev-parse", "HEAD")
    A = anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="lemma_a")
    B = anchor("PROOF-b", proof_file="proofs/B.lean")
    ev = tmp_path / "ev"
    pin, _, _ = enc.pinned_sha_for(
        A, [{"evidence_ref": "proofs/A.lean@x#t"}], repo, head
    )
    plant(
        ev,
        "a.json",
        evidence_from_fixture("01_lean_clean.json", "PROOF-a", "proofs/A.lean", pin),
    )
    ledger = mk_ledger(tmp_path, [A, B])
    first = run_encoder(ledger, repo, ev, tmp_path)
    assert first["changed"] and first["version"] == "6.14.0"
    after1 = ledger.read_text()
    grades1 = {
        a["id"]: (a["pa_local"], a["pa_effective"])
        for a in json.loads(after1)["anchors"]
    }
    assert grades1 == {"PROOF-a": (1, 1), "PROOF-b": (0, 0)}
    # second run, same evidence: nothing changes, nothing written, "already applied"
    second = run_encoder(ledger, repo, ev, tmp_path)
    assert second["changed"] is False
    assert ledger.read_text() == after1
    assert all(not p["changed"] for p in second["plan"].values())
    rc = enc.main(
        [
            "--evidence-dir",
            str(ev),
            "--pinned-master",
            "HEAD",
            "--ledger",
            str(ledger),
            "--repo",
            str(repo),
            "--report",
            str(tmp_path / "r2.md"),
        ]
    )
    assert rc == 1
    # a hand-raised grade is reverted to the computed value (and listed as a drop)
    L = json.loads(ledger.read_text())
    for a in L["anchors"]:
        if a["id"] == "PROOF-b":
            a["pa_local"] = 2
            a["pa_effective"] = 2
    ledger.write_text(canonical_dump(L), encoding="utf-8")
    third = run_encoder(ledger, repo, ev, tmp_path)
    assert third["changed"]
    L3 = json.loads(ledger.read_text())
    assert {
        a["id"]: (a["pa_local"], a["pa_effective"]) for a in L3["anchors"]
    } == grades1
    assert {(d["id"], d["field"]) for d in third["report"]["drops"]} == {
        ("PROOF-b", "pa_local"),
        ("PROOF-b", "pa_effective"),
    }
    assert L3["version"] == "6.15.0"
    # withdrawing the evidence removes the array and drops the grade — never silently
    shutil.rmtree(ev)
    fourth = run_encoder(ledger, repo, ev, tmp_path)
    L4 = json.loads(ledger.read_text())
    a = [x for x in L4["anchors"] if x["id"] == "PROOF-a"][0]
    assert a["pa_local"] == 0 and "proof_assistants" not in a
    assert any(d["id"] == "PROOF-a" for d in fourth["report"]["drops"])


def test_two_correspondence_records_refused(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ev = tmp_path / "ev"
    plant(
        ev,
        "one.json",
        evidence_from_fixture("06_valid_pair_fano.json", "PROOF-a", "proofs/A.lean"),
    )
    plant(
        ev,
        "two.json",
        evidence_from_fixture("06_valid_pair_fano.json", "PROOF-a", "proofs/A.lean"),
    )
    ledger = mk_ledger(tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean")])
    with pytest.raises(SystemExit, match="REFUSED.*ambiguous"):
        run_encoder(ledger, repo, ev, tmp_path)


def test_schema_invalid_assistant_entry_refused(tmp_path):
    """An evidence assistant the 0.3.5 $defs/ProofAssistant would reject (P9: unknown
    assistant name) is a refusal at encode time, not a red schema-lint later."""
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ev = tmp_path / "ev"
    plant(
        ev,
        "p9.json",
        evidence_from_fixture("P9_unknown_assistant.json", "PROOF-a", "proofs/A.lean"),
    )
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    with pytest.raises(SystemExit, match="REFUSED.*ProofAssistant"):
        run_encoder(ledger, repo, ev, tmp_path)


# ---------------------------------------------------------------------------------------
# AC5 — badge golden
# ---------------------------------------------------------------------------------------
def test_badge_golden(tmp_path):
    graded = {
        "id": "PROOF-x",
        "provenance_kind": "proof",
        "pa_local": 1,
        "pa_effective": 0,
        "proof_assistants": [
            {"assistant": "lean4", "evidence_ref": "a@b#c", "trust_check": "pass"},
            {"assistant": "coq", "evidence_ref": "d@e#f", "trust_check": "fail"},
        ],
    }
    # golden: 1/0 with two assistant names. The mutant that renders clean_count or
    # len(proof_assistants) (= 2) in place of pa_effective (= 0) — or pa_local (= 1) — fails.
    assert badge.render_badge(graded) == "PA 1/0 [lean4, coq]"
    assert (
        badge.render_badge({"id": "PROOF-hessian", "pa_local": 0, "pa_effective": 0})
        == "PA 0/0 [—]"
    )
    assert badge.render_badge({"id": "PROOF-ungraded"}) == "PA —/— [—]"
    # CLI: --anchor one line; --all a table of graded anchors only
    ledger = mk_ledger(
        tmp_path, [graded, {"id": "PROOF-ungraded", "provenance_kind": "proof"}]
    )
    out = subprocess.run(
        [
            sys.executable,
            str(HERE / "render_pa_badge.py"),
            "--anchor",
            "PROOF-x",
            "--ledger",
            str(ledger),
        ],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    assert out == "PA 1/0 [lean4, coq]\n"
    table = subprocess.run(
        [
            sys.executable,
            str(HERE / "render_pa_badge.py"),
            "--all",
            "--ledger",
            str(ledger),
        ],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    assert (
        table
        == "| anchor | kind | badge |\n|---|---|---|\n| PROOF-x | proof | PA 1/0 [lean4, coq] |\n"
    )
    assert (
        subprocess.run(
            [
                sys.executable,
                str(HERE / "render_pa_badge.py"),
                "--anchor",
                "nope",
                "--ledger",
                str(ledger),
            ],
            capture_output=True,
            text=True,
        ).returncode
        == 2
    )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))


# --- §I4 seam fix (live-test seq 2342): cross-repo evidence_ref grammar -------------


def test_parse_evidence_ref_grammar():
    d = enc.parse_evidence_ref("proofs/QBP/A.lean@abc1234#thm")
    assert d == {
        "repo": None,
        "path": "proofs/QBP/A.lean",
        "commit": "abc1234",
        "target": "thm",
    }
    d = enc.parse_evidence_ref(
        "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#fano_table_cross_prover"
    )
    assert d["repo"] == "JamesPagetButler/notary"
    assert d["path"] == "proofs/FanoTableCrossProver.v"
    assert d["commit"] == "b4c92818"
    assert not enc.evidence_ref_is_local(
        "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#t"
    )
    assert enc.evidence_ref_is_local("proofs/QBP/A.lean@abc1234#t")


def test_cross_repo_ref_without_commit_is_refused():
    with pytest.raises(enc.Refusal):
        enc.parse_evidence_ref(
            "JamesPagetButler/notary:proofs/FanoTableCrossProver.v#t"
        )
    with pytest.raises(enc.Refusal):
        enc.evidence_ref_path(
            "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#t"
        )


def test_cross_repo_ref_never_enters_manifest(tmp_path):
    """Fano shape: Lean (QBP) + Coq (notary). S = {the Lean file} only; the mutant
    'treat a prefixed ref as a QBP path' would refuse (file missing) or change S."""
    repo = mk_repo(tmp_path, {"proofs/F3.lean": "theorem t : True := trivial\n"})
    head = git(repo, "rev-parse", "HEAD")
    an = anchor("PROOF-x", proof_file="proofs/F3.lean")
    local_only = [{"evidence_ref": "proofs/F3.lean@aaaa#t"}]
    with_coq = local_only + [
        {
            "evidence_ref": "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#t"
        }
    ]
    sha1, src1, flags1 = enc.pinned_sha_for(an, local_only, repo, head)
    sha2, src2, flags2 = enc.pinned_sha_for(an, with_coq, repo, head)
    assert sha1 == sha2
    assert [s["path"] for s in src2] == ["proofs/F3.lean"]
    assert "cross_repo_evidence" in flags2 and "cross_repo_evidence" not in flags1


# ---------------------------------------------------------------------------------------
# RT C2 — target-vs-headline filter (cth seq 2352; architecture seq 2353 FINAL)
# ---------------------------------------------------------------------------------------
HEADLINE = "QBP.Foundations.CDAlg.mulCoeff_three_eq_fano"
COMPANION = "QBP.Foundations.FanoOrientationF3.fanoTableF4_eq_cayleyDickson"
COQ_REF = (
    "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818"
    "#fano_table_cross_prover"
)


def test_names_match_normalisation():
    assert enc.names_match(COMPANION, COMPANION)
    assert enc.names_match("fanoTableF4_eq_cayleyDickson", COMPANION)  # short vs FQ
    assert enc.names_match(COMPANION, "fanoTableF4_eq_cayleyDickson")
    assert not enc.names_match("mulCoeff_three_eq_fano", COMPANION)
    assert not enc.names_match(
        "Other.Ns.fanoTableF4_eq_cayleyDickson", COMPANION
    )  # FQ≠FQ
    assert not enc.names_match(
        "eq_cayleyDickson", COMPANION
    )  # suffix is not a component
    assert not enc.names_match(None, COMPANION) and not enc.names_match("", "")


def fano_record(claim: str, lean_path: str, source_sha: str, maps):
    """Fixture-06 shape re-pointed at the real Fano pair: Lean (QBP) targets the
    companion theorem by SHORT name; Coq (notary, cross-repo) targets its own lemma."""
    doc = fixture("06_valid_pair_fano.json")
    doc["claim"] = claim
    lean, coq = doc["proof_assistants"]
    lean["evidence_ref"] = f"{lean_path}@aaaa111#fanoTableF4_eq_cayleyDickson"
    coq["evidence_ref"] = COQ_REF
    for a in (lean, coq):
        a["source_sha"] = source_sha
    if maps is None:
        doc["correspondence"].pop("maps", None)
    else:
        doc["correspondence"]["maps"] = maps
    return doc


def test_target_filter_unit_rules():
    an = anchor("PROOF-fano-table-equals-cd-products", lean_theorem=COMPANION)
    doc = fano_record(an["id"], "proofs/F3.lean", "s", None)
    merged = enc.merge_claim_records(an["id"], [(Path("r"), doc)])
    corr = merged["correspondence"]
    assert "maps" not in corr  # never handed to the engine
    good = [{"target": "fano_table_cross_prover", "lean_theorem": COMPANION}]
    # (iii) short #target vs FQ lean_theorem counts; Coq counts via the structured pair
    kept, dropped = enc.filter_assistants_by_target(
        an, merged["assistants"], corr, good
    )
    assert [a["assistant"] for a in kept] == ["lean4", "coq"] and dropped == []
    # (ii) bare corresponds:true with NO matching maps entry → Coq dropped
    kept, dropped = enc.filter_assistants_by_target(an, merged["assistants"], corr, [])
    assert [a["assistant"] for a in kept] == ["lean4"]
    assert dropped == ["target_not_headline:coq"]
    # (iv) a maps entry naming a DIFFERENT lean_theorem → dropped
    other = [{"target": "fano_table_cross_prover", "lean_theorem": HEADLINE}]
    kept, dropped = enc.filter_assistants_by_target(
        an, merged["assistants"], corr, other
    )
    assert dropped == ["target_not_headline:coq"]
    # a pair naming the right lean_theorem but another target → dropped
    wrong_t = [{"target": "some_other_lemma", "lean_theorem": COMPANION}]
    _, dropped = enc.filter_assistants_by_target(
        an, merged["assistants"], corr, wrong_t
    )
    assert dropped == ["target_not_headline:coq"]
    # checked_by equal to a producer → the correspondence route is closed
    self_checked = dict(corr, checked_by="deming")
    _, dropped = enc.filter_assistants_by_target(
        an, merged["assistants"], self_checked, good
    )
    assert dropped == ["target_not_headline:coq"]
    # corresponds false / empty checked_by → closed
    for bad in (dict(corr, corresponds=False), dict(corr, checked_by="")):
        _, dropped = enc.filter_assistants_by_target(
            an, merged["assistants"], bad, good
        )
        assert dropped == ["target_not_headline:coq"]
    # misfiled under the headline: NOTHING matches, even with the valid pair → both dropped
    head = anchor("PROOF-cd-structure-constant-tables", lean_theorem=HEADLINE)
    kept, dropped = enc.filter_assistants_by_target(
        head, merged["assistants"], corr, good
    )
    assert kept == [] and dropped == [
        "target_not_headline:lean4",
        "target_not_headline:coq",
    ]
    # an anchor with no lean_theorem admits nothing by route (a)
    bare = anchor("PROOF-hurwitz")
    kept, _ = enc.filter_assistants_by_target(bare, merged["assistants"], corr, good)
    assert kept == []
    # malformed maps are a refusal, not "no pair"
    with pytest.raises(SystemExit, match="REFUSED.*maps"):
        enc.correspondence_maps("x", Path("r"), {"maps": [{"target": "t"}]})
    with pytest.raises(SystemExit, match="REFUSED.*maps"):
        enc.correspondence_maps("x", Path("r"), {"maps": "t->l"})


def test_companion_cannot_lift_headline_end_to_end(tmp_path, monkeypatch):
    """The 3e-refined ruling's item-4 test. One Fano-shaped record (Lean + cross-repo
    Coq, non-producer correspondence with a structured pair):
      filed under the COMPANION anchor → both count → PA 2 (through pa-grade);
      filed under the HEADLINE anchor   → both dropped → 0 assistants → PA 0, no array.
    Mutant: bypass the filter → the misfiled record grades the headline 2 → must fail.
    """
    repo = mk_repo(
        tmp_path, {"proofs/CDAlg.lean": "decide\n", "proofs/F3.lean": "decide\n"}
    )
    head = git(repo, "rev-parse", "HEAD")
    companion = anchor(
        "PROOF-fano-table-equals-cd-products",
        proof_file="proofs/F3.lean",
        lean_theorem=COMPANION,
    )
    headline = anchor(
        "PROOF-cd-structure-constant-tables",
        proof_file="proofs/CDAlg.lean",
        lean_theorem=HEADLINE,
    )
    maps = [{"target": "fano_table_cross_prover", "lean_theorem": COMPANION}]

    # --- correctly filed: S = {F3.lean} (the Coq ref never enters S) → PA 2 ---------------
    pin_c, src_c, fl_c = enc.pinned_sha_for(
        companion,
        [{"evidence_ref": "proofs/F3.lean@x#t"}, {"evidence_ref": COQ_REF}],
        repo,
        head,
    )
    assert [s["path"] for s in src_c] == [
        "proofs/F3.lean"
    ] and "cross_repo_evidence" in fl_c
    ev = tmp_path / "ev-ok"
    plant(ev, "fano.json", fano_record(companion["id"], "proofs/F3.lean", pin_c, maps))
    ledger = mk_ledger(tmp_path, [companion, headline])
    out = run_encoder(ledger, repo, ev, tmp_path)
    r = out["results"][companion["id"]]
    assert (r["pa"], r["effective_pa"]) == (2, 2), r["flags"]
    assert "cross_repo_evidence" in r["report_flags"]
    assert not any(f.startswith("target_not_headline") for f in r["report_flags"])
    L = json.loads(ledger.read_text())
    by = {a["id"]: a for a in L["anchors"]}
    arr = by[companion["id"]]["proof_assistants"]
    assert [a["assistant"] for a in arr] == ["lean4", "coq"]
    assert arr[1]["evidence_ref"] == COQ_REF  # the foreign ref is recorded verbatim
    assert (by[headline["id"]]["pa_local"], by[headline["id"]]["pa_effective"]) == (
        0,
        0,
    )
    assert "proof_assistants" not in by[headline["id"]]

    # --- misfiled under the headline: both dropped → PA 0, NO array ---------------------
    pin_h, src_h, _ = enc.pinned_sha_for(
        headline,
        [{"evidence_ref": "proofs/F3.lean@x#t"}, {"evidence_ref": COQ_REF}],
        repo,
        head,
    )
    assert [s["path"] for s in src_h] == ["proofs/CDAlg.lean", "proofs/F3.lean"]
    ev2 = tmp_path / "ev-misfiled"
    plant(ev2, "fano.json", fano_record(headline["id"], "proofs/F3.lean", pin_h, maps))
    (tmp_path / "two").mkdir()
    ledger2 = mk_ledger(tmp_path / "two", [companion, headline])
    out2 = run_encoder(ledger2, repo, ev2, tmp_path / "two")
    r2 = out2["results"][headline["id"]]
    assert (r2["pa"], r2["effective_pa"]) == (0, 0)
    assert r2["evidence"] is not None and r2["evidence"]["assistants"] == []
    assert sorted(r2["report_flags"]) == sorted(
        [
            "target_not_headline:lean4",
            "target_not_headline:coq",
            "no_admissible_evidence",
        ]
    )
    L2 = json.loads(ledger2.read_text())
    h2 = [a for a in L2["anchors"] if a["id"] == headline["id"]][0]
    assert h2["pa_local"] == 0 and "proof_assistants" not in h2
    rep2 = out2["report"]
    row = [x for x in rep2["anchors"] if x["id"] == headline["id"]][0]
    assert [d["assistant"] for d in row["dropped_assistants"]] == ["lean4", "coq"]
    assert "target_not_headline:coq" in row["flags"]

    # --- MUTANT GUARD: with the filter bypassed the misfiled record grades 2 -------------
    monkeypatch.setattr(
        enc,
        "filter_assistants_by_target",
        lambda anchor, assistants, corr, maps=None: (list(assistants), []),
    )
    (tmp_path / "mut").mkdir()
    ledger3 = mk_ledger(tmp_path / "mut", [companion, headline])
    out3 = run_encoder(ledger3, repo, ev2, tmp_path / "mut")
    assert out3["results"][headline["id"]]["pa"] == 2  # the hole the filter closes
    monkeypatch.undo()
    (tmp_path / "again").mkdir()
    ledger4 = mk_ledger(tmp_path / "again", [companion, headline])
    assert (
        run_encoder(ledger4, repo, ev2, tmp_path / "again")["results"][headline["id"]][
            "pa"
        ]
        == 0
    )


# ---------------------------------------------------------------------------------------
# RT N3 — never `proof_assistants: []`; evidence for non-target anchors is reported
# ---------------------------------------------------------------------------------------
def test_empty_assistants_record_never_writes_empty_array(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ev = tmp_path / "ev"
    plant(ev, "empty.json", {"claim": "PROOF-a", "proof_assistants": []})
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    out = run_encoder(ledger, repo, ev, tmp_path)
    assert out["report"]["v2_record_count"] == 1
    r = out["results"]["PROOF-a"]
    assert r["pa"] == 0 and "no_admissible_evidence" in r["report_flags"]
    a = json.loads(ledger.read_text())["anchors"][0]
    assert a["pa_local"] == 0 and "proof_assistants" not in a
    # and a ledger that CARRIED an empty array has it removed, not rewritten
    L = json.loads(ledger.read_text())
    L["anchors"][0]["proof_assistants"] = []
    ledger.write_text(canonical_dump(L), encoding="utf-8")
    out2 = run_encoder(ledger, repo, ev, tmp_path)
    assert out2["changed"]
    assert "proof_assistants" not in json.loads(ledger.read_text())["anchors"][0]
    # the plan never carries an empty list
    assert all(p["proof_assistants"] != [] for p in out2["plan"].values())


def test_evidence_for_non_target_anchor_is_reported_not_graded(tmp_path):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ev = tmp_path / "ev"
    plant(
        ev,
        "meas.json",
        evidence_from_fixture("01_lean_clean.json", "MEAS-x", "proofs/A.lean"),
    )
    meas = anchor("MEAS-x", kind="measurement", proof_file=None, lean_theorem="lemma_a")
    ledger = mk_ledger(
        tmp_path,
        [meas, anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="z")],
    )
    out = run_encoder(ledger, repo, ev, tmp_path)
    rep = out["report"]
    assert rep["unmatched_claim"] == []
    assert rep["evidence_for_non_target"] == [
        {
            "file": str(ev / "meas.json"),
            "claim": "MEAS-x",
            "provenance_kind": "measurement",
            "assistants": ["lean4"],
        }
    ]
    assert "MEAS-x" not in out["results"]
    m = [a for a in json.loads(ledger.read_text())["anchors"] if a["id"] == "MEAS-x"][0]
    assert "pa_local" not in m and "proof_assistants" not in m
    assert "Evidence for non-target anchors" in (tmp_path / "report.md").read_text()
