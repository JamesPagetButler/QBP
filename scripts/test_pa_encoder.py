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
  seq 2367 / RT C5  the direct match is lean4 + local only (FQ, or a short name in the
            anchor's own proof_file); P-A / P-B / P-D each with a mutant; positive control
            = the real Fano companion shape → 2 through pa-grade
  RT C4  the manifest S is over the CLAIM's same-repo refs, never the filter's survivors
  RT N8 / N9  cross-repo @<commit> is 7-40 hex; the self-prefix JamesPagetButler/QBP: is local
  RT N10  a dry run never writes the committed report
  RT N11  an anchor without lean_theorem admits nothing — one flag `no_lean_theorem`
  N3   never an empty proof_assistants array; evidence for non-target anchors is reported
  RT C7 / seq 2386  the engine counts assistants, not kernels: survivors collapse to one
            per prover kind before grading — [coq, coq] → 1 (mutant → 2); Fano → 2
  RT N18  the dry-run scratch cleanup is REGISTERED with atexit (not just callable)
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
    doc = evidence_from_fixture("P9_unknown_assistant.json", "PROOF-a", "proofs/A.lean")
    # seq 2367: only lean4 direct-matches; the unknown assistant reaches the schema check
    # through a non-producer correspondence pair (its producer is qbp-oppenheimer)
    doc["correspondence"] = {
        "corresponds": True,
        "basis": "probe",
        "checked_by": "qbp-architecture",
        "checked_at": "x",
        "maps": [{"target": "t", "lean_theorem": "t"}],
    }
    plant(ev, "p9.json", doc)
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    with pytest.raises(SystemExit, match="REFUSED.*ProofAssistant"):
        run_encoder(ledger, repo, ev, tmp_path)
    # without the pair the same entry is simply not admissible — dropped, never written
    doc.pop("correspondence")
    plant(ev, "p9.json", doc)
    out = run_encoder(ledger, repo, ev, tmp_path)
    assert "target_not_headline:isabelle" in out["results"]["PROOF-a"]["report_flags"]


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


def test_maps_compared_verbatim_no_short_name_relaxation():
    """RT N14: `maps` is the machine-checked field — `target` and `lean_theorem` are
    compared VERBATIM against the assistant's `#target` and the anchor's `lean_theorem`;
    the `names_match` short-name relaxation does not apply inside maps on either side.
    """
    an = fano_anchor()
    # short lean_theorem in the map vs the anchor's FQ lean_theorem → no pair → dropped
    A, corr, maps = pair(
        FANO_LEAN_FQ,
        COQ_REF,
        maps=[{"target": "fano_table_cross_prover", "lean_theorem": SHORT}],
    )
    assert enc.names_match(SHORT, COMPANION)  # the relaxation WOULD have matched
    assert not enc.maps_pair(maps, "fano_table_cross_prover", COMPANION)
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["lean4"] and dropped == ["target_not_headline:coq"]
    # short map target vs an FQ-named foreign lemma → no pair either
    coq_fq = "JamesPagetButler/notary:proofs/F.v@b4c92818#Ns.fano_table_cross_prover"
    A, corr, maps = pair(FANO_LEAN_FQ, coq_fq, maps=GOOD_MAPS)
    assert not enc.maps_pair(maps, "Ns.fano_table_cross_prover", COMPANION)
    assert enc.filter_assistants_by_target(an, A, corr, maps)[1] == [
        "target_not_headline:coq"
    ]
    # verbatim on both sides → pair
    assert enc.maps_pair(GOOD_MAPS, "fano_table_cross_prover", COMPANION)
    assert not enc.maps_pair(GOOD_MAPS, None, COMPANION)
    assert not enc.maps_pair(None, "fano_table_cross_prover", COMPANION)
    # a short lean_theorem anchor (8 live) pairs only with a short map lean_theorem
    sh = anchor("PROOF-shells", proof_file="proofs/S.lean", lean_theorem="shells")
    A, corr, maps = pair(
        "proofs/S.lean@a#shells",
        COQ_REF,
        maps=[{"target": "fano_table_cross_prover", "lean_theorem": "shells"}],
    )
    assert names(enc.filter_assistants_by_target(sh, A, corr, maps)[0]) == [
        "lean4",
        "coq",
    ]
    A, corr, maps = pair(
        "proofs/S.lean@a#shells",
        COQ_REF,
        maps=[{"target": "fano_table_cross_prover", "lean_theorem": "Any.Ns.shells"}],
    )
    assert names(enc.filter_assistants_by_target(sh, A, corr, maps)[0]) == ["lean4"]


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
    # seq 2367: a SHORT Lean target counts only inside the anchor's own proof_file, so the
    # anchor now declares the file the short `#fanoTableF4_eq_cayleyDickson` ref lives in
    an = anchor(
        "PROOF-fano-table-equals-cd-products",
        proof_file="proofs/F3.lean",
        lean_theorem=COMPANION,
    )
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
    # an anchor with no lean_theorem admits nothing by EITHER route — one anchor-side
    # flag, not a per-assistant blame (RT N11)
    bare = anchor("PROOF-hurwitz")
    kept, dropped = enc.filter_assistants_by_target(
        bare, merged["assistants"], corr, good
    )
    assert kept == [] and dropped == ["no_lean_theorem"]
    assert enc.filter_assistants_by_target(bare, [], corr, good) == ([], [])
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
            "cross_repo_evidence",  # RT C4: S/flags are over the whole record
        ]
    )
    assert r2["pinned_sha"] == pin_h  # the manifest did not shrink with the drops
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


# ---------------------------------------------------------------------------------------
# §I4 round 2 (live-test seq 2367) + RT re-check C5 — the direct match is lean4 + local
# only: FQ equality, or a short name inside the anchor's OWN proof_file. P-A / P-B / P-D
# each with a mutant; positive control = the real Fano companion shape.
# ---------------------------------------------------------------------------------------
FANO_FILE = "proofs/QBP/Foundations/FanoOrientationF3.lean"
FANO_LEAN_FQ = f"{FANO_FILE}@aaaa111#{COMPANION}"
SHORT = "fanoTableF4_eq_cayleyDickson"
COQ_SAME_NAME = (
    "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#" + SHORT
)
GOOD_MAPS = [{"target": "fano_table_cross_prover", "lean_theorem": COMPANION}]


def fano_anchor():
    return anchor(
        "PROOF-fano-table-equals-cd-products",
        proof_file=FANO_FILE,
        lean_theorem=COMPANION,
    )


def pair(lean_ref, other_ref, other="coq", correspondence=True, maps=None):
    """Fixture-06 shape (lean4 + one other prover, non-producer correspondence) with the
    refs replaced; returns the merged (assistants, correspondence, maps) the filter sees.
    """
    doc = fixture("06_valid_pair_fano.json")
    doc["claim"] = "PROOF-fano-table-equals-cd-products"
    lean, oth = doc["proof_assistants"]
    lean["evidence_ref"] = lean_ref
    oth["evidence_ref"] = other_ref
    oth["assistant"] = other
    if not correspondence:
        doc["correspondence"] = {
            "corresponds": False,
            "basis": "",
            "checked_by": "",
            "checked_at": "",
        }
    if maps is None:
        doc["correspondence"].pop("maps", None)
    else:
        doc["correspondence"]["maps"] = maps
    m = enc.merge_claim_records(doc["claim"], [(Path("r"), doc)])
    return m["assistants"], m["correspondence"], m["correspondence_maps"]


def names(kept):
    return [a["assistant"] for a in kept]


def old_fast_path(anchor, a):
    """The commit-7 route (a): names_match for EVERY assistant (prover- and file-blind)."""
    return enc.names_match(enc.assistant_target(a), anchor.get("lean_theorem"))


def no_path_check(anchor, a):
    """Mutant for P-D: lean4 + local, but a short name accepted from any file."""
    return (
        a.get("assistant") == "lean4"
        and enc.evidence_ref_is_local(a["evidence_ref"])
        and enc.names_match(enc.assistant_target(a), anchor.get("lean_theorem"))
    )


def test_direct_target_match_unit():
    an = fano_anchor()

    def lean(ref):
        return {"assistant": "lean4", "evidence_ref": ref}

    assert enc.direct_target_match(an, lean(FANO_LEAN_FQ))  # FQ == lean_theorem
    assert enc.direct_target_match(
        an, lean(f"{FANO_FILE}@a#{SHORT}")
    )  # short, own file
    assert not enc.direct_target_match(an, lean(f"proofs/QBP/Other.lean@a#{SHORT}"))
    assert not enc.direct_target_match(an, lean(f"{FANO_FILE}@a#Other.Ns.{SHORT}"))
    assert not enc.direct_target_match(an, lean(f"{FANO_FILE}@a"))  # no target
    assert not enc.direct_target_match(
        an, {"assistant": "coq", "evidence_ref": FANO_LEAN_FQ}
    )  # not lean4, whatever the name
    assert not enc.direct_target_match(
        an, lean(f"JamesPagetButler/notary:proofs/F.lean@b4c92818#{COMPANION}")
    )  # not local
    assert enc.direct_target_match(
        an, lean(f"JamesPagetButler/QBP:{FANO_LEAN_FQ}")
    )  # RT N9: the self-prefix is local
    assert not enc.direct_target_match(anchor("x"), lean(FANO_LEAN_FQ))  # no headline
    # an anchor without proof_file cannot vouch for a short name
    nofile = anchor("PROOF-fano-table-equals-cd-products", lean_theorem=COMPANION)
    assert not enc.direct_target_match(nofile, lean(f"{FANO_FILE}@a#{SHORT}"))
    assert enc.direct_target_match(nofile, lean(FANO_LEAN_FQ))
    # a SHORT lean_theorem (8 live anchors): only a short target in its own file, never an
    # FQ target from some namespace (the symmetric names_match relaxation is not used here)
    sh = anchor("PROOF-shells", proof_file="proofs/S.lean", lean_theorem="shells")
    assert enc.direct_target_match(sh, lean("proofs/S.lean@a#shells"))
    assert not enc.direct_target_match(sh, lean("proofs/T.lean@a#shells"))
    assert not enc.direct_target_match(sh, lean("proofs/S.lean@a#Any.Ns.shells"))


def test_probe_PA_same_named_coq_lemma_needs_a_maps_entry(monkeypatch):
    """§I4 P-A: Lean FQ local + cross-repo Coq lemma literally named like the Lean theorem;
    corresponds:true, non-producer checked_by, maps: [] → Coq DROPPED."""
    an = fano_anchor()
    A, corr, maps = pair(FANO_LEAN_FQ, COQ_SAME_NAME, maps=[])
    assert corr["corresponds"] is True and corr["checked_by"] == "qbp-architecture"
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["lean4"] and dropped == ["target_not_headline:coq"]
    # declared as a pair it counts — through maps, never through its name
    same_name_map = [{"target": SHORT, "lean_theorem": COMPANION}]
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, same_name_map)
    assert names(kept) == ["lean4", "coq"] and dropped == []
    # MUTANT = the commit-7 fast path → the same-named Coq lemma is kept with maps: []
    monkeypatch.setattr(enc, "direct_target_match", old_fast_path)
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, [])
    assert (
        names(kept) == ["lean4", "coq"] and dropped == []
    )  # the leak the guard closes


def test_probe_PB_same_named_lemma_without_correspondence(monkeypatch):
    """§I4 P-B: the same Coq lemma with NO correspondence → dropped. RT P-B: a LOCAL agda
    ref carrying the FQ Lean name verbatim → dropped without maps (FQ equality is
    Lean-specific too)."""
    an = fano_anchor()
    A, corr, maps = pair(FANO_LEAN_FQ, COQ_SAME_NAME, correspondence=False)
    assert corr["corresponds"] is False and maps == []
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["lean4"] and dropped == ["target_not_headline:coq"]
    agda_fq = f"proofs/X.agda@aaaa111#{COMPANION}"
    A, corr, maps = pair(FANO_LEAN_FQ, agda_fq, other="agda", correspondence=False)
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["lean4"] and dropped == ["target_not_headline:agda"]
    # a maps entry alone (corresponds:false) does not open route (b) either
    kept, dropped = enc.filter_assistants_by_target(
        an, A, corr, [{"target": COMPANION, "lean_theorem": COMPANION}]
    )
    assert names(kept) == ["lean4"] and dropped == ["target_not_headline:agda"]
    # with a valid correspondence + the pair the Agda assistant counts
    A, corr, maps = pair(
        FANO_LEAN_FQ,
        agda_fq,
        other="agda",
        maps=[{"target": COMPANION, "lean_theorem": COMPANION}],
    )
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["lean4", "agda"] and dropped == []
    # MUTANT = the commit-7 fast path → both same-named provers kept with no correspondence
    monkeypatch.setattr(enc, "direct_target_match", old_fast_path)
    A, corr, maps = pair(FANO_LEAN_FQ, agda_fq, other="agda", correspondence=False)
    assert names(enc.filter_assistants_by_target(an, A, corr, maps)[0]) == [
        "lean4",
        "agda",
    ]
    A, corr, maps = pair(FANO_LEAN_FQ, COQ_SAME_NAME, correspondence=False)
    assert names(enc.filter_assistants_by_target(an, A, corr, maps)[0]) == [
        "lean4",
        "coq",
    ]


def test_probe_PD_short_lean_target_only_in_its_own_file(monkeypatch):
    """§I4 P-D: a short Lean target in a DIFFERENT file (proofs/QBP/Other.lean) → dropped;
    the same short name in the anchor's own proof_file → kept."""
    an = fano_anchor()
    other_file = f"proofs/QBP/Other.lean@aaaa111#{SHORT}"
    own_file = f"{FANO_FILE}@aaaa111#{SHORT}"
    A, corr, maps = pair(other_file, COQ_REF, maps=GOOD_MAPS)
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["coq"] and dropped == ["target_not_headline:lean4"]
    A, corr, maps = pair(own_file, COQ_REF, maps=GOOD_MAPS)
    kept, dropped = enc.filter_assistants_by_target(an, A, corr, maps)
    assert names(kept) == ["lean4", "coq"] and dropped == []
    # P-C: FQ in another namespace with the same last component → dropped (unchanged)
    A, corr, maps = pair(
        f"{FANO_FILE}@aaaa111#Other.Ns.{SHORT}", COQ_REF, maps=GOOD_MAPS
    )
    assert enc.filter_assistants_by_target(an, A, corr, maps)[1] == [
        "target_not_headline:lean4"
    ]
    # a cross-repo lean4 ref (another repo's Lean) with the FQ name → not local → dropped
    A, corr, maps = pair(
        f"JamesPagetButler/notary:proofs/Fano.lean@b4c92818#{COMPANION}",
        COQ_REF,
        maps=GOOD_MAPS,
    )
    assert enc.filter_assistants_by_target(an, A, corr, maps)[1] == [
        "target_not_headline:lean4"
    ]
    # ... and a maps entry does NOT rescue it either (RT C6, seq 2372: route (b) is
    # open across kernels only — a Lean→Lean map carries no kernel diversity, same-repo
    # or cross-repo; see test_C6_*)
    A, corr, maps = pair(
        f"JamesPagetButler/notary:proofs/Fano.lean@b4c92818#{COMPANION}",
        COQ_REF,
        maps=GOOD_MAPS + [{"target": COMPANION, "lean_theorem": COMPANION}],
    )
    assert enc.filter_assistants_by_target(an, A, corr, maps)[1] == [
        "target_not_headline:lean4"
    ]
    # MUTANT = drop the path check on short names → the other-file target is kept
    monkeypatch.setattr(enc, "direct_target_match", no_path_check)
    A, corr, maps = pair(other_file, COQ_REF, maps=GOOD_MAPS)
    assert names(enc.filter_assistants_by_target(an, A, corr, maps)[0]) == [
        "lean4",
        "coq",
    ]


def test_positive_control_real_fano_companion_shape_grades_2(tmp_path):
    """Positive control (seq 2367): the real Fano companion shape — local lean4 FQ target
    == lean_theorem (kept WITHOUT maps) + cross-repo Coq `fano_table_cross_prover` with
    its maps entry (kept) → PA 2 end-to-end through pa-grade; the headline stays 0."""
    cd_file = "proofs/QBP/Foundations/CDAlg.lean"
    repo = mk_repo(tmp_path, {FANO_FILE: "decide\n", cd_file: "decide\n"})
    head = git(repo, "rev-parse", "HEAD")
    companion = fano_anchor()
    headline = anchor(
        "PROOF-cd-structure-constant-tables", proof_file=cd_file, lean_theorem=HEADLINE
    )
    pin, src, _ = enc.pinned_sha_for(
        companion,
        [{"evidence_ref": FANO_LEAN_FQ}, {"evidence_ref": COQ_REF}],
        repo,
        head,
    )
    assert [s["path"] for s in src] == [FANO_FILE]

    def record(coq_ref, maps):
        doc = fixture("06_valid_pair_fano.json")
        doc["claim"] = companion["id"]
        lean, coq = doc["proof_assistants"]
        lean["evidence_ref"] = f"{FANO_FILE}@{head}#{COMPANION}"
        coq["evidence_ref"] = coq_ref
        for a in (lean, coq):
            a["source_sha"] = pin
        doc["correspondence"]["maps"] = maps
        return doc

    ev = tmp_path / "ev"
    plant(ev, "fano.json", record(COQ_REF, GOOD_MAPS))
    ledger = mk_ledger(tmp_path, [companion, headline])
    out = run_encoder(ledger, repo, ev, tmp_path)
    r = out["results"][companion["id"]]
    assert (r["pa"], r["effective_pa"]) == (2, 2), r["flags"]
    assert not any(f.startswith("target_not_headline") for f in r["report_flags"])
    by = {a["id"]: a for a in json.loads(ledger.read_text())["anchors"]}
    assert [a["assistant"] for a in by[companion["id"]]["proof_assistants"]] == [
        "lean4",
        "coq",
    ]
    assert (by[headline["id"]]["pa_local"], by[headline["id"]]["pa_effective"]) == (
        0,
        0,
    )
    assert "proof_assistants" not in by[headline["id"]]
    # the same shape with the Coq lemma NAMED like the Lean theorem: still 2 — via its
    # maps entry (P-A positive side), not via the name
    ev2 = tmp_path / "ev2"
    plant(
        ev2,
        "fano.json",
        record(COQ_SAME_NAME, [{"target": SHORT, "lean_theorem": COMPANION}]),
    )
    (tmp_path / "two").mkdir()
    ledger2 = mk_ledger(tmp_path / "two", [companion, headline])
    out2 = run_encoder(ledger2, repo, ev2, tmp_path / "two")
    assert out2["results"][companion["id"]]["pa"] == 2
    # ... and with maps: [] the same record grades 1 (lean4 only; Coq dropped)
    ev3 = tmp_path / "ev3"
    plant(ev3, "fano.json", record(COQ_SAME_NAME, []))
    (tmp_path / "three").mkdir()
    ledger3 = mk_ledger(tmp_path / "three", [companion, headline])
    r3 = run_encoder(ledger3, repo, ev3, tmp_path / "three")["results"][companion["id"]]
    assert r3["pa"] == 1 and "target_not_headline:coq" in r3["report_flags"]
    assert r3["pinned_sha"] == pin  # C4: the drop did not change S


# ---------------------------------------------------------------------------------------
# RT C6 (architecture seq 2372 + cth 2371) — maps rescues across KERNELS only
# ---------------------------------------------------------------------------------------
CROSS_REPO_LEAN = (
    "JamesPagetButler/other:proofs/X.lean@"
    "0123456789abcdef0123456789abcdef01234567#" + SHORT
)


def test_maps_may_rescue_is_kernel_diversity():
    assert enc.headline_kind(fano_anchor()) == "lean4"
    assert not enc.maps_may_rescue("lean4", "lean4")  # Lean→Lean: no kernel diversity
    assert enc.maps_may_rescue("coq", "lean4")
    assert enc.maps_may_rescue("agda", "lean4")
    assert not enc.maps_may_rescue(None, "lean4") and not enc.maps_may_rescue(
        "", "lean4"
    )


def test_C6_lean_target_never_rescued_by_maps_unit():
    """(i) a LOCAL lean4 companion target paired to the headline by maps → dropped;
    (ii) a CROSS-REPO lean4 ref paired by maps → dropped (repo-locality is provenance,
    not maps-eligibility); the Coq assistant in the same record stays map-eligible."""
    headline = anchor(
        "PROOF-cd-structure-constant-tables",
        proof_file="proofs/QBP/Foundations/CDAlg.lean",
        lean_theorem=HEADLINE,
    )
    both_to_headline = [
        {"target": COMPANION, "lean_theorem": HEADLINE},
        {"target": SHORT, "lean_theorem": HEADLINE},
        {"target": "fano_table_cross_prover", "lean_theorem": HEADLINE},
    ]
    # (i) local lean4 FQ companion + cross-repo Coq, both mapped to the headline
    A, corr, maps = pair(FANO_LEAN_FQ, COQ_REF, maps=both_to_headline)
    assert corr["corresponds"] is True and corr["checked_by"] == "qbp-architecture"
    kept, dropped = enc.filter_assistants_by_target(headline, A, corr, maps)
    assert names(kept) == ["coq"] and dropped == ["target_not_headline:lean4"]
    # (ii) cross-repo lean4 (another repo's Lean port) mapped to the headline → dropped
    A, corr, maps = pair(CROSS_REPO_LEAN, COQ_REF, maps=both_to_headline)
    assert not enc.evidence_ref_is_local(CROSS_REPO_LEAN)
    kept, dropped = enc.filter_assistants_by_target(headline, A, corr, maps)
    assert names(kept) == ["coq"] and dropped == ["target_not_headline:lean4"]
    # the same cross-repo ref as a Coq port of the same name IS map-eligible
    A, corr, maps = pair(
        FANO_LEAN_FQ, CROSS_REPO_LEAN.replace(".lean", ".v"), maps=both_to_headline
    )
    kept, dropped = enc.filter_assistants_by_target(headline, A, corr, maps)
    assert names(kept) == ["coq"] and dropped == ["target_not_headline:lean4"]


def test_C6_misfiled_lean_lean_map_cannot_lift_headline_end_to_end(
    tmp_path, monkeypatch
):
    """The C6 reproduction (RT re-check @ 5cbcfd3), end-to-end through pa-grade: a record
    filed under the HEADLINE anchor — local lean4 targeting the COMPANION theorem (a
    different statement) + cross-repo Coq `fano_table_cross_prover`; `corresponds: true`,
    non-producer `checked_by`.
      shape A (the real Fano maps + a Lean→Lean map COMPANION→HEADLINE): both dropped —
        the Lean→Lean map has no kernel diversity, the Coq map pairs the companion, not
        the headline → headline PA 0, no array;
      shape B (the RT's exact repro: BOTH maps → HEADLINE): lean4 dropped regardless of
        its map; the Coq assistant is kernel-diverse and its map names the headline
        verbatim, so it survives on the checker's word → headline PA 1 (one foreign
        Coq assistant), never the 2 the probe produced with zero Lean proof of itself.
    Positive control unchanged: the pair filed under the COMPANION → PA 2. Mutant (`maps`
    rescues lean4) → shape B grades the misfiled headline 2 → must fail."""
    cd_file = "proofs/QBP/Foundations/CDAlg.lean"
    repo = mk_repo(tmp_path, {FANO_FILE: "decide\n", cd_file: "decide\n"})
    head = git(repo, "rev-parse", "HEAD")
    companion = fano_anchor()
    headline = anchor(
        "PROOF-cd-structure-constant-tables", proof_file=cd_file, lean_theorem=HEADLINE
    )

    def record(claim, pin, maps):
        doc = fixture("06_valid_pair_fano.json")
        doc["claim"] = claim
        lean, coq = doc["proof_assistants"]
        lean["evidence_ref"] = f"{FANO_FILE}@{head}#{COMPANION}"
        coq["evidence_ref"] = COQ_REF
        for a in (lean, coq):
            a["source_sha"] = pin
        doc["correspondence"]["maps"] = maps
        return doc

    pin_h, src_h, _ = enc.pinned_sha_for(
        headline,
        [{"evidence_ref": FANO_LEAN_FQ}, {"evidence_ref": COQ_REF}],
        repo,
        head,
    )
    assert [s["path"] for s in src_h] == [cd_file, FANO_FILE]
    lean_lean = {"target": COMPANION, "lean_theorem": HEADLINE}

    # --- shape A: real Fano maps + the Lean→Lean map → both dropped → PA 0, no array ----
    ev_a = tmp_path / "ev-a"
    plant(ev_a, "fano.json", record(headline["id"], pin_h, [lean_lean] + GOOD_MAPS))
    ledger = mk_ledger(tmp_path, [companion, headline])
    out = run_encoder(ledger, repo, ev_a, tmp_path)
    r = out["results"][headline["id"]]
    assert (r["pa"], r["effective_pa"]) == (0, 0), r["flags"]
    assert r["evidence"]["assistants"] == []
    assert sorted(r["report_flags"]) == sorted(
        [
            "target_not_headline:lean4",
            "target_not_headline:coq",
            "no_admissible_evidence",
            "cross_repo_evidence",
        ]
    )
    assert r["pinned_sha"] == pin_h  # C4: S over the whole record
    by = {a["id"]: a for a in json.loads(ledger.read_text())["anchors"]}
    assert (
        by[headline["id"]]["pa_local"] == 0
        and "proof_assistants" not in by[headline["id"]]
    )
    assert by[companion["id"]]["pa_local"] == 0
    row = [x for x in out["report"]["anchors"] if x["id"] == headline["id"]][0]
    assert [d["assistant"] for d in row["dropped_assistants"]] == ["lean4", "coq"]

    # --- shape B: the RT's exact repro (both maps → HEADLINE) → lean4 dropped, PA 1 ----
    ev = tmp_path / "ev-b"
    both_to_headline = [
        lean_lean,
        {"target": "fano_table_cross_prover", "lean_theorem": HEADLINE},
    ]
    plant(ev, "fano.json", record(headline["id"], pin_h, both_to_headline))
    (tmp_path / "b").mkdir()
    ledger_b = mk_ledger(tmp_path / "b", [companion, headline])
    out_b = run_encoder(ledger_b, repo, ev, tmp_path / "b")
    rb = out_b["results"][headline["id"]]
    assert (rb["pa"], rb["effective_pa"]) == (1, 1), rb["flags"]  # was 2 at 5cbcfd3
    assert [a["assistant"] for a in rb["evidence"]["assistants"]] == ["coq"]
    assert sorted(rb["report_flags"]) == [
        "cross_repo_evidence",
        "target_not_headline:lean4",
    ]
    by_b = {a["id"]: a for a in json.loads(ledger_b.read_text())["anchors"]}
    assert [a["assistant"] for a in by_b[headline["id"]]["proof_assistants"]] == ["coq"]
    assert (
        by_b[headline["id"]]["pa_local"] == 1 and by_b[companion["id"]]["pa_local"] == 0
    )

    # --- positive control: the same pair filed under the companion → PA 2 ------------
    pin_c, _, _ = enc.pinned_sha_for(
        companion,
        [{"evidence_ref": FANO_LEAN_FQ}, {"evidence_ref": COQ_REF}],
        repo,
        head,
    )
    ev2 = tmp_path / "ev-ok"
    plant(ev2, "fano.json", record(companion["id"], pin_c, GOOD_MAPS))
    (tmp_path / "ok").mkdir()
    ledger2 = mk_ledger(tmp_path / "ok", [companion, headline])
    out2 = run_encoder(ledger2, repo, ev2, tmp_path / "ok")
    r2 = out2["results"][companion["id"]]
    assert (r2["pa"], r2["effective_pa"]) == (2, 2), r2["flags"]
    assert not any(f.startswith("target_not_headline") for f in r2["report_flags"])
    by2 = {a["id"]: a for a in json.loads(ledger2.read_text())["anchors"]}
    assert [a["assistant"] for a in by2[companion["id"]]["proof_assistants"]] == [
        "lean4",
        "coq",
    ]
    assert by2[headline["id"]]["pa_local"] == 0

    # --- MUTANT: maps may rescue lean4 → shape B grades the misfiled headline 2 --------
    monkeypatch.setattr(enc, "maps_may_rescue", lambda kind, hk: bool(kind))
    (tmp_path / "mut").mkdir()
    ledger3 = mk_ledger(tmp_path / "mut", [companion, headline])
    r3 = run_encoder(ledger3, repo, ev, tmp_path / "mut")["results"][headline["id"]]
    assert r3["pa"] == 2 and "target_not_headline:lean4" not in r3["report_flags"]
    monkeypatch.undo()
    (tmp_path / "again").mkdir()
    ledger4 = mk_ledger(tmp_path / "again", [companion, headline])
    r4 = run_encoder(ledger4, repo, ev, tmp_path / "again")["results"][headline["id"]]
    assert r4["pa"] == 1 and "target_not_headline:lean4" in r4["report_flags"]


# ---------------------------------------------------------------------------------------
# RT N13 — a refusal over an unresolvable same-repo ref names the record and the claim
# ---------------------------------------------------------------------------------------
def test_refusal_names_record_file_and_claim(tmp_path):
    """One record: on-target `#t` in proofs/A.lean + a second (would-be-dropped) assistant
    at `proofs/DoesNotExist.lean`. S covers both (C4), so the run refuses — and the
    message names the evidence record file and the claim id, not only the anchor."""
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    head = git(repo, "rev-parse", "HEAD")
    doc = fixture("01_lean_clean.json")
    doc["claim"] = "PROOF-a"
    a0 = doc["proof_assistants"][0]
    a1 = json.loads(json.dumps(a0))
    a0["evidence_ref"] = "proofs/A.lean@x#t"
    a1["evidence_ref"] = "proofs/DoesNotExist.lean@x#other"
    doc["proof_assistants"] = [a0, a1]
    ev = tmp_path / "ev"
    rec = plant(ev, "companion-ref.json", doc)
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    with pytest.raises(SystemExit) as ei:
        run_encoder(ledger, repo, ev, tmp_path)
    msg = str(ei.value)
    assert msg.startswith(
        "REFUSED: PROOF-a: evidence_ref path 'proofs/DoesNotExist.lean'"
    )
    assert "does not exist at pinned master" in msg
    assert f"claim 'PROOF-a' in record {rec}" in msg
    assert "dropped or kept" in msg
    # the unit function names the record(s) it is given; without them, the claim only
    with pytest.raises(
        SystemExit, match=r"claim 'PROOF-a' in record r1\.json, r2\.json"
    ):
        enc.pinned_sha_for(
            anchor("PROOF-a", proof_file="proofs/A.lean"),
            [{"evidence_ref": "proofs/Nope.lean@x#t"}],
            repo,
            head,
            ["r1.json", "r2.json"],
        )
    with pytest.raises(SystemExit, match=r"\(claim 'PROOF-a'\); pinned_sha"):
        enc.pinned_sha_for(
            anchor("PROOF-a", proof_file="proofs/A.lean"),
            [{"evidence_ref": "proofs/Nope.lean@x#t"}],
            repo,
            head,
        )
    # a missing proof_file while grading names the record too
    with pytest.raises(SystemExit, match=r"declared proof_file .* in record r\.json"):
        enc.pinned_sha_for(
            anchor("PROOF-a", proof_file="proofs/Missing.lean"),
            [{"evidence_ref": "proofs/A.lean@x#t"}],
            repo,
            head,
            ["r.json"],
        )


# ---------------------------------------------------------------------------------------
# RT re-check C4 — S is the CLAIM's same-repo refs (seq 2299), never the survivors
# ---------------------------------------------------------------------------------------
def test_manifest_covers_dropped_same_repo_refs_not_only_survivors(tmp_path):
    """One record, two local lean4 assistants: `#mulCoeff_three_eq_fano` in CDAlg.lean
    (on-target) + `#fanoTableF4_eq_cayleyDickson` in F3.lean (dropped: short name, other
    file). Notary's source_sha is over BOTH files. The survivor must grade 1, not stale.
    """
    repo = mk_repo(tmp_path, {"proofs/CDAlg.lean": "a\n", "proofs/F3.lean": "b\n"})
    head = git(repo, "rev-parse", "HEAD")
    hid = "PROOF-cd-structure-constant-tables"
    headline = anchor(hid, proof_file="proofs/CDAlg.lean", lean_theorem=HEADLINE)
    refs = [
        {"evidence_ref": "proofs/CDAlg.lean@x#mulCoeff_three_eq_fano"},
        {"evidence_ref": "proofs/F3.lean@x#fanoTableF4_eq_cayleyDickson"},
    ]
    pin_both, src_both, _ = enc.pinned_sha_for(headline, refs, repo, head)
    pin_surv, src_surv, _ = enc.pinned_sha_for(headline, refs[:1], repo, head)
    assert [s["path"] for s in src_both] == ["proofs/CDAlg.lean", "proofs/F3.lean"]
    assert [s["path"] for s in src_surv] == ["proofs/CDAlg.lean"]
    assert pin_both != pin_surv
    doc = fixture("01_lean_clean.json")
    doc["claim"] = hid
    a0 = doc["proof_assistants"][0]
    a1 = json.loads(json.dumps(a0))
    a0["evidence_ref"], a1["evidence_ref"] = (
        refs[0]["evidence_ref"],
        refs[1]["evidence_ref"],
    )
    a0["source_sha"] = a1["source_sha"] = (
        pin_both  # as notary computes it: over the record
    )
    doc["proof_assistants"] = [a0, a1]
    ev = tmp_path / "ev"
    plant(ev, "cd.json", doc)
    ledger = mk_ledger(tmp_path, [headline])
    out = run_encoder(ledger, repo, ev, tmp_path)
    r = out["results"][hid]
    assert r["pinned_sha"] == pin_both
    assert [s["path"] for s in r["sources"]] == ["proofs/CDAlg.lean", "proofs/F3.lean"]
    assert r["pa"] == 1, r["flags"]
    assert "target_not_headline:lean4" in r["report_flags"]
    assert not any("stale" in f for f in r["flags"])
    assert [d["evidence_ref"] for d in r["evidence"]["dropped_assistants"]] == [
        refs[1]["evidence_ref"]
    ]
    # MUTANT: manifest over the survivors only → the survivor's source_sha mismatches →
    # the engine flags it stale → PA 0 (the false drop the fix prevents)
    merged = enc.merge_claim_records(hid, [(Path("r"), doc)])
    kept, _ = enc.filter_assistants_by_target(
        headline,
        merged["assistants"],
        merged["correspondence"],
        merged["correspondence_maps"],
    )
    assert len(kept) == 1
    mut = enc.run_engine(
        [enc.build_claim(hid, pin_surv, kept, merged["correspondence"], [])], []
    )["claims"][0]
    assert mut["pa"] == 0 and any("stale" in f for f in mut["flags"]), mut["flags"]


# ---------------------------------------------------------------------------------------
# RT N8 / N9 — cross-repo @<commit> is a hex pin; the self-prefix is local
# ---------------------------------------------------------------------------------------
def test_cross_repo_commit_must_be_a_hex_pin():
    for tok in ("main", "HEAD", "v1.2", "b4c9", "B4C92818"):
        with pytest.raises(SystemExit, match="REFUSED.*not a 7-40 hex"):
            enc.parse_evidence_ref(f"JamesPagetButler/notary:proofs/X.v@{tok}#t")
    assert (
        enc.parse_evidence_ref("JamesPagetButler/notary:proofs/X.v@b4c92818#t")[
            "commit"
        ]
        == "b4c92818"
    )
    assert (
        enc.parse_evidence_ref(f"JamesPagetButler/notary:proofs/X.v@{'a' * 40}#t")[
            "commit"
        ]
        == "a" * 40
    )
    # local refs keep the permissive token (resolved at the pinned master, never at @tok)
    assert enc.parse_evidence_ref("proofs/A.lean@x#t")["commit"] == "x"
    assert enc.parse_evidence_ref("proofs/A.lean@main#t")["commit"] == "main"


def test_self_prefixed_ref_is_local_and_enters_manifest(tmp_path):
    ref = "JamesPagetButler/QBP:proofs/A.lean@x#t"
    d = enc.parse_evidence_ref(ref)
    assert d["repo"] is None and d["path"] == "proofs/A.lean" and d["commit"] == "x"
    assert (
        enc.evidence_ref_is_local(ref) and enc.evidence_ref_path(ref) == "proofs/A.lean"
    )
    # exactly JamesPagetButler/QBP — a fork or another owner's QBP stays foreign
    assert not enc.evidence_ref_is_local(
        "JamesPagetButler/QBP-fork:proofs/A.lean@b4c92818#t"
    )
    assert not enc.evidence_ref_is_local("someone/QBP:proofs/A.lean@b4c92818#t")
    # RT N15: GitHub owner/repo names are case-insensitive — so is the self-prefix
    for lc in (
        "jamespagetbutler/qbp:",
        "JAMESPAGETBUTLER/QBP:",
        "jamesPagetButler/Qbp:",
    ):
        d_lc = enc.parse_evidence_ref(lc + "proofs/A.lean@x#t")
        assert d_lc["repo"] is None and d_lc["path"] == "proofs/A.lean", lc
        assert enc.evidence_ref_is_local(lc + "proofs/A.lean@x#t")
    assert not enc.evidence_ref_is_local(
        "jamespagetbutler/qbp-fork:proofs/A.lean@b4c92818#t"
    )
    repo = mk_repo(tmp_path, {"proofs/F3.lean": "a\n", "proofs/A.lean": "b\n"})
    head = git(repo, "rev-parse", "HEAD")
    an = anchor("PROOF-x", proof_file="proofs/F3.lean")
    p1, s1, f1 = enc.pinned_sha_for(
        an, [{"evidence_ref": "proofs/A.lean@x#t"}], repo, head
    )
    p2, s2, f2 = enc.pinned_sha_for(an, [{"evidence_ref": ref}], repo, head)
    assert p1 == p2 and [s["path"] for s in s2] == ["proofs/A.lean", "proofs/F3.lean"]
    assert "cross_repo_evidence" not in f2
    p3, s3, f3 = enc.pinned_sha_for(
        an, [{"evidence_ref": "jamespagetbutler/qbp:proofs/A.lean@x#t"}], repo, head
    )
    assert p3 == p1 and [s["path"] for s in s3] == ["proofs/A.lean", "proofs/F3.lean"]
    assert "cross_repo_evidence" not in f3  # N15: enters S like the canonical casing


# ---------------------------------------------------------------------------------------
# RT N10 — a dry run never writes the committed report
# ---------------------------------------------------------------------------------------
def test_dry_run_never_writes_the_committed_report(tmp_path, monkeypatch):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    committed = tmp_path / "analysis-692"
    committed.mkdir()
    (committed / "backfill-2026-10-02.md").write_text("RECORD\n")
    monkeypatch.setattr(enc, "REPORT_DIR", committed)
    ev = tmp_path / "ev"
    ev.mkdir()
    kw = dict(
        evidence_dir=ev,
        pinned_master="HEAD",
        ledger_path=ledger,
        repo=repo,
        report_path=None,
        today="2026-10-02T00:00:00Z",
    )
    out = enc.run(dry_run=True, **kw)
    assert out["changed"]  # the dry run still computes (grades would be written)
    assert json.loads(ledger.read_text())["version"] == "6.13.0"  # ledger untouched
    assert [p.name for p in committed.iterdir()] == ["backfill-2026-10-02.md"]
    assert (committed / "backfill-2026-10-02.md").read_text() == "RECORD\n"
    rp = Path(out["report"]["_report_md"])
    assert out["report"]["_report_scratch"] is True
    assert rp.exists() and committed not in rp.parents
    assert (
        rp.name == "backfill-2026-10-02.dry-run.md" and rp.with_suffix(".json").exists()
    )
    # an explicit --report is honoured under --dry-run
    out2 = enc.run(dry_run=True, **dict(kw, report_path=tmp_path / "mine.md"))
    assert out2["report"]["_report_md"] == str(tmp_path / "mine.md")
    assert out2["report"]["_report_scratch"] is False
    assert (committed / "backfill-2026-10-02.md").read_text() == "RECORD\n"
    # a real run with no --report writes the committed record (the AC4 table)
    out3 = enc.run(dry_run=False, **kw)
    assert out3["report"]["_report_scratch"] is False
    assert (committed / "backfill-2026-10-02.md").read_text() != "RECORD\n"
    assert (committed / "backfill-2026-10-02.json").exists()
    # RT N16: the scratch dir is registered for removal at exit; an explicit --report is
    # not. Run the registered cleanup now and check only the scratch one is gone.
    assert rp.parent in enc._DRY_RUN_SCRATCH
    assert (tmp_path / "mine.md").parent not in enc._DRY_RUN_SCRATCH
    gone = enc.cleanup_dry_run_scratch()
    assert rp.parent in gone and not rp.parent.exists() and not rp.exists()
    assert (tmp_path / "mine.md").exists() and enc._DRY_RUN_SCRATCH == []
    assert (committed / "backfill-2026-10-02.md").exists()


def test_dry_run_cli_names_no_scratch_path(tmp_path, monkeypatch, capsys):
    """RT N16 (CLI): without --report the dry-run line names no path (the scratch dir
    is gone at exit); with --report the kept path is printed."""
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    monkeypatch.setattr(enc, "REPORT_DIR", tmp_path / "committed")
    ev = tmp_path / "ev"
    ev.mkdir()
    base = [
        "--evidence-dir",
        str(ev),
        "--pinned-master",
        "HEAD",
        "--ledger",
        str(ledger),
        "--repo",
        str(repo),
        "--dry-run",
    ]
    rc = enc.main(base)
    out = capsys.readouterr().out
    assert rc == 0 and "DRY applied" in out
    assert "not kept" in out and "qbp692-pa-dry-run-" not in out
    scratch = list(enc._DRY_RUN_SCRATCH)
    assert len(scratch) == 1 and scratch[0].exists()
    enc.cleanup_dry_run_scratch()
    assert not scratch[0].exists()
    rc = enc.main(base + ["--report", str(tmp_path / "keep.md")])
    out = capsys.readouterr().out
    assert rc == 0 and f"report: {tmp_path / 'keep.md'} (+ .json)" in out
    assert (tmp_path / "keep.md").exists() and enc._DRY_RUN_SCRATCH == []


# ---------------------------------------------------------------------------------------
# RT N11 — an anchor without lean_theorem admits nothing; one anchor-side flag; counted
# ---------------------------------------------------------------------------------------
def test_no_lean_theorem_anchor_admits_nothing_and_is_counted(tmp_path):
    bare = anchor("PROOF-hurwitz", proof_file="proofs/H.lean")
    A, corr, maps = pair(FANO_LEAN_FQ, COQ_REF, maps=GOOD_MAPS)
    # even a valid correspondence + a maps entry naming the companion cannot open route (b)
    kept, dropped = enc.filter_assistants_by_target(bare, A, corr, maps)
    assert kept == [] and dropped == ["no_lean_theorem"]
    repo = mk_repo(tmp_path, {"proofs/H.lean": "a\n", "proofs/A.lean": "b\n"})
    head = git(repo, "rev-parse", "HEAD")
    pin, _, _ = enc.pinned_sha_for(
        bare, [{"evidence_ref": "proofs/H.lean@x#t"}], repo, head
    )
    ev = tmp_path / "ev"
    plant(
        ev,
        "h.json",
        evidence_from_fixture(
            "01_lean_clean.json", "PROOF-hurwitz", "proofs/H.lean", pin
        ),
    )
    ok = anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")
    ledger = mk_ledger(tmp_path, [bare, ok])
    out = run_encoder(ledger, repo, ev, tmp_path)
    r = out["results"]["PROOF-hurwitz"]
    assert r["pa"] == 0 and r["evidence"]["assistants"] == []
    assert sorted(r["report_flags"]) == ["no_admissible_evidence", "no_lean_theorem"]
    assert not any(f.startswith("target_not_headline") for f in r["report_flags"])
    assert r["pinned_sha"] == pin  # C4: S still covers the record's file
    assert out["report"]["targets_without_lean_theorem"] == {
        "count": 1,
        "ids": ["PROOF-hurwitz"],
    }
    md = (tmp_path / "report.md").read_text()
    assert "without `lean_theorem`" in md and "| 1 |" in md
    h = [
        a
        for a in json.loads(ledger.read_text())["anchors"]
        if a["id"] == "PROOF-hurwitz"
    ][0]
    assert h["pa_local"] == 0 and "proof_assistants" not in h


# ---------------------------------------------------------------------------------------
# RT C7 (architecture ruling live-test seq 2386; Gemini concurs) — the engine's
# GradeClaim counts clean ASSISTANTS, not kernels: collapse survivors to one per kind.
# ---------------------------------------------------------------------------------------
COQ_REF_2 = (
    "JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#"
    "fano_table_cross_prover_alt"
)
TWO_COQ_MAPS = GOOD_MAPS + [
    {"target": "fano_table_cross_prover_alt", "lean_theorem": COMPANION}
]


def test_C7_collapse_unit():
    coq1 = {"assistant": "coq", "evidence_ref": COQ_REF}
    coq2 = {"assistant": "coq", "evidence_ref": COQ_REF_2}
    lean = {"assistant": "lean4", "evidence_ref": FANO_LEAN_FQ}
    agda = {"assistant": "agda", "evidence_ref": "x.agda@a#t"}
    # first of a kind survives, in order; later same-kind entries are flagged
    kept, flags = enc.collapse_to_one_per_kernel([coq1, coq2])
    assert kept == [coq1] and flags == ["same_kernel_duplicate:coq"]
    kept, flags = enc.collapse_to_one_per_kernel([coq1, coq1])  # listed twice
    assert kept == [coq1] and flags == ["same_kernel_duplicate:coq"]
    kept, flags = enc.collapse_to_one_per_kernel([lean, coq1, coq2, lean, agda])
    assert kept == [lean, coq1, agda]
    assert flags == ["same_kernel_duplicate:coq", "same_kernel_duplicate:lean4"]
    # distinct kinds are untouched (the Fano pair)
    assert enc.collapse_to_one_per_kernel([lean, coq1]) == ([lean, coq1], [])
    assert enc.collapse_to_one_per_kernel([]) == ([], [])


def _coq_only_record(claim, pin, refs, maps):
    """Fixture-06 shape with the lean4 entry REMOVED and one Coq entry per ref (the
    same Coq entry listed twice when refs repeat); maps planted; source_sha = pin."""
    doc = fixture("06_valid_pair_fano.json")
    doc["claim"] = claim
    _lean, coq = doc["proof_assistants"]
    out = []
    for ref in refs:
        c = json.loads(json.dumps(coq))
        c["evidence_ref"] = ref
        c["source_sha"] = pin
        out.append(c)
    doc["proof_assistants"] = out
    doc["correspondence"]["maps"] = maps
    return doc


def test_C7_two_coq_assistants_are_one_kernel_end_to_end(tmp_path, monkeypatch):
    """[coq, coq] (two distinct Coq lemmas, each with its own maps entry, no lean4)
    → PA 1 with flag `same_kernel_duplicate:coq`, array carries ONE coq entry; the same
    Coq assistant listed twice → PA 1; mutant (collapse removed) → the engine grades 2
    from a single kernel; positive control: Fano lean4 + coq → 2 unchanged."""
    cd_file = "proofs/QBP/Foundations/CDAlg.lean"
    repo = mk_repo(tmp_path, {FANO_FILE: "decide\n", cd_file: "decide\n"})
    head = git(repo, "rev-parse", "HEAD")
    companion = fano_anchor()
    pin, _, _ = enc.pinned_sha_for(
        companion, [{"evidence_ref": COQ_REF}, {"evidence_ref": COQ_REF_2}], repo, head
    )

    def grade(sub, refs, maps):
        ev = tmp_path / sub / "ev"
        plant(ev, "fano.json", _coq_only_record(companion["id"], pin, refs, maps))
        ledger = mk_ledger(tmp_path / sub, [companion])
        out = run_encoder(ledger, repo, ev, tmp_path / sub)
        by = {a["id"]: a for a in json.loads(ledger.read_text())["anchors"]}
        return out["results"][companion["id"]], by[companion["id"]], out

    # (1) two distinct Coq lemmas, both admissible via maps, no lean4 → ONE kernel → 1
    (tmp_path / "two").mkdir()
    r, a, out = grade("two", [COQ_REF, COQ_REF_2], TWO_COQ_MAPS)
    assert (r["pa"], r["effective_pa"]) == (1, 1), r["flags"]
    assert r["report_flags"].count("same_kernel_duplicate:coq") == 1
    assert not any(f.startswith("target_not_headline") for f in r["report_flags"])
    assert [x["evidence_ref"] for x in a["proof_assistants"]] == [COQ_REF]  # first
    assert [x["assistant"] for x in r["assistants"]] == ["coq"]  # engine saw one
    assert [
        (d["assistant"], d["evidence_ref"]) for d in r["evidence"]["dropped_assistants"]
    ] == [("coq", COQ_REF_2)]
    md = (tmp_path / "two" / "report.md").read_text()
    assert "same_kernel_duplicate:coq" in md and COQ_REF_2 in md
    assert r["pinned_sha"] == pin  # C4: the collapse did not change S
    # (2) the SAME Coq assistant listed twice → still 1, still flagged
    (tmp_path / "same").mkdir()
    r2, a2, _ = grade("same", [COQ_REF, COQ_REF], GOOD_MAPS)
    assert (r2["pa"], r2["effective_pa"]) == (1, 1), r2["flags"]
    assert "same_kernel_duplicate:coq" in r2["report_flags"]
    assert len(a2["proof_assistants"]) == 1
    # (3) MUTANT — collapse removed: the engine counts the two Coq assistants and grades
    # 2 from one kernel. This is the defect C7 names; with the collapse in place the
    # assertions above hold and this one shows the guard is load-bearing.
    monkeypatch.setattr(enc, "collapse_to_one_per_kernel", lambda kept: (kept, []))
    (tmp_path / "mut").mkdir()
    r3, a3, _ = grade("mut", [COQ_REF, COQ_REF_2], TWO_COQ_MAPS)
    assert r3["pa"] == 2 and len(a3["proof_assistants"]) == 2
    assert "same_kernel_duplicate:coq" not in r3["report_flags"]
    monkeypatch.undo()
    # (4) positive control — the real Fano pair (lean4 + coq, two kinds) → 2 unchanged
    (tmp_path / "pos").mkdir()
    doc = fixture("06_valid_pair_fano.json")
    doc["claim"] = companion["id"]
    lean, coq = doc["proof_assistants"]
    lean["evidence_ref"] = f"{FANO_FILE}@{head}#{COMPANION}"
    coq["evidence_ref"] = COQ_REF
    for x in (lean, coq):
        x["source_sha"] = pin
    doc["correspondence"]["maps"] = GOOD_MAPS
    ev = tmp_path / "pos" / "ev"
    plant(ev, "fano.json", doc)
    ledger = mk_ledger(tmp_path / "pos", [companion])
    r4 = run_encoder(ledger, repo, ev, tmp_path / "pos")["results"][companion["id"]]
    assert (r4["pa"], r4["effective_pa"]) == (2, 2), r4["flags"]
    assert not any(f.startswith("same_kernel_duplicate") for f in r4["report_flags"])
    assert [
        x["assistant"]
        for x in json.loads(ledger.read_text())["anchors"][0]["proof_assistants"]
    ] == ["lean4", "coq"]


# ---------------------------------------------------------------------------------------
# RT N18 — the dry-run scratch cleanup is REGISTERED with atexit, not merely callable
# ---------------------------------------------------------------------------------------
def test_N18_dry_run_registers_atexit_cleanup(tmp_path, monkeypatch):
    repo = mk_repo(tmp_path, {"proofs/A.lean": "a\n"})
    ledger = mk_ledger(
        tmp_path, [anchor("PROOF-a", proof_file="proofs/A.lean", lean_theorem="t")]
    )
    monkeypatch.setattr(enc, "REPORT_DIR", tmp_path / "committed")
    ev = tmp_path / "ev"
    ev.mkdir()
    enc.cleanup_dry_run_scratch()  # start from no scratch (registration is once-only)
    assert enc._DRY_RUN_SCRATCH == []
    registered: list = []
    monkeypatch.setattr(
        enc.atexit, "register", lambda fn, *a, **k: registered.append(fn)
    )
    base = [
        "--evidence-dir",
        str(ev),
        "--pinned-master",
        "HEAD",
        "--ledger",
        str(ledger),
        "--repo",
        str(repo),
        "--dry-run",
    ]
    # --dry-run without --report: the scratch dir exists AND its cleanup is registered
    assert enc.main(base) == 0
    assert registered == [enc.cleanup_dry_run_scratch]
    assert len(enc._DRY_RUN_SCRATCH) == 1 and enc._DRY_RUN_SCRATCH[0].exists()
    # a second scratch dir in the same process registers nothing new (one hook suffices)
    assert enc.main(base) == 0
    assert registered == [enc.cleanup_dry_run_scratch]
    assert len(enc._DRY_RUN_SCRATCH) == 2
    gone = enc.cleanup_dry_run_scratch()
    assert len(gone) == 2 and not any(d.exists() for d in gone)
    # --dry-run WITH --report: nothing registered, no scratch dir
    registered.clear()
    assert enc.main(base + ["--report", str(tmp_path / "keep.md")]) == 0
    assert registered == [] and enc._DRY_RUN_SCRATCH == []
    assert (tmp_path / "keep.md").exists()
