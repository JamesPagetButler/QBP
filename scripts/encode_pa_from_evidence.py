#!/usr/bin/env python3
"""QBP#692 — the ONLY writer of `pa_local` / `pa_effective` / `proof_assistants` on CTH anchors.

PA is COMPUTED, never declared (QBP#692 AC1/AC2; confluent-trust#110 derive-don't-declare).
This encoder has no argument that takes a grade. It reads notary evidence records, shapes
them VERBATIM into the vendored confluent-trust PA engine's own input types, runs ONE
`tools/cth-pa` `pa-grade` invocation, and writes what the engine returns through the
confined ledger writer (`scripts/cth_ledger_edit.py`). A grade that looks wrong is fixed by
new or corrected evidence, never by editing this script's output.

Pipeline
--------
1. EVIDENCE. Every `*.yaml` / `*.json` under --evidence-dir that is in the engine's v2
   record shape (top-level `claim` + `proof_assistants[]`, each assistant carrying
   `declared{}` and `derived{}` — the shape of tools/cth-pa/testdata/pa/01_lean_clean.json)
   is an evidence record for the anchor `claim`. Anything else (the prose cycle YAMLs with
   top-level `verification_evidence` / `correction`) is reported as `ignored_non_v2` and is
   NEVER parsed for grades: the encoder does not synthesise `declared`, `derived`,
   `trust_check`, `evidence_ref` or `source_sha` from prose (architecture ruling 2026-10-02
   item 1; cth-implementor finding 1). Records whose `claim` is not a ledger anchor id are
   reported as `unmatched_claim`. Assistants are projected onto the engine's known fields
   (the fixtures' `attestation`/`expected_pa`/`flags` oracles are test-only and dropped).
2. TARGETS. Anchors with `provenance_kind ∈ {proof, derivation}` ∪ ids starting `PROOF-`
   (147 at ledger 6.13.0, incl. `PROOF-hessian` which is `internal-compute`).
3. pinned_sha (architecture ruling, live-test seq 2299 — FINAL): the claim-source MANIFEST
   hash. S = {anchor proof_file} ∪ {QBP paths named by the claim's v2 evidence_refs
   (format path@sha#theorem)}, deduplicated. For p in sorted(S) the manifest line is
   `f"{p} {git rev-parse <pinned-master>:p}\\n"` (the git BLOB sha1 — never hash-object on
   a working-tree file, which is filter-sensitive); pinned_sha = `git hash-object --stdin`
   over the concatenated lines. The same form is used when S has one file, so there is one
   rule. The engine compares every assistant's `source_sha` to this value (stale ⇒ counts
   0, fail-closed). Refusals: an evidence_ref path that does not exist at the pinned
   commit; a declared proof_file that does not exist at the pinned commit while evidence is
   being graded (pinned_sha must never be empty when grading evidence — architecture 3c).
   No evidence and no resolvable proof_file ⇒ pinned_sha "" (inert: nothing to be stale),
   report flag `no_proof_file`. The convention lives in ONE function (`pinned_sha_for`) so
   it can be swapped; S and the per-file blobs go in the report, not the ledger
   (`pinned_sha` has no ledger home at schema 0.3.5).
4. ENGINE. One `pa.Claim` per target anchor {claim, consumer "qbp#692-ci", pinned_sha,
   proof_assistants, correspondence, corroborated_by}. Edges: every `prediction_chain`
   entry (id → target) whose target is also a target anchor, typed `derivation`. This is
   CONSERVATIVE — a derivation edge can only LOWER effective PA; typed relevance / mention
   edges (which the engine excludes from the min) arrive with the Phase-1 chain migration,
   and until then every chain entry is treated as a derivation. Anchors with no evidence
   enter the same invocation as empty claims (zero assistants ⇒ PA 0 by construction) so
   that edges into them still fold; no evidence is graded for them. Policy
   `require_signature: false` (inter#149 v0 — StubV0, every record unsigned).
5. WRITE (confined). For every target anchor `pa_local` = engine `pa`, `pa_effective` =
   engine `effective_pa` (integers). `proof_assistants` = the ledger-shape array
   [{assistant, evidence_ref, trust_check, source_sha, producer}] ONLY when (a) v2 evidence
   exists for the anchor AND (b) `provenance_kind ∈ {proof, derivation}` — on
   `internal-compute` (PROOF-hessian) the two grades are written and the array NEVER is
   (cth-implementor ruling 2026-10-02 3d, live-test seq 2290). New keys are appended at the
   end of the record (key order is content for the confined writer). A stale array whose
   evidence has been withdrawn is removed. If nothing would change: exit 1 "already
   applied". Version minor-bump, `last_updated` = today UTC, one changelog entry.
6. REPORT. `--report` (default analysis/692-pa-backfill/backfill-<date>.md + .json): the
   AC4 before/after table for all target anchors, the drop list, ignored_non_v2 /
   unmatched_claim, pinned master commit, per-anchor S + blobs + pinned_sha, engine pin.

Usage:
  python3 scripts/encode_pa_from_evidence.py [--evidence-dir DIR] [--pinned-master REV]
                                              [--dry-run] [--report PATH]
There is NO --pa argument. --ledger / --repo exist for tests (paths, never grades).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, OrderedDict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
SCHEMA = ROOT / "docs/cth/inventory.schema.current.json"
ENGINE_DIR = ROOT / "tools/cth-pa"
ENGINE_PIN = "13de2f728707cd4431e0116126c530247f132158"
DEFAULT_EVIDENCE_DIR = Path("/home/prime/Documents/inter/notary-evidence")
REPORT_DIR = ROOT / "analysis/692-pa-backfill"

CONSUMER = "qbp#692-ci"
POLICY = {"require_signature": False}
TARGET_KINDS = ("proof", "derivation")  # kinds that may carry a proof_assistants array
HEX40 = re.compile(r"^[0-9a-f]{40}$")

# The engine's own field names (pa.go JSON tags). Everything else on an evidence
# assistant / record is an oracle or provenance annotation and is not an engine input.
ASSISTANT_KEYS = ("assistant", "evidence_ref", "producer", "trust_check", "source_sha")
DECLARED_KEYS = ("mode", "output_hash", "axioms", "exit_code")
DERIVED_KEYS = ("output_hash", "tactics_used", "axioms", "exit_code", "kernel_clean")
CORRESPONDENCE_KEYS = ("corresponds", "basis", "checked_by", "checked_at")
# The ledger-shape ProofAssistant record (schema 0.3.5 $defs/ProofAssistant): the three
# required pointers plus the two provenance fields the reconcile job needs.
LEDGER_ASSISTANT_KEYS = (
    "assistant",
    "evidence_ref",
    "trust_check",
    "source_sha",
    "producer",
)


class Refusal(SystemExit):
    """A loud stop: the encoder will not grade or write under this condition."""

    def __init__(self, msg: str):
        super().__init__(f"REFUSED: {msg}")


# ---------------------------------------------------------------------------------------
# git helpers
# ---------------------------------------------------------------------------------------
def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args],
        cwd=str(repo),
        capture_output=True,
        text=True,
        check=check,
    )


def resolve_commit(repo: Path, rev: str) -> str:
    """Full 40-hex commit sha for `rev` (e.g. origin/master); refuses if unresolvable."""
    p = _git(repo, "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}", check=False)
    sha = p.stdout.strip()
    if p.returncode != 0 or not HEX40.match(sha):
        raise Refusal(f"--pinned-master {rev!r} does not resolve to a commit in {repo}")
    return sha


def blob_sha(repo: Path, commit: str, path: str) -> Optional[str]:
    """Git BLOB sha1 of `path` at `commit` (`git rev-parse <commit>:<path>`), or None if
    the path does not exist there. Never hash-object on a checkout (filter-sensitive).
    """
    p = _git(repo, "rev-parse", "--verify", "--quiet", f"{commit}:{path}", check=False)
    sha = p.stdout.strip()
    if p.returncode != 0 or not HEX40.match(sha):
        return None
    return sha


def manifest_hash(repo: Path, lines: List[str]) -> str:
    """`git hash-object --stdin` over the concatenated manifest lines (ruling seq 2299)."""
    data = "".join(lines)
    p = subprocess.run(
        ["git", "hash-object", "--stdin"],
        cwd=str(repo),
        input=data,
        capture_output=True,
        text=True,
        check=True,
    )
    sha = p.stdout.strip()
    if not HEX40.match(sha):
        raise Refusal(f"git hash-object returned a non-sha: {sha!r}")
    return sha


def manifest_hash_py(lines: List[str]) -> str:
    """Independent recomputation of the git blob hash (tests cross-check the git call)."""
    data = "".join(lines).encode("utf-8")
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


# ---------------------------------------------------------------------------------------
# evidence
# ---------------------------------------------------------------------------------------
def is_v2_record(doc: Any) -> bool:
    """The engine's v2 claim-record shape: top-level `claim` (str) + `proof_assistants`
    list whose every item is a dict carrying `assistant`, `declared{}` and `derived{}`.
    """
    if not isinstance(doc, dict):
        return False
    if not isinstance(doc.get("claim"), str) or not doc["claim"]:
        return False
    pas = doc.get("proof_assistants")
    if not isinstance(pas, list):
        return False
    for a in pas:
        if not isinstance(a, dict):
            return False
        if not isinstance(a.get("assistant"), str):
            return False
        if not isinstance(a.get("declared"), dict) or not isinstance(
            a.get("derived"), dict
        ):
            return False
    return True


def _load_doc(path: Path) -> Any:
    text = path.read_text(encoding="utf-8")
    if path.suffix == ".json":
        return json.loads(text)
    import yaml  # type: ignore

    return yaml.safe_load(text)


def load_evidence(
    evidence_dir: Path,
) -> Tuple[List[Tuple[Path, Dict[str, Any]]], List[Dict[str, str]]]:
    """(v2 records as (path, doc), ignored_non_v2 as [{file, reason}]). An unparseable
    file is a refusal — the encoder cannot tell whether it was evidence."""
    records: List[Tuple[Path, Dict[str, Any]]] = []
    ignored: List[Dict[str, str]] = []
    if not evidence_dir.is_dir():
        raise Refusal(f"--evidence-dir {evidence_dir} is not a directory")
    for p in sorted(evidence_dir.rglob("*")):
        if not p.is_file() or p.suffix not in (".yaml", ".yml", ".json"):
            continue
        try:
            doc = _load_doc(p)
        except Exception as e:  # noqa: BLE001 — loud, not silent
            raise Refusal(f"evidence record {p} does not parse: {e}")
        if is_v2_record(doc):
            records.append((p, doc))
        else:
            top = (
                sorted(doc.keys())[:6] if isinstance(doc, dict) else type(doc).__name__
            )
            ignored.append(
                {
                    "file": str(p),
                    "reason": f"not the engine v2 record shape (top-level keys: {top})",
                }
            )
    return records, ignored


def group_by_claim(
    records: List[Tuple[Path, Dict[str, Any]]], anchor_ids: set
) -> Tuple[Dict[str, List[Tuple[Path, Dict[str, Any]]]], List[Dict[str, str]]]:
    by_claim: Dict[str, List[Tuple[Path, Dict[str, Any]]]] = OrderedDict()
    unmatched: List[Dict[str, str]] = []
    for p, doc in records:
        cid = doc["claim"]
        if cid not in anchor_ids:
            unmatched.append({"file": str(p), "claim": cid})
            continue
        by_claim.setdefault(cid, []).append((p, doc))
    return by_claim, unmatched


def _project(d: Dict[str, Any], keys: Tuple[str, ...]) -> Dict[str, Any]:
    return OrderedDict((k, d[k]) for k in keys if k in d)


def engine_assistant(a: Dict[str, Any]) -> Dict[str, Any]:
    """Project an evidence assistant onto the engine's Assistant fields, VERBATIM values.
    Missing fields stay missing (the engine fails closed on them); nothing is filled in.
    """
    out = _project(a, ASSISTANT_KEYS)
    out["declared"] = _project(a.get("declared", {}), DECLARED_KEYS)
    out["derived"] = _project(a.get("derived", {}), DERIVED_KEYS)
    return out


def evidence_ref_path(ref: Any) -> str:
    """`path@sha#theorem` → `path`. Refuses an unparseable ref."""
    if not isinstance(ref, str) or not ref:
        raise Refusal(f"evidence_ref is not a non-empty string: {ref!r}")
    path = ref.split("@", 1)[0].split("#", 1)[0]
    if not path:
        raise Refusal(f"evidence_ref names no path: {ref!r}")
    return path


def merge_claim_records(
    cid: str, recs: List[Tuple[Path, Dict[str, Any]]]
) -> Dict[str, Any]:
    """Fold one anchor's v2 records into the engine inputs: assistants concatenated in
    file order; the correspondence block from the single record that asserts one (two
    asserting records are ambiguous ⇒ refuse); corroborated_by unioned."""
    assistants: List[Dict[str, Any]] = []
    corr: Optional[Dict[str, Any]] = None
    corr_src: Optional[Path] = None
    corroborated: List[str] = []
    for p, doc in recs:
        for a in doc["proof_assistants"]:
            assistants.append(engine_assistant(a))
        c = doc.get("correspondence")
        if isinstance(c, dict) and c.get("corresponds") is True:
            if corr is not None:
                raise Refusal(
                    f"{cid}: two evidence records assert a correspondence "
                    f"({corr_src} and {p}); which pair corresponds is ambiguous"
                )
            corr, corr_src = _project(c, CORRESPONDENCE_KEYS), p
        for x in doc.get("corroborated_by") or []:
            if isinstance(x, str) and x not in corroborated:
                corroborated.append(x)
    if corr is None:
        corr = OrderedDict(
            [
                ("corresponds", False),
                ("basis", ""),
                ("checked_by", ""),
                ("checked_at", ""),
            ]
        )
    return {
        "assistants": assistants,
        "correspondence": corr,
        "corroborated_by": corroborated,
        "files": [str(p) for p, _ in recs],
    }


# ---------------------------------------------------------------------------------------
# targets, pinned_sha, edges
# ---------------------------------------------------------------------------------------
def is_target(anchor: Dict[str, Any]) -> bool:
    return anchor.get("provenance_kind") in TARGET_KINDS or str(
        anchor.get("id", "")
    ).startswith("PROOF-")


def target_anchors(ledger: Dict[str, Any]) -> List[Dict[str, Any]]:
    return [a for a in ledger["anchors"] if is_target(a)]


def pinned_sha_for(
    anchor: Dict[str, Any],
    assistants: List[Dict[str, Any]],
    repo: Path,
    commit: str,
) -> Tuple[str, List[Dict[str, str]], List[str]]:
    """THE pinned_sha convention (one place; swap here if the ruling changes).

    Returns (pinned_sha, sources=[{path, blob}], report_flags). See module doc §3."""
    flags: List[str] = []
    has_evidence = bool(assistants)
    proof_file = anchor.get("proof_file")
    paths: Dict[str, str] = (
        OrderedDict()
    )  # path -> origin ("proof_file" | "evidence_ref")
    if isinstance(proof_file, str) and proof_file:
        paths[proof_file] = "proof_file"
    for a in assistants:
        p = evidence_ref_path(a.get("evidence_ref"))
        paths.setdefault(p, "evidence_ref")
    sources: List[Dict[str, str]] = []
    for path in sorted(paths):
        blob = blob_sha(repo, commit, path)
        if blob is None:
            if paths[path] == "evidence_ref":
                raise Refusal(
                    f"{anchor['id']}: evidence_ref path {path!r} does not exist at pinned "
                    f"master {commit[:12]}; pinned_sha cannot be computed for evidence "
                    "that names a file the pinned tree does not have"
                )
            if has_evidence:
                raise Refusal(
                    f"{anchor['id']}: declared proof_file {path!r} does not exist at "
                    f"pinned master {commit[:12]} while evidence is being graded; "
                    "pinned_sha must never be empty when grading evidence"
                )
            flags.append("no_proof_file")
            continue
        sources.append({"path": path, "blob": blob})
    if not sources:
        if not has_evidence and "no_proof_file" not in flags:
            flags.append("no_proof_file")
        return "", sources, flags
    lines = [f"{s['path']} {s['blob']}\n" for s in sources]
    return manifest_hash(repo, lines), sources, flags


def derivation_edges(targets: List[Dict[str, Any]]) -> List[Dict[str, str]]:
    """Every prediction_chain entry (id → target) with target also a target anchor, typed
    `derivation` (conservative; see module doc §4)."""
    ids = {a["id"] for a in targets}
    edges: List[Dict[str, str]] = []
    seen = set()
    for a in targets:
        for t in a.get("prediction_chain") or []:
            if t in ids and t != a["id"] and (a["id"], t) not in seen:
                seen.add((a["id"], t))
                edges.append({"from": a["id"], "to": t, "type": "derivation"})
    return edges


# ---------------------------------------------------------------------------------------
# engine
# ---------------------------------------------------------------------------------------
_BIN: Optional[Path] = None


def pa_grade_binary() -> Path:
    """Build `tools/cth-pa/cmd/pa-grade` once per process (or use $CTH_PA_GRADE_BIN)."""
    global _BIN
    if _BIN is not None:
        return _BIN
    env_bin = os.environ.get("CTH_PA_GRADE_BIN")
    if env_bin:
        _BIN = Path(env_bin)
        return _BIN
    out = Path(tempfile.mkdtemp(prefix="pa-grade-")) / "pa-grade"
    p = subprocess.run(
        ["go", "build", "-o", str(out), "./cmd/pa-grade"],
        cwd=str(ENGINE_DIR),
        capture_output=True,
        text=True,
    )
    if p.returncode != 0:
        raise Refusal(
            f"go build ./cmd/pa-grade failed (exit {p.returncode}):\n{p.stderr}"
        )
    _BIN = out
    return _BIN


def run_engine(
    claims: List[Dict[str, Any]],
    edges: List[Dict[str, str]],
    policy: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """ONE pa-grade invocation over all claims + edges; returns the parsed stdout
    document (engine, verifier, policy, claims[{claim_id, pa, effective_pa, clean_count,
    flags, assistants[]}]). Any non-zero exit is a refusal with the engine's stderr."""
    doc = {"policy": policy or POLICY, "claims": claims, "edges": edges}
    p = subprocess.run(
        [str(pa_grade_binary())],
        input=json.dumps(doc),
        capture_output=True,
        text=True,
    )
    if p.returncode != 0:
        raise Refusal(f"pa-grade exit {p.returncode}: {p.stderr.strip()}")
    out = json.loads(p.stdout)
    if out.get("engine") != f"confluent-trust/internal/pa@{ENGINE_PIN}":
        raise Refusal(f"engine pin mismatch: {out.get('engine')!r} != {ENGINE_PIN}")
    return out


def build_claim(
    anchor_id: str,
    pinned_sha: str,
    assistants: List[Dict[str, Any]],
    correspondence: Dict[str, Any],
    corroborated_by: List[str],
) -> Dict[str, Any]:
    return OrderedDict(
        [
            ("claim", anchor_id),
            ("consumer", CONSUMER),
            ("pinned_sha", pinned_sha),
            ("proof_assistants", assistants),
            ("correspondence", correspondence),
            ("corroborated_by", corroborated_by),
        ]
    )


def grade_ledger(
    ledger: Dict[str, Any],
    by_claim: Dict[str, List[Tuple[Path, Dict[str, Any]]]],
    repo: Path,
    commit: str,
) -> Tuple[Dict[str, Dict[str, Any]], Dict[str, Any]]:
    """Grade every target anchor. Returns ({id: result}, engine_output). A result carries
    pa, effective_pa, clean_count, flags (engine), assistants (engine split), evidence
    (merged v2 inputs or None), pinned_sha, sources, report_flags."""
    targets = target_anchors(ledger)
    results: Dict[str, Dict[str, Any]] = OrderedDict()
    claims: List[Dict[str, Any]] = []
    for a in targets:
        ev = (
            merge_claim_records(a["id"], by_claim[a["id"]])
            if a["id"] in by_claim
            else None
        )
        assistants = ev["assistants"] if ev else []
        pinned, sources, rflags = pinned_sha_for(a, assistants, repo, commit)
        if ev:
            corr, corro = ev["correspondence"], ev["corroborated_by"]
        else:
            corr = OrderedDict(
                [
                    ("corresponds", False),
                    ("basis", ""),
                    ("checked_by", ""),
                    ("checked_at", ""),
                ]
            )
            corro = []
        claims.append(build_claim(a["id"], pinned, assistants, corr, corro))
        results[a["id"]] = {
            "provenance_kind": a.get("provenance_kind"),
            "evidence": ev,
            "pinned_sha": pinned,
            "sources": sources,
            "report_flags": rflags,
        }
    edges = derivation_edges(targets)
    out = run_engine(claims, edges)
    graded = {c["claim_id"]: c for c in out["claims"]}
    for cid, r in results.items():
        g = graded[cid]
        r["pa"] = int(g["pa"])
        r["effective_pa"] = int(g["effective_pa"])
        r["clean_count"] = int(g["clean_count"])
        r["flags"] = list(g["flags"])
        r["assistants"] = list(g["assistants"])
    out["_edges"] = edges
    return results, out


# ---------------------------------------------------------------------------------------
# write
# ---------------------------------------------------------------------------------------
def ledger_assistants(
    anchor_id: str, ev: Dict[str, Any], schema_path: Path = SCHEMA
) -> List[Dict[str, Any]]:
    """The ledger-shape proof_assistants array from the merged evidence; each entry is
    validated against the vendored schema's $defs/ProofAssistant (a record the schema
    would reject is a refusal here, not a red schema-lint later)."""
    arr = [_project(a, LEDGER_ASSISTANT_KEYS) for a in ev["assistants"]]
    try:
        import jsonschema  # type: ignore
    except ImportError:  # pragma: no cover
        raise Refusal("jsonschema is required to validate proof_assistants entries")
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    sub = {
        "$schema": schema.get(
            "$schema", "https://json-schema.org/draft/2020-12/schema"
        ),
        "$defs": schema["$defs"],
        "$ref": "#/$defs/ProofAssistant",
    }
    v = jsonschema.Draft202012Validator(sub)
    for i, entry in enumerate(arr):
        errs = sorted(v.iter_errors(entry), key=lambda e: str(e.path))
        if errs:
            raise Refusal(
                f"{anchor_id}: proof_assistants[{i}] from {ev['files']} fails schema "
                f"$defs/ProofAssistant: " + "; ".join(e.message for e in errs)
            )
    return arr


def plan_writes(
    ledger: Dict[str, Any], results: Dict[str, Dict[str, Any]]
) -> Dict[str, Dict[str, Any]]:
    """{id: {pa_local, pa_effective, proof_assistants (list | None=absent), changed}}.
    The array is planned only on proof/derivation anchors WITH evidence; on any other
    kind with evidence it is refused (flag `array_refused_<kind>`) and only grades go.
    """
    by_id = {a["id"]: a for a in ledger["anchors"]}
    plan: Dict[str, Dict[str, Any]] = OrderedDict()
    for cid, r in results.items():
        a = by_id[cid]
        arr: Optional[List[Dict[str, Any]]] = None
        if r["evidence"] is not None:
            if a.get("provenance_kind") in TARGET_KINDS:
                arr = ledger_assistants(cid, r["evidence"])
            else:
                r["report_flags"].append(f"array_refused_{a.get('provenance_kind')}")
        before_arr = a.get("proof_assistants")
        changed = (
            a.get("pa_local") != r["pa"]
            or a.get("pa_effective") != r["effective_pa"]
            or ("proof_assistants" in a) != (arr is not None)
            or (arr is not None and json.dumps(before_arr) != json.dumps(arr))
        )
        plan[cid] = {
            "pa_local": r["pa"],
            "pa_effective": r["effective_pa"],
            "proof_assistants": arr,
            "changed": changed,
        }
    return plan


def bump_minor(version: str) -> str:
    m = re.match(r"^(\d+)\.(\d+)\.(\d+)$", version)
    if not m:
        raise Refusal(f"ledger version {version!r} is not x.y.z")
    return f"{m.group(1)}.{int(m.group(2)) + 1}.0"


def changelog_note(
    n_targets: int,
    n_changed: int,
    n_records: int,
    commit: str,
    dist: Counter,
    engine_id: str,
) -> str:
    d = ", ".join(f"{k[0]}/{k[1]}: {v}" for k, v in sorted(dist.items()))
    return (
        f"#692: PA backfill of {n_targets} proof/derivation anchors ({n_changed} records "
        f"changed) from {n_records} v2 notary evidence records at pinned master {commit}. "
        f"Grade distribution (pa_local/pa_effective: count) — {d}. pa_local = GradeClaim(...).pa "
        f"on the anchor's own evidence; pa_effective = EffectivePA over prediction_chain "
        f"edges typed derivation (conservative); pinned_sha = claim-source manifest hash "
        f"(sorted `path blob` lines, git hash-object --stdin; architecture ruling seq 2299), "
        f"not stored. Computed by tools/cth-pa ({engine_id}); never hand-set — a wrong grade is "
        f"fixed by new or corrected evidence in inter/notary-evidence/, never by editing "
        f"the ledger (QBP#692 AC1/AC2/AC4). proof_assistants arrays only on provenance_kind "
        f"proof/derivation anchors WITH evidence; internal-compute anchors (PROOF-hessian) "
        f"carry grades only (cth ruling 2026-10-02)."
    )


def apply_writes(
    ledger_path: Path,
    plan: Dict[str, Dict[str, Any]],
    note_args: Dict[str, Any],
    today: str,
    dry_run: bool,
) -> Tuple[bool, str]:
    """Write the planned grades through the confined writer. Returns (changed, version)."""
    changed_ids = [cid for cid, p in plan.items() if p["changed"]]
    if not changed_ids:
        return False, ""
    with ledger_edit(str(ledger_path), dry_run=dry_run) as ed:
        L = ed.ledger
        for cid in changed_ids:
            p = plan[cid]
            a = ed.record("anchors", cid)
            a["pa_local"] = p["pa_local"]  # appended at the end if new
            a["pa_effective"] = p["pa_effective"]
            if p["proof_assistants"] is not None:
                a["proof_assistants"] = p["proof_assistants"]
            elif "proof_assistants" in a:
                del a["proof_assistants"]
        new_version = bump_minor(L["version"])
        L["version"] = new_version
        ed.touch("version")
        if L.get("last_updated") != today:
            L["last_updated"] = today
            ed.touch("last_updated")
        L["changelog"].append(
            OrderedDict(
                [
                    ("version", new_version),
                    ("date", today),
                    ("note", changelog_note(n_changed=len(changed_ids), **note_args)),
                ]
            )
        )
        ed.touch("changelog")
    return True, new_version


# ---------------------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------------------
def _fmt_before(a: Dict[str, Any]) -> str:
    if "pa_local" not in a and "pa_effective" not in a:
        return "—"
    return f"{a.get('pa_local', '—')}/{a.get('pa_effective', '—')}"


def build_report(
    ledger_before: Dict[str, Any],
    results: Dict[str, Dict[str, Any]],
    plan: Dict[str, Dict[str, Any]],
    engine_out: Dict[str, Any],
    meta: Dict[str, Any],
    ignored: List[Dict[str, str]],
    unmatched: List[Dict[str, str]],
) -> Tuple[str, Dict[str, Any]]:
    by_id = {a["id"]: a for a in ledger_before["anchors"]}
    rows: List[Dict[str, Any]] = []
    drops: List[Dict[str, Any]] = []
    dist: Counter = Counter()
    for cid, r in results.items():
        a = by_id[cid]
        p = plan[cid]
        names = [x["assistant"] for x in (p["proof_assistants"] or [])]
        flags = list(r["flags"]) + list(r["report_flags"])
        dist[(r["pa"], r["effective_pa"])] += 1
        row = OrderedDict(
            [
                ("id", cid),
                ("provenance_kind", r["provenance_kind"]),
                ("before_pa_local", a.get("pa_local")),
                ("before_pa_effective", a.get("pa_effective")),
                ("after_pa_local", r["pa"]),
                ("after_pa_effective", r["effective_pa"]),
                ("clean_count", r["clean_count"]),
                ("assistants", names),
                ("flags", flags),
                ("changed", p["changed"]),
                ("pinned_sha", r["pinned_sha"]),
                ("sources", r["sources"]),
                ("evidence_files", (r["evidence"] or {}).get("files", [])),
            ]
        )
        rows.append(row)
        for key, after in (("pa_local", r["pa"]), ("pa_effective", r["effective_pa"])):
            before = a.get(key)
            if isinstance(before, int) and after < before:
                drops.append(
                    {"id": cid, "field": key, "before": before, "after": after}
                )

    rep: Dict[str, Any] = OrderedDict(
        [
            ("issue", "QBP#692"),
            ("generated", meta["today"]),
            ("ledger", meta["ledger"]),
            ("ledger_version_before", ledger_before["version"]),
            ("ledger_version_after", meta.get("version_after") or "(no change)"),
            ("pinned_master_rev", meta["pinned_master_rev"]),
            ("pinned_master_commit", meta["pinned_master_commit"]),
            ("engine", engine_out["engine"]),
            ("verifier", engine_out["verifier"]),
            ("policy", engine_out["policy"]),
            ("evidence_dir", meta["evidence_dir"]),
            ("v2_record_count", meta["v2_record_count"]),
            ("target_anchor_count", len(rows)),
            ("changed_anchor_count", sum(1 for r in rows if r["changed"])),
            (
                "grade_distribution",
                {f"{k[0]}/{k[1]}": v for k, v in sorted(dist.items())},
            ),
            ("derivation_edges", engine_out["_edges"]),
            ("drops", drops),
            ("ignored_non_v2", ignored),
            ("unmatched_claim", unmatched),
            (
                "pinned_sha_convention",
                "claim-source manifest hash: S = {proof_file} ∪ {evidence_ref paths}; "
                "lines `path <git rev-parse <commit>:path>\\n` sorted by path; "
                "pinned_sha = git hash-object --stdin over the lines (ruling seq 2299)",
            ),
            ("anchors", rows),
        ]
    )

    md: List[str] = []
    md.append(f"# QBP#692 PA backfill — {meta['today'][:10]}\n")
    md.append("| | |\n|---|---|")
    md.append(f"| ledger | `{meta['ledger']}` |")
    md.append(
        f"| version | {ledger_before['version']} → {rep['ledger_version_after']} |"
    )
    md.append(
        f"| pinned master | `{meta['pinned_master_rev']}` = `{meta['pinned_master_commit']}` |"
    )
    md.append(f"| engine | `{engine_out['engine']}` ({engine_out['verifier']}) |")
    md.append(f"| policy | `{json.dumps(engine_out['policy'])}` |")
    md.append(f"| evidence dir | `{meta['evidence_dir']}` |")
    md.append(f"| v2 evidence records | {meta['v2_record_count']} |")
    md.append(f"| ignored (non-v2) files | {len(ignored)} |")
    md.append(f"| unmatched claims | {len(unmatched)} |")
    md.append(f"| target anchors | {len(rows)} |")
    md.append(f"| changed anchors | {rep['changed_anchor_count']} |")
    md.append(f"| derivation edges fed to the engine | {len(engine_out['_edges'])} |")
    md.append("")
    md.append("## Grade distribution (pa_local/pa_effective → count)\n")
    md.append("| grade | count |\n|---|---|")
    for k, v in sorted(dist.items()):
        md.append(f"| {k[0]}/{k[1]} | {v} |")
    md.append("")
    md.append("## Drops (any decrease vs the committed value)\n")
    if drops:
        md.append("| id | field | before | after |\n|---|---|---|---|")
        for d in drops:
            md.append(f"| {d['id']} | {d['field']} | {d['before']} | {d['after']} |")
    else:
        md.append(
            "None"
            + (
                " (first backfill: no committed value to drop from)."
                if all(r["before_pa_local"] is None for r in rows)
                else "."
            )
        )
    md.append("")
    md.append("## Spot values (QBP#692 AC3)\n")
    for cid, why in (
        ("PROOF-hessian", "internal-compute; 0 by absence, no array ever"),
        ("PROOF-eigenratios", "derivation on PROOF-hessian; effective 0 via the edge"),
        (
            "PROOF-cd-structure-constant-tables",
            "the Fano table; 2 only once the v2 cycle-8 record (Coq + Lean, correspondence) is promoted",
        ),
    ):
        r = results.get(cid)
        if r:
            md.append(
                f"- `{cid}`: pa_local {r['pa']}, pa_effective {r['effective_pa']} — {why}"
            )
    md.append("")
    md.append("## Before / after — all target anchors (AC4)\n")
    md.append(
        "| id | kind | before local/eff | after local/eff | assistants | flags | pinned_sha |\n"
        "|---|---|---|---|---|---|---|"
    )
    for r in rows:
        before = _fmt_before(by_id[r["id"]])
        names_s = ", ".join(r["assistants"]) or "—"
        flags_s = ", ".join(r["flags"]) or "—"
        ps = r["pinned_sha"][:12] if r["pinned_sha"] else "—"
        md.append(
            f"| {r['id']} | {r['provenance_kind']} | {before} | "
            f"{r['after_pa_local']}/{r['after_pa_effective']} | {names_s} | {flags_s} | `{ps}` |"
        )
    md.append("")
    md.append(
        "## Ignored evidence files (not the engine v2 record shape; never parsed for grades)\n"
    )
    if ignored:
        for i in ignored:
            md.append(f"- `{i['file']}` — {i['reason']}")
    else:
        md.append("None.")
    md.append("")
    md.append(
        "## Unmatched claims (v2 records whose `claim` is not a ledger anchor id)\n"
    )
    if unmatched:
        for u in unmatched:
            md.append(f"- `{u['file']}` — claim `{u['claim']}`")
    else:
        md.append("None.")
    md.append("")
    md.append("## pinned_sha manifests (S and per-file blobs at the pinned commit)\n")
    md.append(f"{rep['pinned_sha_convention']}\n")
    md.append("<details><summary>per-anchor manifests</summary>\n")
    for r in rows:
        if r["sources"]:
            lines = "; ".join(f"`{s['path']} {s['blob']}`" for s in r["sources"])
            md.append(f"- `{r['id']}` → `{r['pinned_sha']}` ← {lines}")
        else:
            md.append(
                f"- `{r['id']}` → (no resolvable source; pinned_sha empty, inert)"
            )
    md.append("\n</details>\n")
    return "\n".join(md) + "\n", rep


# ---------------------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------------------
def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        description="Compute pa_local / pa_effective / proof_assistants from notary evidence "
        "via the vendored confluent-trust PA engine and write them through the confined "
        "ledger writer. No argument takes a grade."
    )
    ap.add_argument(
        "--evidence-dir",
        type=Path,
        default=DEFAULT_EVIDENCE_DIR,
        help="directory of notary evidence records (v2 engine shape graded; others ignored)",
    )
    ap.add_argument(
        "--pinned-master",
        default="origin/master",
        help="git rev of QBP master the ledger is pinned to (resolved to a full sha)",
    )
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument(
        "--report",
        type=Path,
        default=None,
        help="markdown report path (a .json sibling is written too); "
        "default analysis/692-pa-backfill/backfill-<date>.md",
    )
    ap.add_argument("--ledger", type=Path, default=LEDGER, help="(tests) ledger path")
    ap.add_argument(
        "--repo", type=Path, default=ROOT, help="(tests) git repo for the pinned rev"
    )
    return ap


def run(
    evidence_dir: Path,
    pinned_master: str,
    ledger_path: Path,
    repo: Path,
    dry_run: bool,
    report_path: Optional[Path],
    today: Optional[str] = None,
    write_report: bool = True,
) -> Dict[str, Any]:
    """The whole pipeline; returns {changed, version, report, results}."""
    today = today or _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT00:00:00Z")
    commit = resolve_commit(repo, pinned_master)
    ledger_before = json.loads(ledger_path.read_text(encoding="utf-8"))
    records, ignored = load_evidence(evidence_dir)
    anchor_ids = {a["id"] for a in ledger_before["anchors"]}
    by_claim, unmatched = group_by_claim(records, anchor_ids)
    results, engine_out = grade_ledger(ledger_before, by_claim, repo, commit)
    plan = plan_writes(ledger_before, results)
    dist: Counter = Counter((r["pa"], r["effective_pa"]) for r in results.values())
    note_args = dict(
        n_targets=len(results),
        n_records=len(records),
        commit=commit,
        dist=dist,
        engine_id=engine_out["engine"],
    )
    changed, version = apply_writes(ledger_path, plan, note_args, today, dry_run)
    meta = {
        "today": today,
        "ledger": str(ledger_path),
        "pinned_master_rev": pinned_master,
        "pinned_master_commit": commit,
        "evidence_dir": str(evidence_dir),
        "v2_record_count": len(records),
        "version_after": version if changed else None,
    }
    md, rep = build_report(
        ledger_before, results, plan, engine_out, meta, ignored, unmatched
    )
    if write_report:
        rp = report_path or (REPORT_DIR / f"backfill-{today[:10]}.md")
        rp.parent.mkdir(parents=True, exist_ok=True)
        rp.write_text(md, encoding="utf-8")
        rp.with_suffix(".json").write_text(
            json.dumps(rep, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        rep["_report_md"] = str(rp)
    return {
        "changed": changed,
        "version": version,
        "report": rep,
        "results": results,
        "plan": plan,
        "distribution": dist,
    }


def main(argv: Optional[List[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    out = run(
        evidence_dir=args.evidence_dir,
        pinned_master=args.pinned_master,
        ledger_path=args.ledger,
        repo=args.repo,
        dry_run=args.dry_run,
        report_path=args.report,
    )
    rep = out["report"]
    print(
        f"pinned master {rep['pinned_master_rev']} = {rep['pinned_master_commit']}; "
        f"engine {rep['engine']}"
    )
    print(
        f"v2 evidence records: {rep['v2_record_count']}; ignored non-v2: "
        f"{len(rep['ignored_non_v2'])}; unmatched claims: {len(rep['unmatched_claim'])}"
    )
    print(
        f"target anchors: {rep['target_anchor_count']}; distribution "
        f"(local/effective: n): {rep['grade_distribution']}; drops: {len(rep['drops'])}"
    )
    if "_report_md" in rep:
        print(f"report: {rep['_report_md']} (+ .json)")
    if not out["changed"]:
        print(
            "already applied: every target anchor carries exactly the computed grades"
        )
        return 1
    print(
        f"{'DRY ' if args.dry_run else ''}applied: {rep['changed_anchor_count']} anchors; "
        f"ledger {rep['ledger_version_before']} → {out['version']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
