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
   reported as `unmatched_claim`; records whose `claim` IS a ledger anchor but not a
   target anchor (step 2) are reported as `evidence_for_non_target` and never graded (RT
   N3a). Assistants are projected onto the engine's known fields (the fixtures'
   `attestation`/`expected_pa`/`flags` oracles are test-only and dropped).
2. TARGETS. Anchors with `provenance_kind ∈ {proof, derivation}` ∪ ids starting `PROOF-`
   (147 at ledger 6.13.0, incl. `PROOF-hessian` which is `internal-compute`).
3. pinned_sha (architecture ruling, live-test seq 2299 — FINAL): the claim-source MANIFEST
   hash. S = {anchor proof_file} ∪ {SAME-REPO paths named by the claim's v2
   evidence_refs}, deduplicated. evidence_ref grammar (§I4 ruling on PR #695, live-test
   seq 2342; RT C1): `[<owner>/<repo>:]<path>@<commit>#<target>` — no prefix means THIS
   repo (QBP) and only such refs enter S; a prefixed (cross-repo, e.g. the notary's Coq
   port `JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#…`) ref MUST
   carry `@<commit>` — a 7–40 hex sha (RT N8: `@main` / `@HEAD` / a tag is a moving
   ref, not a pin ⇒ refusal) — is pinned by that commit plus `reproduce`, never enters S,
   and is reported with flag `cross_repo_evidence` (`parse_evidence_ref` /
   `evidence_ref_is_local` / `evidence_ref_path`; a prefixed ref without a commit is a
   refusal). The explicit self-prefix `JamesPagetButler/QBP:` names THIS repo and is
   normalised to a local ref (RT N9: it enters S; a local commit token stays permissive —
   same-repo files are resolved at the pinned master, never at the ref's token). For p in
   sorted(S) the manifest line is
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
   (`pinned_sha` has no ledger home at schema 0.3.5). S is computed over EVERY assistant
   of the merged record BEFORE the target filter (RT C4): the filter decides who reaches
   the engine, never what S is — a dropped same-repo companion must not shrink the
   manifest and false-flag the on-target survivor `stale` (notary computes `source_sha`
   over the record it emits, i.e. over all of them).
3b. TARGET FILTER (RT C2 / ruling 3e-refined item 4; cth seq 2352 + architecture seq
   2353; §I4 round 2 live-test seq 2367 + RT re-check C5 — FINAL): an assistant counts
   toward an anchor's grade only if it attests THAT anchor's headline statement.
   `filter_assistants_by_target` keeps an assistant iff
   (a) DIRECT match (`direct_target_match`, no maps needed) — ONLY when the assistant is
   `lean4` AND its evidence_ref is local (no owner/repo prefix) AND either its `#target`
   is fully qualified (dotted) and equals `anchor.lean_theorem` verbatim, or its `#target`
   is a short (dot-free) name equal to `lean_theorem`'s last dotted component AND the
   ref's path equals `anchor.proof_file` (an unqualified name identifies the headline
   only inside the headline's own file; P-D); OR
   (b) CORRESPONDENCE — the record's block has `corresponds: true`, a non-empty
   `checked_by` that is not any assistant's `producer`, AND a STRUCTURED `maps[]` entry
   `{target: <this assistant's #target>, lean_theorem: <this anchor's lean_theorem>}`,
   BOTH compared VERBATIM (RT N14: no short-name relaxation inside maps — the map is the
   machine-checked field; `basis` stays prose and is never parsed). Route (b) is open
   ONLY across KERNELS (`maps_may_rescue`, RT C6; architecture seq 2372 + cth 2371 —
   one function so a ruling flips it in a line): a correspondence attests that a
   DIFFERENT prover's kernel checked the same statement, so the assistant's prover must
   differ from the headline's — a `lean_theorem` headline is Lean 4, so `maps` may
   rescue coq / agda, never `lean4`. A lean4 target that fails (a) is dropped REGARDLESS
   of `maps`, same-repo or cross-repo: a Lean theorem that is not `lean_theorem` is a
   different Lean statement, and a map from it to the headline carries zero kernel
   diversity — it is a declared Lean→Lean derivation (a chain edge, seq 2338), never a
   cross-prover correspondence. Repo-locality is a PROVENANCE axis only (`cross_repo_
   evidence` flag, S membership, staleness), never a maps-eligibility criterion. So:
   coq/agda whatever the lemma is named (P-A: a Coq lemma literally named
   `fanoTableF4_eq_cayleyDickson`; P-B: an Agda ref carrying the FQ Lean name verbatim),
   local or foreign, counts ONLY through route (b); a lean4 short name in another file
   (P-D), a local lean4 companion theorem (C6) or a foreign Lean port counts through
   NEITHER; else dropped with report flag
   `target_not_headline:<assistant>` and never reaches the engine — so a companion
   theorem's evidence cannot lift a headline, a name coincidence across provers is not a
   correspondence, and a misfiled valid pair grades the headline 0, not 2. `maps` is
   encoder-side only: `pa-grade`'s decoder is strict (`DisallowUnknownFields`), so the
   correspondence handed to the engine is projected onto its four fields. The rule lives
   in ONE function so it can be tightened or switched off by ruling. An anchor WITHOUT
   `lean_theorem` admits NOTHING — both routes need a headline (route (b) pairs a target
   with THIS anchor's `lean_theorem`); its evidence is dropped under the single anchor-
   side flag `no_lean_theorem` (RT N11: the defect is the anchor's, not the evidence's);
   the report counts these anchors (`targets_without_lean_theorem`; 22 at ledger 6.16.0,
   all `theory` / `theory-external` with no Lean `proof_file`).
4. ENGINE. One `pa.Claim` per target anchor {claim, consumer "qbp#692-ci", pinned_sha,
   proof_assistants, correspondence, corroborated_by}. Edges: every `prediction_chain`
   entry (id → target) whose target is also a target anchor, typed `derivation`. This is
   CONSERVATIVE — a derivation edge can only LOWER effective PA: `EffectivePA(X)` is the
   min over X and its derivation DEPENDENCIES (the anchors X's `prediction_chain` points
   at), never over X's dependents (RT N2); typed relevance / mention
   edges (which the engine excludes from the min) arrive with the Phase-1 chain migration,
   and until then every chain entry is treated as a derivation. Anchors with no evidence
   enter the same invocation as empty claims (zero assistants ⇒ PA 0 by construction) so
   that edges into them still fold; no evidence is graded for them. Policy
   `require_signature: false` (inter#149 v0 — StubV0, every record unsigned).
5. WRITE (confined). For every target anchor `pa_local` = engine `pa`, `pa_effective` =
   engine `effective_pa` (integers). `proof_assistants` = the ledger-shape array
   [{assistant, evidence_ref, trust_check, source_sha, producer}] over the assistants that
   SURVIVED the target filter, ONLY when (a) at least one did (an empty array is never
   written — the key is omitted and the report flags `no_admissible_evidence`; RT N3b)
   AND (b) `provenance_kind ∈ {proof, derivation}` — on
   `internal-compute` (PROOF-hessian) the two grades are written and the array NEVER is
   (cth-implementor ruling 2026-10-02 3d, live-test seq 2290). New keys are appended at the
   end of the record (key order is content for the confined writer). A stale array whose
   evidence has been withdrawn is removed. If nothing would change: exit 1 "already
   applied". Version minor-bump, `last_updated` = today UTC, one changelog entry.
6. REPORT. `--report` (default analysis/692-pa-backfill/backfill-<date>.md + .json): the
   AC4 before/after table for all target anchors, the drop list, ignored_non_v2 /
   unmatched_claim / evidence_for_non_target, pinned master commit, per-anchor S + blobs +
   pinned_sha, engine pin, and every per-anchor flag (engine + encoder).

Usage:
  python3 scripts/encode_pa_from_evidence.py [--evidence-dir DIR] [--pinned-master REV]
                                              [--dry-run] [--report PATH]
There is NO --pa argument. --ledger / --repo exist for tests (paths, never grades).
--evidence-dir defaults to the beekeeper's checkout of inter/notary-evidence; that is a
default only — CI and other checkouts pass the path explicitly (RT N5).
"""

from __future__ import annotations

import argparse
import atexit
import datetime as _dt
import hashlib
import json
import os
import re
import shutil
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
# RT N8: a cross-repo ref is pinned by its commit alone, so the token must BE a commit
# (7–40 hex), never a branch / tag / HEAD. Local tokens stay permissive: same-repo files
# are resolved at the pinned master, never at the ref's token.
CROSS_REPO_COMMIT_RE = re.compile(r"^[0-9a-f]{7,40}$")
# RT N9: the explicit self-prefix names THIS repo; such a ref is local and enters S.
SELF_REPO = "JamesPagetButler/QBP"
# The one assistant whose `#target` can name a Lean `lean_theorem` directly (seq 2367).
LEAN_ASSISTANT = "lean4"

# The engine's own field names (pa.go JSON tags). Everything else on an evidence
# assistant / record is an oracle or provenance annotation and is not an engine input.
ASSISTANT_KEYS = ("assistant", "evidence_ref", "producer", "trust_check", "source_sha")
DECLARED_KEYS = ("mode", "output_hash", "axioms", "exit_code")
DERIVED_KEYS = ("output_hash", "tactics_used", "axioms", "exit_code", "kernel_clean")
CORRESPONDENCE_KEYS = ("corresponds", "basis", "checked_by", "checked_at")
# Encoder-side ONLY (never handed to the engine, whose decoder rejects unknown fields):
# correspondence.maps = [{target, lean_theorem}] — the structured per-target pairs the
# target filter reads (architecture ruling seq 2353). `basis` is prose, never parsed.
CORRESPONDENCE_MAPS_KEY = "maps"
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
    records: List[Tuple[Path, Dict[str, Any]]],
    anchor_ids: set,
    target_ids: Optional[set] = None,
    kinds: Optional[Dict[str, Any]] = None,
) -> Tuple[
    Dict[str, List[Tuple[Path, Dict[str, Any]]]],
    List[Dict[str, str]],
    List[Dict[str, Any]],
]:
    """(by_claim over TARGET anchors, unmatched_claim, evidence_for_non_target). A record
    whose claim is a ledger anchor but not a target anchor (e.g. a MEAS-*) is listed, not
    graded and not silently dropped (RT N3a). `target_ids=None` ⇒ every anchor is a target
    (tests of the merge path)."""
    by_claim: Dict[str, List[Tuple[Path, Dict[str, Any]]]] = OrderedDict()
    unmatched: List[Dict[str, str]] = []
    non_target: List[Dict[str, Any]] = []
    for p, doc in records:
        cid = doc["claim"]
        if cid not in anchor_ids:
            unmatched.append({"file": str(p), "claim": cid})
            continue
        if target_ids is not None and cid not in target_ids:
            non_target.append(
                {
                    "file": str(p),
                    "claim": cid,
                    "provenance_kind": (kinds or {}).get(cid),
                    "assistants": [
                        a.get("assistant") for a in doc.get("proof_assistants", [])
                    ],
                }
            )
            continue
        by_claim.setdefault(cid, []).append((p, doc))
    return by_claim, unmatched, non_target


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


EVIDENCE_REF_RE = re.compile(
    r"^(?:(?P<repo>[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+):)?"  # optional <owner>/<repo>:
    r"(?P<path>[^@#:\s]+)"  # path (no '@', '#', ':' or whitespace)
    r"(?:@(?P<commit>[^#\s]+))?"  # optional @<commit> (any rev token; cross-repo must have one)
    r"(?:#(?P<target>\S+))?$"  # optional #<target>
)


def parse_evidence_ref(ref: Any) -> Dict[str, Optional[str]]:
    """`[<owner>/<repo>:]<path>@<commit>#<target>` (ruling: live-test seq 2342).

    No prefix means this repo (QBP). A cross-repo ref MUST carry a commit — it is
    pinned by that commit plus `reproduce`, and it never enters the claim-source
    manifest S. Refuses anything unparseable."""
    if not isinstance(ref, str) or not ref:
        raise Refusal(f"evidence_ref is not a non-empty string: {ref!r}")
    m = EVIDENCE_REF_RE.match(ref)
    if not m or not m.group("path"):
        raise Refusal(
            f"evidence_ref does not match [<owner>/<repo>:]<path>@<commit>#<target>: {ref!r}"
        )
    d = m.groupdict()
    if d["repo"] is not None and d["repo"].lower() == SELF_REPO.lower():
        # RT N9: `JamesPagetButler/QBP:<path>` IS this repo — local. RT N15: GitHub
        # owner/repo names are case-insensitive, so `jamespagetbutler/qbp:` is too.
        d["repo"] = None
    if d["repo"] is not None and d["commit"] is None:
        raise Refusal(
            f"cross-repo evidence_ref {ref!r} carries no @<commit>; a foreign file is "
            "pinned only by its commit (plus reproduce) and cannot be graded without one"
        )
    if d["repo"] is not None and not CROSS_REPO_COMMIT_RE.match(d["commit"] or ""):
        raise Refusal(
            f"cross-repo evidence_ref {ref!r}: @{d['commit']} is not a 7-40 hex commit "
            "sha; a branch, tag or HEAD is a moving ref, not a pin (RT N8)"
        )
    return d


def evidence_ref_is_local(ref: Any) -> bool:
    """True iff the ref names a file in THIS repo (no <owner>/<repo>: prefix)."""
    return parse_evidence_ref(ref)["repo"] is None


def evidence_ref_path(ref: Any) -> str:
    """Same-repo `path@sha#theorem` → `path`. Refuses a cross-repo ref: a foreign
    path must never be looked up in the QBP tree (§I4 seam bug, seq 2342)."""
    d = parse_evidence_ref(ref)
    if d["repo"] is not None:
        raise Refusal(
            f"evidence_ref {ref!r} is cross-repo ({d['repo']}); it has no QBP path and "
            "must not enter the claim-source manifest"
        )
    return d["path"]  # type: ignore[return-value]


def merge_claim_records(
    cid: str, recs: List[Tuple[Path, Dict[str, Any]]]
) -> Dict[str, Any]:
    """Fold one anchor's v2 records into the engine inputs: assistants concatenated in
    file order; the correspondence block from the single record that asserts one (two
    asserting records are ambiguous ⇒ refuse); corroborated_by unioned."""
    assistants: List[Dict[str, Any]] = []
    corr: Optional[Dict[str, Any]] = None
    corr_src: Optional[Path] = None
    maps: List[Dict[str, str]] = []
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
            maps = correspondence_maps(cid, p, c)
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
        "correspondence": corr,  # engine fields only
        "correspondence_maps": maps,  # encoder-side target pairs (never sent)
        "corroborated_by": corroborated,
        "files": [str(p) for p, _ in recs],
    }


def correspondence_maps(cid: str, src: Path, c: Dict[str, Any]) -> List[Dict[str, str]]:
    """The structured `maps: [{target, lean_theorem}]` of a correspondence block (seq 2353).
    Absent ⇒ []. Present but malformed ⇒ refusal (a pair the filter cannot read must not
    silently become "no pair")."""
    raw = c.get(CORRESPONDENCE_MAPS_KEY)
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise Refusal(f"{cid}: correspondence.maps in {src} is not a list")
    out: List[Dict[str, str]] = []
    for i, m in enumerate(raw):
        if (
            not isinstance(m, dict)
            or not isinstance(m.get("target"), str)
            or not m["target"]
            or not isinstance(m.get("lean_theorem"), str)
            or not m["lean_theorem"]
        ):
            raise Refusal(
                f"{cid}: correspondence.maps[{i}] in {src} is not "
                "{target: <str>, lean_theorem: <str>}"
            )
        out.append({"target": m["target"], "lean_theorem": m["lean_theorem"]})
    return out


# ---------------------------------------------------------------------------------------
# target filter (RT C2; cth seq 2352 + architecture seq 2353) — ONE function, swappable
# ---------------------------------------------------------------------------------------
def names_match(a: Optional[str], b: Optional[str]) -> bool:
    """Fully-qualified theorem-name equality with ONE relaxation: a short (dot-free) name
    matches an FQ name iff it equals that name's last dotted component. Two FQ names must
    be identical; two short names must be identical."""
    if not a or not b:
        return False
    if a == b:
        return True
    if "." not in a and "." in b:
        return a == b.rsplit(".", 1)[-1]
    if "." not in b and "." in a:
        return b == a.rsplit(".", 1)[-1]
    return False


def assistant_target(a: Dict[str, Any]) -> Optional[str]:
    """The `#target` of an assistant's evidence_ref (None when the ref carries none)."""
    return parse_evidence_ref(a.get("evidence_ref"))["target"]


def anchor_headline(anchor: Dict[str, Any]) -> Optional[str]:
    """The anchor's `lean_theorem` when it has a non-empty one, else None."""
    h = anchor.get("lean_theorem")
    return h if isinstance(h, str) and h else None


def direct_target_match(anchor: Dict[str, Any], a: Dict[str, Any]) -> bool:
    """Route (a) — the DIRECT match, no maps needed (§I4 round 2, live-test seq 2367;
    RT re-check C5 probes P-A / P-B / P-D). ONLY the Lean assistant, ONLY a same-repo ref:

      assistant == "lean4"  and  the evidence_ref is local  and
        ( target is fully qualified (dotted) and target == anchor.lean_theorem verbatim
        | target is short (dot-free), equals lean_theorem's last dotted component,
          AND the ref's path == anchor.proof_file )

    A short name is unqualified: it identifies the headline only inside the headline's
    own file (P-D). Every other assistant — coq / agda whatever its lemma is named (P-A,
    P-B), any cross-repo ref — reaches the engine only through a correspondence maps[]
    entry. A short `lean_theorem` (8 live anchors) therefore matches only a short target
    in its own proof_file, never an FQ target in some namespace."""
    headline = anchor_headline(anchor)
    if headline is None or a.get("assistant") != LEAN_ASSISTANT:
        return False
    d = parse_evidence_ref(a.get("evidence_ref"))
    target = d["target"]
    if d["repo"] is not None or not target:
        return False
    if "." in target:
        return target == headline
    if target != headline.rsplit(".", 1)[-1]:
        return False
    proof_file = anchor.get("proof_file")
    return isinstance(proof_file, str) and bool(proof_file) and d["path"] == proof_file


def headline_kind(anchor: Dict[str, Any]) -> str:
    """The prover whose kernel checked the anchor's headline. At schema 0.3.5 the only
    headline field is `lean_theorem`, so every headline is Lean 4."""
    return LEAN_ASSISTANT


def maps_may_rescue(assistant_kind: Optional[str], headline_kind: str) -> bool:
    """RT C6 (architecture seq 2372 + cth 2371) — may a correspondence `maps[]` entry
    admit an assistant that failed the direct match? The criterion is KERNEL DIVERSITY:
    a correspondence attests that a DIFFERENT prover's kernel checked the same statement,
    so `maps` may rescue only an assistant whose prover differs from the headline's.
    For a `lean_theorem` headline that means `assistant != "lean4"` — a Lean theorem
    that is not `lean_theorem` is a different Lean statement, and a map from it to the
    headline carries zero kernel diversity: it is a declared Lean→Lean derivation (a
    chain edge, seq 2338), not a cross-prover correspondence, same-repo or cross-repo.
    Repo-locality is a provenance axis (`cross_repo_evidence`, S, staleness), never a
    maps-eligibility criterion. ONE function; a ruling flips it in a line."""
    return bool(assistant_kind) and assistant_kind != headline_kind


def maps_pair(
    maps: Optional[List[Dict[str, str]]], target: Optional[str], headline: str
) -> bool:
    """Some `maps[]` entry equals {target, lean_theorem} VERBATIM (RT N14: the map is the
    machine-checked field — no short-name relaxation on either side)."""
    if not target:
        return False
    return any(
        m.get("target") == target and m.get("lean_theorem") == headline
        for m in (maps or [])
    )


def filter_assistants_by_target(
    anchor: Dict[str, Any],
    assistants: List[Dict[str, Any]],
    correspondence: Dict[str, Any],
    maps: Optional[List[Dict[str, str]]] = None,
) -> Tuple[List[Dict[str, Any]], List[str]]:
    """THE target-vs-headline rule (module doc §3b). Returns (kept, dropped_flags).

    no lean_theorem on the anchor  ⇒  nothing kept, ONE flag `no_lean_theorem` (RT N11)
    keep iff  direct_target_match(anchor, a)          # lean4 + local + FQ | short-in-own-file
          or  (maps_may_rescue(a.assistant, headline_kind)   # RT C6: prover ≠ headline's
               and correspondence.corresponds is True
               and correspondence.checked_by is non-empty
               and checked_by is not any assistant's producer
               and some maps entry == {target: a.#target, lean_theorem: anchor.lean_theorem}
                                                      # RT N14: verbatim, both sides)
    else drop with flag `target_not_headline:<assistant>`.
    Dropped assistants never reach the engine or the ledger array. S is NOT decided here
    (RT C4): `pinned_sha_for` runs over the whole record before this filter."""
    headline = anchor_headline(anchor)
    if headline is None:
        return [], (["no_lean_theorem"] if assistants else [])
    producers = {a.get("producer") for a in assistants if a.get("producer")}
    checked_by = correspondence.get("checked_by")
    corr_ok = (
        correspondence.get("corresponds") is True
        and isinstance(checked_by, str)
        and bool(checked_by)
        and checked_by not in producers
    )
    kept: List[Dict[str, Any]] = []
    dropped: List[str] = []
    for a in assistants:
        if direct_target_match(anchor, a):
            kept.append(a)
            continue
        if (
            corr_ok
            and maps_may_rescue(a.get("assistant"), headline_kind(anchor))
            and maps_pair(maps, assistant_target(a), headline)
        ):
            kept.append(a)
            continue
        dropped.append(f"target_not_headline:{a.get('assistant', '?')}")
    return kept, dropped


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
    record_files: Optional[List[str]] = None,
) -> Tuple[str, List[Dict[str, str]], List[str]]:
    """THE pinned_sha convention (one place; swap here if the ruling changes).

    Returns (pinned_sha, sources=[{path, blob}], report_flags). See module doc §3.
    `record_files` = the evidence record file(s) the assistants came from; a refusal
    names them and the claim id (RT N13) so one malformed companion ref in a promoted
    record can be found without re-running the whole batch."""
    flags: List[str] = []
    where = (
        f" (claim {anchor['id']!r} in record " + ", ".join(record_files) + ")"
        if record_files
        else f" (claim {anchor['id']!r})"
    )
    has_evidence = bool(assistants)
    proof_file = anchor.get("proof_file")
    paths: Dict[str, str] = (
        OrderedDict()
    )  # path -> origin ("proof_file" | "evidence_ref")
    if isinstance(proof_file, str) and proof_file:
        paths[proof_file] = "proof_file"
    for a in assistants:
        ref = a.get("evidence_ref")
        if not evidence_ref_is_local(ref):
            # cross-repo evidence (e.g. the notary's Coq port): validated above
            # (prefix + commit), pinned by its own commit + reproduce; it never
            # enters S — the claim-source manifest is over THIS repo's files only.
            if "cross_repo_evidence" not in flags:
                flags.append("cross_repo_evidence")
            continue
        p = evidence_ref_path(ref)
        paths.setdefault(p, "evidence_ref")
    sources: List[Dict[str, str]] = []
    for path in sorted(paths):
        blob = blob_sha(repo, commit, path)
        if blob is None:
            if paths[path] == "evidence_ref":
                raise Refusal(
                    f"{anchor['id']}: evidence_ref path {path!r} does not exist at pinned "
                    f"master {commit[:12]}{where}; pinned_sha cannot be computed for "
                    "evidence that names a file the pinned tree does not have (S covers "
                    "every same-repo ref of the record, dropped or kept)"
                )
            if has_evidence:
                raise Refusal(
                    f"{anchor['id']}: declared proof_file {path!r} does not exist at "
                    f"pinned master {commit[:12]}{where} while evidence is being graded; "
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
        rflags: List[str] = []
        # RT C4: S = proof_file ∪ the CLAIM's same-repo refs (seq 2299) — over EVERY
        # assistant of the merged record, BEFORE the target filter. The filter decides
        # who reaches the engine; it never shrinks the manifest (a dropped companion
        # must not false-flag the on-target survivor `stale`).
        pinned, sources, pflags = pinned_sha_for(
            a,
            ev["assistants"] if ev else [],
            repo,
            commit,
            ev["files"] if ev else None,
        )
        if ev:
            kept, dropped = filter_assistants_by_target(
                a, ev["assistants"], ev["correspondence"], ev["correspondence_maps"]
            )
            ev["dropped_assistants"] = [
                x for x in ev["assistants"] if not any(x is k for k in kept)
            ]
            ev["assistants"] = kept
            rflags.extend(dropped)
            if not kept:
                rflags.append("no_admissible_evidence")
        assistants = ev["assistants"] if ev else []
        rflags.extend(pflags)
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
    The array is planned only on proof/derivation anchors with at least one ADMISSIBLE
    assistant (an empty array is never written — RT N3b); on any other kind with
    admissible evidence it is refused (flag `array_refused_<kind>`) and only grades go.
    """
    by_id = {a["id"]: a for a in ledger["anchors"]}
    plan: Dict[str, Dict[str, Any]] = OrderedDict()
    for cid, r in results.items():
        a = by_id[cid]
        arr: Optional[List[Dict[str, Any]]] = None
        if r["evidence"] is not None and r["evidence"]["assistants"]:
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
    non_target: Optional[List[Dict[str, Any]]] = None,
) -> Tuple[str, Dict[str, Any]]:
    non_target = non_target or []
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
                (
                    "dropped_assistants",
                    [
                        {
                            "assistant": x.get("assistant"),
                            "evidence_ref": x.get("evidence_ref"),
                        }
                        for x in (r["evidence"] or {}).get("dropped_assistants", [])
                    ],
                ),
            ]
        )
        rows.append(row)
        for key, after in (("pa_local", r["pa"]), ("pa_effective", r["effective_pa"])):
            before = a.get(key)
            if isinstance(before, int) and after < before:
                drops.append(
                    {"id": cid, "field": key, "before": before, "after": after}
                )

    # RT N11: anchors with no `lean_theorem` admit nothing (both routes need a headline)
    no_headline = [cid for cid in results if anchor_headline(by_id[cid]) is None]
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
            (
                "targets_without_lean_theorem",
                {"count": len(no_headline), "ids": no_headline},
            ),
            ("changed_anchor_count", sum(1 for r in rows if r["changed"])),
            (
                "grade_distribution",
                {f"{k[0]}/{k[1]}": v for k, v in sorted(dist.items())},
            ),
            ("derivation_edges", engine_out["_edges"]),
            ("drops", drops),
            ("ignored_non_v2", ignored),
            ("unmatched_claim", unmatched),
            ("evidence_for_non_target", non_target),
            (
                "pinned_sha_convention",
                "claim-source manifest hash: S = {proof_file} ∪ {SAME-REPO evidence_ref "
                "paths — grammar [<owner>/<repo>:]<path>@<commit>#<target>, no prefix = "
                "QBP; cross-repo refs never enter S (seq 2342)}; "
                "lines `path <git rev-parse <commit>:path>\\n` sorted by path; "
                "pinned_sha = git hash-object --stdin over the lines (ruling seq 2299)",
            ),
            (
                "target_filter",
                "an assistant counts iff (a) it is lean4 with a same-repo evidence_ref "
                "whose #target equals the anchor's lean_theorem as an FQ name, or is the "
                "short last component AND the ref's path is the anchor's proof_file; or "
                "(b) a non-producer correspondence (corresponds true, checked_by set) "
                "carries a maps[] entry {target, lean_theorem} pairing it with this "
                "anchor's lean_theorem — every other assistant (coq/agda whatever its "
                "lemma is named, any cross-repo ref) only via (b); else dropped, flag "
                "target_not_headline:<assistant>; an anchor without lean_theorem admits "
                "nothing, flag no_lean_theorem (RT C2; cth seq 2352, architecture seq "
                "2353, §I4 round 2 seq 2367, RT C5/N11)",
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
    md.append(f"| evidence for non-target anchors | {len(non_target)} |")
    md.append(f"| target anchors | {len(rows)} |")
    md.append(
        f"| target anchors without `lean_theorem` (admit nothing; flag `no_lean_theorem`) "
        f"| {len(no_headline)} |"
    )
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
    md.append(
        "## Evidence for non-target anchors (v2 records whose `claim` is a ledger anchor "
        "that is not proof/derivation/PROOF-*; listed, never graded)\n"
    )
    if non_target:
        for u in non_target:
            md.append(
                f"- `{u['file']}` — claim `{u['claim']}` (provenance_kind "
                f"`{u.get('provenance_kind')}`; assistants {u.get('assistants')})"
            )
    else:
        md.append("None.")
    md.append("")
    md.append("## Target filter\n")
    md.append(f"{rep['target_filter']}\n")
    dropped_rows = [r for r in rows if r["dropped_assistants"]]
    if dropped_rows:
        for r in dropped_rows:
            ds = "; ".join(
                f"`{d['assistant']}` ← `{d['evidence_ref']}`"
                for d in r["dropped_assistants"]
            )
            md.append(f"- `{r['id']}` dropped: {ds}")
    else:
        md.append("No assistant dropped.")
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
# dry-run scratch (RT N10 + N16)
# ---------------------------------------------------------------------------------------
_DRY_RUN_SCRATCH: List[Path] = []


def dry_run_scratch_dir() -> Path:
    """A fresh scratch directory for a `--dry-run` report without `--report`. It exists
    for the life of the process (callers may read the report back) and is removed at
    interpreter exit (RT N16: a CI runner dry-running per PR must not accumulate them).
    Pass `--report` to keep a dry-run report."""
    d = Path(tempfile.mkdtemp(prefix="qbp692-pa-dry-run-"))
    if not _DRY_RUN_SCRATCH:
        atexit.register(cleanup_dry_run_scratch)
    _DRY_RUN_SCRATCH.append(d)
    return d


def cleanup_dry_run_scratch() -> List[Path]:
    """Remove every dry-run scratch directory made by this process; returns them."""
    gone: List[Path] = []
    while _DRY_RUN_SCRATCH:
        d = _DRY_RUN_SCRATCH.pop()
        shutil.rmtree(d, ignore_errors=True)
        gone.append(d)
    return gone


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
        help="directory of notary evidence records (v2 engine shape graded; others "
        "ignored). The default is the beekeeper's checkout of inter/notary-evidence — "
        "a default only; CI and other checkouts pass the path explicitly",
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
    target_ids = {a["id"] for a in target_anchors(ledger_before)}
    kinds = {a["id"]: a.get("provenance_kind") for a in ledger_before["anchors"]}
    by_claim, unmatched, non_target = group_by_claim(
        records, anchor_ids, target_ids, kinds
    )
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
        ledger_before, results, plan, engine_out, meta, ignored, unmatched, non_target
    )
    if write_report:
        if report_path is not None:
            rp = report_path
        elif dry_run:
            # RT N10: a dry run must never clobber the committed record under
            # REPORT_DIR (the AC4 before/after table is the genuine record of the
            # last applied run). Without --report it goes to a scratch directory
            # that is removed at exit (RT N16) — pass --report to keep one.
            rp = dry_run_scratch_dir() / f"backfill-{today[:10]}.dry-run.md"
        else:
            rp = REPORT_DIR / f"backfill-{today[:10]}.md"
        rp.parent.mkdir(parents=True, exist_ok=True)
        rp.write_text(md, encoding="utf-8")
        rp.with_suffix(".json").write_text(
            json.dumps(rep, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        rep["_report_md"] = str(rp)
        rep["_report_scratch"] = bool(dry_run and report_path is None)
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
        f"{len(rep['ignored_non_v2'])}; unmatched claims: {len(rep['unmatched_claim'])}; "
        f"evidence for non-target anchors: {len(rep['evidence_for_non_target'])}"
    )
    print(
        f"target anchors: {rep['target_anchor_count']}; distribution "
        f"(local/effective: n): {rep['grade_distribution']}; drops: {len(rep['drops'])}"
    )
    print(
        f"target anchors without lean_theorem (admit nothing): "
        f"{rep['targets_without_lean_theorem']['count']}"
    )
    if rep.get("_report_scratch"):
        # RT N16: the scratch report is removed at exit — name no path that will not
        # exist when the operator looks for it.
        print(
            "report: DRY RUN — not kept (scratch, removed at exit; pass --report "
            f"<path> to keep one); the committed record under {REPORT_DIR} is untouched"
        )
    elif "_report_md" in rep:
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
