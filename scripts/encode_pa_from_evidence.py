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
3. pinned_sha (architecture ruling, live-test seq 2299; closure ruling live-test seq 2394
   — FINAL; scope extended to every lake library + Agda by QBP#696; DERIVATION rewritten
   on the provers' own tools by QBP#700 / architecture §I4 conditions 1–3): the
   claim-source MANIFEST hash. S = the TRANSITIVE CLOSURE, over SAME-REPO imports, of
   {anchor proof_file} ∪ {SAME-REPO paths named by the claim's v2 evidence_refs},
   deduplicated — a claim's statement depends on the definitions its file imports (the
   Fano headline names `fanoTableF4`, defined in FanoOrientationF3.lean), so those files
   are part of what the evidence pinned. RULE (PR #698 root-cause analysis: a regex
   re-implementation of module resolution is a load-bearing float): each prover's import
   closure is derived from THAT PROVER'S OWN DEPENDENCY TOOL at the pinned commit, never
   from a parser we maintain. The tools run in a HERMETIC PIN CHECKOUT (`pin_worktree`):
   a temporary detached `git worktree` of the pin (one per run, removed in `run()`'s
   `finally` — atexit is the belt), with
   the running checkout's `proofs/.lake/packages` SYMLINKED in (never copied or fetched)
   and its gitignored `proofs/lake-manifest.json` COPIED in — refused if absent while the
   pin's lakefile has a `require`, and refused if the manifest does not resolve the revs
   the lakefile pins (QBP#700 G-L2: documented, not solved here; owner qbp-implementor).
   LEAN (`lean_workspace` / `lean_closure`; all `lake query --no-build --json`, so no
   `.olean` is ever produced — `lean --deps` and the `deps` facet need built oleans and
   are NOT used): the libraries come from `lake translate-config toml` (Lake's documented
   export of its elaborated configuration — Lake offers no facet that enumerates
   libraries); the same-repo module set M = ∪ over libraries of `@<pkg>/<lib>:modules`
   (each root and its transitive imports inside the library — exactly what `lake build`
   compiles); module → file from `+<M>:lean`; the closure from `+<M>:transImports` ∩ M.
   G-L1 ON EVERY MEMBER OF S (architecture condition 1): Lake drops an import it cannot
   resolve from `imports`/`transImports` SILENTLY (exit 0), so for each member
   `unknown = header.imports − imports − {m : <lake env lean --print-libdir>/<m>.olean
   exists}`; any unknown ⇒ refusal naming the importing file, the module and the anchor
   (`import Nonexistent.Mod` two hops down surfaces; `Init` / `Lean.*` do not). A `.lean`
   seed that is a module of no library ⇒ refusal (Lake would not build it either); a
   Lake-resolved import whose source is a same-repo file in no listed library (the
   translation is lossy by Lake's own documentation) ⇒ refusal. AGDA (`agda_closure`):
   from the member's library dir (the nearest ancestor holding an `*.agda-lib`, else its
   own dir — G-A1) `agda --only-scope-checking --dependency-graph=<dot> <file>`; module →
   file from Agda's own `Checking <M> (<path>).` stdout lines plus the root (= the CLI
   argument, the graph's unique in-degree-0 node); S = reachable(dot) ∩ files inside the
   worktree; the non-local namespaces (`Cubical`, `Agda`) are recorded in the report.
   ARCHITECTURE CONDITION 2: `Checking` lines are printed only for modules with no fresh
   interface, so the wrapper ASSERTS a clean interface state — no `_build/` and no
   `*.agdai` anywhere under the pinned `proofs/` — before the run and REFUSES otherwise
   (the temp worktree is fresh, so it holds; the assertion is what makes a stale interface
   fail closed instead of shrinking S), and removes the `_build/` it caused afterwards.
   Non-zero exit / no graph ⇒ refusal with Agda's stderr. COQ (`coq_closure`, forward-
   looking — no in-repo `.v` exists today; G-C1): `_CoqProject` at the pin is required
   (refusal otherwise); `coqdep -f _CoqProject`; coqdep has no strict mode, so ANY stderr
   line ⇒ refusal; closure by following each rule's `.vo` prerequisites to their own
   rule's `.v` source (a prerequisite with no rule ⇒ refusal). Cross-repo refs keep
   today's behaviour (never enter S). TOOL ABSENCE = REFUSAL, never a fallback
   (`require_tool`). Every tool runs under `tool_wrapper` (`run-bounded 8G 1800` when on
   PATH; $QBP_PROVER_TOOL_WRAPPER overrides). The closure's HANDLE — `proofs/lean-
   toolchain` at the pin, `lake --version` (in the pin's `proofs/`), `agda --version`,
   `coqc --version` or `not installed` — is recorded in the report (`toolchain_handle`).
   Library modules (Mathlib / Std / Lean core; the pinned agda/cubical; Coq's stdlib)
   never enter S: the tools place them outside the tree (under `proofs/.lake/` or
   outside the worktree). OUT-OF-TREE GUARD (architecture ruling live-test seq 2446): a
   path-valued `proof_file` or a same-repo evidence_ref path that is absolute, contains a
   `..` segment, or does not start with `proofs/` is a refusal naming the anchor and is
   NEVER a closure seed (`check_in_tree`); a `proof_file` that is not a path at all (the
   literature citations `PROOF-hurwitz` "Hurwitz 1898", `PROOF-born` "Hurwitz corollary")
   is `no_proof_file`, inert; a path-valued `proof_file` that does not exist at the pin is
   `stale_proof_file` (inert without evidence, refusal with it) and is listed in the
   report's `stale_proof_file` section (AC5). evidence_ref grammar (§I4 ruling on PR
   #695, live-test seq 2342; RT C1): `[<owner>/<repo>:]<path>@<commit>#<target>` — no
   prefix means THIS repo (QBP) and only such refs enter S; a prefixed (cross-repo, e.g.
   the notary's Coq port `JamesPagetButler/notary:proofs/FanoTableCrossProver.v@b4c92818#…`)
   ref MUST carry `@<commit>` — a 7–40 hex sha (RT N8: `@main` / `@HEAD` / a tag is a
   moving ref, not a pin ⇒ refusal) — is pinned by that commit plus `reproduce`, never
   enters S, and is reported with flag `cross_repo_evidence` (`parse_evidence_ref` /
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
   commit; a declared proof_file that does not exist at the pinned commit — or is not a
   path at all (a citation) — while evidence is being graded (pinned_sha must never be
   empty when grading evidence — architecture 3c).
   No evidence and no resolvable proof_file ⇒ pinned_sha "" (inert: nothing to be stale),
   report flag `no_proof_file`. The convention lives in ONE function (`pinned_sha_for`) so
   it can be swapped; S, the per-file blobs and the per-seed closure record (tool, modules,
   non-local namespaces) go in the report, not the ledger (`pinned_sha` has no ledger home
   at schema 0.3.5). S is computed over EVERY assistant of the merged record BEFORE the
   target filter (RT C4): the filter decides who reaches the engine, never what S is — a
   dropped same-repo companion must not shrink the manifest and false-flag the on-target
   survivor `stale` (notary computes `source_sha` over the record it emits, i.e. over all
   of them).
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
3c. KERNEL COLLAPSE (RT C7, issuecomment-5962978225; architecture ruling live-test seq
   2386; Gemini concurs issuecomment-5963015465): the vendored engine's `GradeClaim`
   counts clean ASSISTANTS, not distinct kernels — `[coq, coq]` (two Coq lemmas, or one
   Coq entry listed twice) with no lean4 would grade PA 2 from a single kernel. PA 2
   means "two independent kernels agree", so after the target filter the survivors are
   collapsed to the FIRST admissible assistant per prover kind (the `assistant` field);
   every later same-kind survivor is dropped with report flag
   `same_kernel_duplicate:<kind>` (`collapse_to_one_per_kernel`, ONE function). The
   collapse runs before the engine Claim is built and before the ledger array is planned,
   so neither ever sees the duplicate. Fano lean4 + coq is untouched (two kinds).
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
   SURVIVED the target filter AND the kernel collapse (§3c), ONLY when (a) at least one did (an empty array is never
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
   pinned_sha, engine pin, every per-anchor flag (engine + encoder), the EVIDENCE REPO
   IDENTITY (RT N2 on PR #697: `git -C <evidence_dir> rev-parse HEAD` + `remote get-url
   origin`; a directory that is not a git checkout is recorded as the explicit string
   `unknown (not a git checkout)`, never omitted — `evidence_repo_identity`; the checkout's
   own path — `--show-toplevel` — is the `<evidence-repo>` base of the record paths and is
   never written into the report, RT N7 on PR #703),
   and the `stale_proof_file` / `no_proof_file` anchor lists (seq 2446, AC5).

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
import posixpath
import re
import shlex
import shutil
import signal
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
# seq 2394 + QBP#696 (rewritten on QBP#700): the claim-source manifest closes over
# SAME-REPO imports, and the closure is DERIVED FROM EACH PROVER'S OWN DEPENDENCY TOOL
# at the pinned commit — Lake's facets, `agda --dependency-graph`, `coqdep` — never from
# a parser of ours (PR #698 root-cause analysis: a regex re-implementation of module
# resolution is a load-bearing float). See the module doc §3 and `pin_worktree`.
LEAN_SRC_ROOT = "proofs"
LAKEFILE = "proofs/lakefile.lean"
LAKEFILE_TOML = (
    "proofs/lakefile.toml"  # Lake accepts either; so does `pin_worktree` (RT N2)
)
LEAN_TOOLCHAIN_FILE = "proofs/lean-toolchain"
LAKE_MANIFEST = "proofs/lake-manifest.json"
LAKE_PACKAGES_DIR = "proofs/.lake/packages"
LEAN_EXT = ".lean"
AGDA_EXTS = (".agda", ".lagda.md", ".lagda")
AGDA_LIB_EXT = ".agda-lib"
COQ_EXT = ".v"
COQ_PROJECT = "_CoqProject"
# seq 2446: every closure seed (proof_file, same-repo evidence_ref path) must live under
# this tree; an absolute path, a `..` segment, or any other prefix is refused.
LOCAL_TREE_PREFIX = "proofs/"
# A proof_file is PATH-VALUED iff it looks like one: a separator or a proof-source
# extension. The two literature citations (`PROOF-hurwitz` "Hurwitz 1898", `PROOF-born`
# "Hurwitz corollary") are neither → `no_proof_file`, inert.
PATH_EXTS = (LEAN_EXT, COQ_EXT, *AGDA_EXTS)
# Every prover-tool invocation (lake, agda, coqdep) runs under this prefix: the env var
# (shell-split; "" = none) when set, else `run-bounded 8G 1800` when that wrapper is on
# PATH (the QBP#700 resource envelope: ≤ 8 G RAM, 30 min, per leg), else nothing (CI).
PROVER_TOOL_WRAPPER_ENV = "QBP_PROVER_TOOL_WRAPPER"
# Where the running checkout keeps the Lake dependency sources + the manifest that
# resolves them (gitignored, so no pinned commit carries them — G-L2). Defaults: the
# repo's own `proofs/.lake/packages` / `proofs/lake-manifest.json`, else the same paths
# in the repo's MAIN worktree (`git worktree list`). Never copied, never fetched.
LAKE_PACKAGES_ENV = "QBP_LAKE_PACKAGES_DIR"
LAKE_MANIFEST_ENV = "QBP_LAKE_MANIFEST"
# When set to "1", `require_tool` reports which tools are missing instead of refusing
# lazily — the test suite's unconditional gate (`QBP_REQUIRE_PROVER_TOOLS=1` in CI).
REQUIRE_PROVER_TOOLS_ENV = "QBP_REQUIRE_PROVER_TOOLS"
PROVER_TOOLS = ("lake", "agda", "coqdep")
# G-L2 (QBP#700): the ONLY thing read from the lakefile's text — the git revisions its
# `require`s pin — so the run REFUSES, before Lake ever runs, if the manifest handed to
# Lake does not already resolve them (Lake would otherwise fetch: network, and a write
# into the shared packages checkout). Not a parser: a `require` is only ever recognised
# as "present", and a rev only ever as "must be in the manifest".
LAKE_REQUIRE_REV_RE = re.compile(r'@\s*"([0-9a-f]{7,40})"')
# one `require` statement of a `lakefile.lean`: the package name (`«n»`, `"n"` or bare),
# then its text up to the next column-0 declaration (RT N3: the manifest check is per NAMED
# package — the pinned rev must be THAT package's rev, not any package's)
LAKE_REQUIRE_STMT_RE = re.compile(
    r'^[ \t]*require\s+(?:«([^»]+)»|"([^"]+)"|(\S+))', re.M
)
LAKE_DECL_START_RE = re.compile(r"^(?:[A-Za-z_]|@\[)", re.M)
HEX_REV_RE = re.compile(r"^[0-9a-f]{7,40}$")
# Agda's own module → file record: one `Checking <M> (<path>).` stdout line per module it
# type-checks from source (G-A1: printed only when no fresh interface exists — hence the
# clean-interface assertion in `agda_closure`, architecture condition 2).
AGDA_CHECKING_RE = re.compile(r"^\s*Checking (\S+) \((.+)\)\.?\s*$")
# Graphviz as `agda --dependency-graph` writes it: `mN[label="Mod.Name"];` / `mA -> mB;`.
DOT_NODE_RE = re.compile(r'^\s*(\w+)\s*\[label="([^"]*)"\]', re.M)
DOT_EDGE_RE = re.compile(r"^\s*(\w+)\s*->\s*(\w+)\s*;", re.M)

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


def blob_text(repo: Path, blob: str) -> str:
    """Content of git blob `blob` (`git cat-file blob`) decoded as UTF-8 — the file AT the
    pinned commit, never the working tree."""
    p = subprocess.run(
        ["git", "cat-file", "blob", blob],
        cwd=str(repo),
        capture_output=True,
        check=False,
    )
    if p.returncode != 0:
        raise Refusal(
            f"git cat-file blob {blob} failed: {p.stderr.decode('utf-8', 'replace')}"
        )
    return p.stdout.decode("utf-8", errors="replace")


# ---------------------------------------------------------------------------------------
# prover-tool closure (QBP#700 → QBP#696; architecture §I4 conditions 1–3)
# ---------------------------------------------------------------------------------------
# RULE: each prover's import closure is derived from that prover's own dependency tool at
# the pinned commit, never from a parser we maintain. Lean: Lake's facets (`modules`,
# `lean`, `imports`, `transImports`, `header`) under `lake query --no-build`; Agda:
# `agda --only-scope-checking --dependency-graph`; Coq: `coqdep -f _CoqProject`. The tools
# run inside a hermetic, temporary `git worktree` of the pinned commit (`pin_worktree`),
# so what they see IS the pin — never the working tree. Tool absence is a refusal, never
# a fallback. The toolchain versions are the closure's handle (`toolchain_handle`).
def tool_wrapper() -> List[str]:
    """The argv prefix every prover tool runs under: $QBP_PROVER_TOOL_WRAPPER shell-split
    when set ("" disables), else `run-bounded 8G 1800` when on PATH, else nothing."""
    env = os.environ.get(PROVER_TOOL_WRAPPER_ENV)
    if env is not None:
        return shlex.split(env)
    rb = shutil.which("run-bounded")
    return [rb, "8G", "1800"] if rb else []


def require_tool(name: str, why: str) -> str:
    """Absolute path of prover tool `name`, or a Refusal naming what needed it. A missing
    tool is never a fallback to some other way of computing the closure."""
    path = shutil.which(name)
    if path is None:
        raise Refusal(
            f"prover tool {name!r} is not installed (needed to derive {why}); the closure "
            "is derived from the prover's own dependency tool or not at all (QBP#700)"
        )
    return path


def missing_prover_tools() -> List[str]:
    """The prover tools absent from PATH (the test suite's CI gate reads this)."""
    return [t for t in PROVER_TOOLS if shutil.which(t) is None]


def signal_exit(rc: int) -> Optional[str]:
    """`SIGSEGV (rc 139)` when `rc` is a death-by-signal exit code — negative from
    `subprocess` (the tool process itself was killed) or 128+N (the tool's wrapper —
    run-bounded / `timeout` / a shell — reporting its child's signal); None for an
    ordinary exit, including rc 128 and a 128+N that names no signal (RT N8 on PR #703).
    """
    n = -rc if rc < 0 else rc - 128 if rc > 128 else 0
    if n <= 0:
        return None
    try:
        name = signal.Signals(n).name
    except ValueError:
        return None
    return f"{name} (rc {128 + n})"


def run_tool(argv: List[str], cwd: Path) -> subprocess.CompletedProcess:
    """Run a prover tool (under `tool_wrapper`) with its stdout/stderr captured. A tool
    that exits BY SIGNAL (`signal_exit`) is a refusal naming the tool and the signal — an
    operator reads a binary crash or an external kill (run-bounded's memory cap is
    SIGKILL), not a logic error of the tool or the encoder; fail-closed, never retried
    (RT N8 on PR #703). An ordinary non-zero exit is the caller's to interpret."""
    p = subprocess.run(
        [*tool_wrapper(), *argv],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )
    sig = signal_exit(p.returncode)
    if sig is not None:
        raise Refusal(
            f"prover tool {Path(argv[0]).name!r} exited by signal {sig} — a binary crash "
            "or an external kill (run-bounded's memory cap is SIGKILL), not a logic "
            f"error of the tool or the encoder; argv `{shlex.join(argv)}` in {cwd}; "
            f"stderr: {p.stderr.strip()[-2000:] or '(empty)'}"
        )
    return p


def tool_version(name: str, cwd: Path) -> str:
    """First line of `<name> --version` run in `cwd` (so elan picks the pin's toolchain
    for `lake`), or the explicit string `not installed`."""
    path = shutil.which(name)
    if path is None:
        return "not installed"
    p = run_tool([path, "--version"], cwd)
    line = (p.stdout or p.stderr).strip().split("\n", 1)[0].strip()
    return line or f"{name} --version printed nothing (rc {p.returncode})"


# ---- hermetic pin checkout --------------------------------------------------------------
_PIN_WORKTREES: Dict[Tuple[str, str], Path] = {}
_PIN_SCRATCH: List[Tuple[Path, Path, Path]] = []  # (repo, scratch parent, worktree)
_PIN_ATEXIT_REGISTERED = False  # the belt is registered once per process (RT C2)


def _main_worktree(repo: Path) -> Optional[Path]:
    p = _git(repo, "worktree", "list", "--porcelain", check=False)
    for ln in p.stdout.split("\n"):
        if ln.startswith("worktree "):
            return Path(ln[len("worktree ") :])
    return None


def lake_dependency_sources(repo: Path) -> Tuple[Optional[Path], Optional[Path]]:
    """(packages dir, manifest) of the running checkout that a pin worktree borrows: the
    env overrides when set, else `repo`'s own, else the repo's main worktree's. None when
    absent (the caller decides whether the pin needs them)."""
    cands_pkgs: List[Path] = []
    cands_man: List[Path] = []
    if os.environ.get(LAKE_PACKAGES_ENV):
        cands_pkgs.append(Path(os.environ[LAKE_PACKAGES_ENV]))
    if os.environ.get(LAKE_MANIFEST_ENV):
        cands_man.append(Path(os.environ[LAKE_MANIFEST_ENV]))
    roots = [repo]
    main = _main_worktree(repo)
    if main is not None and main.resolve() != repo.resolve():
        roots.append(main)
    for r in roots:
        cands_pkgs.append(r / LAKE_PACKAGES_DIR)
        cands_man.append(r / LAKE_MANIFEST)
    pkgs = next((p for p in cands_pkgs if p.is_dir()), None)
    man = next((p for p in cands_man if p.is_file()), None)
    return pkgs, man


def lake_requires(
    repo: Path, commit: str
) -> Optional[Tuple[str, List[Tuple[str, Optional[str]]]]]:
    """(lakefile path, [(package, pinned hex rev or None)]) for the Lake configuration at
    the pin — `proofs/lakefile.lean` (each `require` statement: its name, and the
    `@ "<hex>"` inside that statement) or, failing that, `proofs/lakefile.toml` (the
    `[[require]]` tables via `read_lake_toml`: `name`, `rev`) — or None when the pin has
    neither (RT N2: `pin_worktree` lends dependencies to a TOML pin too, and refuses on
    the same conditions, so Lake can never be left to fetch). A rev that is not a hex sha
    (a tag / branch — N1, qbp-implementor's G-L2 PR) is recorded as None, as before."""
    blob = blob_sha(repo, commit, LAKEFILE)
    if blob is not None:
        text = blob_text(repo, blob)
        out: List[Tuple[str, Optional[str]]] = []
        starts = list(LAKE_REQUIRE_STMT_RE.finditer(text))
        for i, m in enumerate(starts):
            name = next(g for g in m.groups() if g is not None)
            end = starts[i + 1].start() if i + 1 < len(starts) else len(text)
            nxt = LAKE_DECL_START_RE.search(text, m.end(), end)
            chunk = text[m.end() : nxt.start() if nxt else end]
            revs = LAKE_REQUIRE_REV_RE.findall(chunk)
            out.append((name, revs[0] if revs else None))
        return LAKEFILE, out
    blob = blob_sha(repo, commit, LAKEFILE_TOML)
    if blob is None:
        return None
    cfg = read_lake_toml(blob_text(repo, blob))
    out = []
    for t in cfg.get("require", []) or []:
        name = t.get("name") if isinstance(t, dict) else None
        if not isinstance(name, str) or not name:
            raise Refusal(
                f"{LAKEFILE_TOML} at pinned master {commit[:12]} has a `[[require]]` "
                f"without a `name` ({t!r}); the dependency cannot be checked against the "
                "manifest — refusing (QBP#700 G-L2)"
            )
        rev = t.get("rev")
        out.append(
            (name, rev if isinstance(rev, str) and HEX_REV_RE.match(rev) else None)
        )
    return LAKEFILE_TOML, out


def _check_manifest_resolves_pin(
    lakefile: str,
    requires: List[Tuple[str, Optional[str]]],
    manifest_path: Path,
    commit: str,
) -> None:
    """G-L2: every package the pin's lakefile requires at an `@ "<rev>"` must be resolved
    BY NAME in the manifest Lake is handed to a `rev` / `inputRev` matching that rev (RT
    N3: another package at the wanted rev proves nothing); otherwise Lake would resolve
    over the network and the result would not be the pin's. Documented, not solved here
    (owner qbp-implementor)."""
    try:
        man = json.loads(manifest_path.read_text(encoding="utf-8"))
        by_name: Dict[str, List[str]] = {}
        for pkg in man.get("packages", []):
            if isinstance(pkg, dict) and isinstance(pkg.get("name"), str):
                by_name[pkg["name"]] = [
                    pkg[k] for k in ("rev", "inputRev") if isinstance(pkg.get(k), str)
                ]
    except (OSError, ValueError, AttributeError) as e:
        raise Refusal(f"{manifest_path} is not a readable Lake manifest: {e}")
    why = (
        f"the manifest {manifest_path} (copied in, since {LAKE_MANIFEST} is gitignored — "
        "QBP#700 G-L2)"
    )
    tail = (
        "; Lake would fetch over the network and the closure would not be the pin's — "
        "refusing (track the manifest, or run against a checkout whose packages match "
        "the pin)"
    )
    for name, want in requires:
        if want is None:
            continue
        if name not in by_name:
            raise Refusal(
                f"{lakefile} at pinned master {commit[:12]} requires package {name!r} at "
                f"rev {want!r} but {why} lists no package named {name!r}{tail}"
            )
        have = by_name[name]
        if not any(r.startswith(want) or want.startswith(r) for r in have):
            raise Refusal(
                f"{lakefile} at pinned master {commit[:12]} requires package {name!r} at "
                f"rev {want!r} but {why} resolves {name!r} to "
                f"{', '.join(repr(r) for r in have) or 'no rev'}, not to it{tail}"
            )


def pin_worktree(repo: Path, commit: str) -> Path:
    """A temporary, detached `git worktree` of `commit` (one per (repo, pin) per process,
    removed by `run()`'s `finally` — `cleanup_pin_worktrees`; atexit is the belt for
    callers that bypass `run()`), with the running checkout's Lake
    dependency sources SYMLINKED in (`proofs/.lake/packages`, 7 GB of Mathlib — never
    copied, never fetched) and its `proofs/lake-manifest.json` COPIED in (gitignored, so
    the pin carries none; G-L2 verified by `_check_manifest_resolves_pin`, per named
    package). A pin whose lakefile (`.lean` or `.toml` — RT N2) has a `require` while
    the running checkout has neither ⇒ refusal (Lake would fetch). The prover tools run
    here, so every path they report is the pin's."""
    key = (str(repo), commit)
    if key in _PIN_WORKTREES:
        return _PIN_WORKTREES[key]
    parent = Path(tempfile.mkdtemp(prefix="qbp696-pin-"))
    wt = parent / "wt"
    p = _git(repo, "worktree", "add", "--detach", str(wt), commit, check=False)
    if p.returncode != 0:
        shutil.rmtree(parent, ignore_errors=True)
        raise Refusal(
            f"git worktree add of pinned master {commit[:12]} failed: {p.stderr.strip()}"
        )
    global _PIN_ATEXIT_REGISTERED
    if not _PIN_ATEXIT_REGISTERED:
        # the belt: `run()` removes its worktrees in `finally`; atexit covers a caller
        # that uses `pin_worktree` directly and never cleans up
        atexit.register(cleanup_pin_worktrees)
        _PIN_ATEXIT_REGISTERED = True
    _PIN_SCRATCH.append((repo, parent, wt))
    reqs = lake_requires(repo, commit)
    if reqs is not None:
        lakefile, requires = reqs
        pkgs, man = lake_dependency_sources(repo)
        if requires and (pkgs is None or man is None):
            raise Refusal(
                f"{lakefile} at pinned master {commit[:12]} has a `require`, but the "
                f"running checkout offers {'no ' + LAKE_PACKAGES_DIR if pkgs is None else ''}"
                f"{' and ' if pkgs is None and man is None else ''}"
                f"{'no ' + LAKE_MANIFEST if man is None else ''} to lend the pin "
                f"(${LAKE_PACKAGES_ENV} / ${LAKE_MANIFEST_ENV} override the lookup); Lake "
                "would fetch the dependencies over the network — refusing (QBP#700 G-L2)"
            )
        if pkgs is not None:
            dest = wt / LAKE_PACKAGES_DIR
            dest.parent.mkdir(parents=True, exist_ok=True)
            if not dest.exists():
                dest.symlink_to(pkgs.resolve(), target_is_directory=True)
        if man is not None:
            _check_manifest_resolves_pin(lakefile, requires, man, commit)
            shutil.copyfile(man, wt / LAKE_MANIFEST)
    _PIN_WORKTREES[key] = wt
    return wt


def cleanup_pin_worktrees() -> List[Path]:
    """Remove every pin worktree this process made (`git worktree remove --force`, then
    the scratch parent; `git worktree prune` if the repo is gone). Returns them."""
    gone: List[Path] = []
    while _PIN_SCRATCH:
        repo, parent, wt = _PIN_SCRATCH.pop()
        _git(repo, "worktree", "remove", "--force", str(wt), check=False)
        shutil.rmtree(parent, ignore_errors=True)
        _git(repo, "worktree", "prune", check=False)
        gone.append(wt)
    _PIN_WORKTREES.clear()
    _LEAN_WORKSPACES.clear()
    _AGDA_CLOSURES.clear()
    return gone


def _inside(wt: Path, path: str) -> Optional[str]:
    """`path` (as a tool printed it) relative to the worktree, posix, or None when it
    lies outside the worktree or under the borrowed `proofs/.lake/` (a dependency)."""
    rel = os.path.relpath(os.path.abspath(path), str(wt))
    rel = rel.replace(os.sep, "/")
    if rel.startswith("..") or rel.startswith(f"{LEAN_SRC_ROOT}/.lake/"):
        return None
    return rel


# ---- Lean: Lake's own facets -----------------------------------------------------------
class LeanWorkspace:
    """Lake's answers about the pinned Lean project, memoised per (repo, pin):
    `libs` (from `lake translate-config toml`, Lake's documented export of the elaborated
    configuration — there is no facet that enumerates libraries), `modules` (module →
    library; the union of every library's `:modules` facet = each root and its
    transitive imports within the library — exactly what `lake build` compiles),
    `mod2path` / `path2mod` (the `lean` facet), `imports` / `trans` (the `imports` /
    `transImports` facets, Lake-resolved), `header` (the raw header imports) and
    `unresolved` (G-L1 per module: header − imports − toolchain oleans)."""

    def __init__(self, wt: Path) -> None:
        self.wt = wt
        self.package = ""
        self.libs: List[str] = []
        self.modules: "OrderedDict[str, str]" = OrderedDict()
        self.mod2path: Dict[str, str] = {}
        self.path2mod: Dict[str, str] = {}
        self.imports: Dict[str, List[str]] = {}
        self.trans: Dict[str, List[str]] = {}
        self.header: Dict[str, List[str]] = {}
        self.unresolved: Dict[str, List[str]] = {}
        self.libdir = Path()


_LEAN_WORKSPACES: Dict[Tuple[str, str], LeanWorkspace] = {}


def lake_query(proofs: Path, targets: List[str]) -> List[Any]:
    """`lake query --no-build --json <targets>` in `proofs`: one JSON value per target, in
    order. Non-zero exit (unknown module / facet, a target that would need a build) or
    a non-JSON stdout line ⇒ refusal with Lake's stderr. `--no-build` is what keeps
    this a header-level derivation: no `.olean` is ever produced (the `deps` facet and
    `lean --deps` need built oleans and are not used)."""
    lake = require_tool("lake", "the Lean import closure")
    p = run_tool([lake, "query", "--no-build", "--json", *targets], proofs)
    if p.returncode != 0:
        raise Refusal(
            f"`lake query --no-build --json` failed (rc {p.returncode}) in {proofs} on "
            f"{len(targets)} target(s) [{targets[0]}{', …' if len(targets) > 1 else ''}]: "
            f"{p.stderr.strip()[-1500:]}"
        )
    out: List[Any] = []
    for ln in p.stdout.split("\n"):
        if not ln.strip():
            continue
        try:
            out.append(json.loads(ln))
        except ValueError:
            raise Refusal(f"`lake query --json` printed a non-JSON line: {ln[:200]!r}")
    if len(out) != len(targets):
        raise Refusal(
            f"`lake query --json` returned {len(out)} value(s) for {len(targets)} "
            "target(s); the facet results cannot be paired with their modules"
        )
    return out


def read_lake_toml(text: str) -> Dict[str, Any]:
    """The `lakefile.toml` that `lake translate-config toml` emits, as a dict with the
    top-level keys and `[[table]]` arrays. `tomllib` (3.11+) or `tomli` when available;
    else a reader of exactly the shape Lake's own emitter writes — one `key = value`
    per line, values a `"string"`, `["array", "of", "strings"]`, `true`/`false` or a
    number — refusing on any other line or array element (Lake's output is
    machine-written, so an unrecognised shape means the emitter changed, not that a
    comment slipped in; RT N4: a non-string element is refused, never dropped)."""
    try:  # pragma: no cover — depends on the interpreter
        import tomllib  # type: ignore

        return tomllib.loads(text)
    except ImportError:
        pass
    try:  # pragma: no cover
        import tomli  # type: ignore

        return tomli.loads(text)
    except ImportError:
        pass
    doc: Dict[str, Any] = {}
    cur: Dict[str, Any] = doc
    for raw in text.split("\n"):
        ln = raw.strip()
        if not ln:
            continue
        m = re.match(r"^\[\[([A-Za-z_][\w-]*)\]\]$", ln)
        if m:
            cur = {}
            doc.setdefault(m.group(1), []).append(cur)
            continue
        m = re.match(r"^([A-Za-z_][\w-]*)\s*=\s*(.*)$", ln)
        if not m:
            raise Refusal(
                f"unrecognised line in Lake's translate-config output: {ln!r}"
            )
        key, val = m.group(1), m.group(2).strip()
        if val in ("true", "false"):
            cur[key] = val == "true"
        elif re.fullmatch(r'"(?:[^"\\]|\\.)*"', val):
            cur[key] = json.loads(val)
        elif val.startswith("[") and val.endswith("]"):
            # exactly a list of strings (optional trailing comma); any other element —
            # a bare word, a number, a nested table — is refused, never dropped (RT N4)
            if not re.fullmatch(
                r'\[\s*(?:"(?:[^"\\]|\\.)*"\s*(?:,\s*"(?:[^"\\]|\\.)*"\s*)*,?\s*)?\]',
                val,
            ):
                raise Refusal(
                    "non-string array element in Lake's translate-config output: "
                    f"{ln!r}"
                )
            items = re.findall(r'"(?:[^"\\]|\\.)*"', val)
            cur[key] = [json.loads(i) for i in items]
        elif re.fullmatch(r"-?\d+", val):
            cur[key] = int(val)
        else:
            raise Refusal(
                f"unrecognised value in Lake's translate-config output: {ln!r}"
            )
    return doc


def lean_workspace(repo: Path, commit: str) -> LeanWorkspace:
    """Everything Lake knows about the pinned project, in four batched `lake query`
    calls (plus `translate-config` and `lake env lean --print-libdir`); memoised per
    (repo, pin). Fail-closed guards: no library in the configuration ⇒ refusal; a
    Lake-resolved import whose source is a same-repo file in no listed library (the
    translation is lossy by Lake's own documentation) ⇒ refusal; G-L1 per module."""
    key = (str(repo), commit)
    if key in _LEAN_WORKSPACES:
        return _LEAN_WORKSPACES[key]
    wt = pin_worktree(repo, commit)
    proofs = wt / LEAN_SRC_ROOT
    if (
        not (proofs / "lakefile.lean").is_file()
        and not (proofs / "lakefile.toml").is_file()
    ):
        raise Refusal(
            f"no Lake configuration ({LAKEFILE} / lakefile.toml) at pinned master "
            f"{commit[:12]}; the Lean module set is Lake's to derive and cannot be guessed"
        )
    lake = require_tool("lake", "the Lean import closure")
    ws = LeanWorkspace(wt)
    # 1. the libraries, from Lake's own export of its elaborated configuration
    fd, toml_out = tempfile.mkstemp(prefix="qbp696-lakefile-", suffix=".toml")
    os.close(fd)
    os.unlink(toml_out)  # translate-config refuses to overwrite
    try:
        p = run_tool([lake, "translate-config", "toml", toml_out], proofs)
        if p.returncode != 0 or not os.path.isfile(toml_out):
            raise Refusal(
                f"`lake translate-config toml` failed (rc {p.returncode}) at pinned "
                f"master {commit[:12]}: {p.stderr.strip()[-1500:]}"
            )
        cfg = read_lake_toml(Path(toml_out).read_text(encoding="utf-8"))
    finally:
        if os.path.exists(toml_out):
            os.unlink(toml_out)
    ws.package = str(cfg.get("name", ""))
    ws.libs = [str(t["name"]) for t in cfg.get("lean_lib", []) if "name" in t]
    if not ws.package or not ws.libs:
        raise Refusal(
            f"Lake's configuration at pinned master {commit[:12]} exports no "
            f"`lean_lib` (package {ws.package!r}); nothing is same-repo Lean and no "
            "`.lean` seed can be a module — refusing rather than treating every import "
            "as external"
        )
    # 2. the module set: each library's `modules` facet (roots + their transitive
    #    imports inside the library — Lake's notion of what the library contains)
    for lib, mods in zip(
        ws.libs, lake_query(proofs, [f"@{ws.package}/{lib}:modules" for lib in ws.libs])
    ):
        for m in mods:
            ws.modules.setdefault(str(m), lib)
    mods_all = list(ws.modules)
    if not mods_all:
        raise Refusal(
            f"Lake lists no module in any library at pinned master {commit[:12]}"
        )
    # 3. module → source path (the `lean` facet), relativised to the worktree
    for m, path in zip(mods_all, lake_query(proofs, [f"+{m}:lean" for m in mods_all])):
        rel = _inside(wt, str(path))
        if rel is None:
            raise Refusal(
                f"Lake places module {m!r} at {path!r}, outside the pinned tree"
            )
        ws.mod2path[m] = rel
        ws.path2mod.setdefault(rel, m)
    # 4. imports / transImports / header for every module, one batched call
    facets = ("imports", "transImports", "header")
    res = lake_query(proofs, [f"+{m}:{f}" for m in mods_all for f in facets])
    for i, m in enumerate(mods_all):
        imp, trans, header = res[3 * i], res[3 * i + 1], res[3 * i + 2]
        ws.imports[m] = [str(x) for x in imp]
        ws.trans[m] = [str(x) for x in trans]
        ws.header[m] = [str(d["module"]) for d in header.get("imports", [])]
    # 5. the toolchain's own modules (Init, Lean.*, Std.*): `lake env lean --print-libdir`
    p = run_tool([lake, "env", "lean", "--print-libdir"], proofs)
    if p.returncode != 0 or not p.stdout.strip():
        raise Refusal(
            f"`lake env lean --print-libdir` failed (rc {p.returncode}): "
            f"{p.stderr.strip()[-800:]}"
        )
    ws.libdir = Path(p.stdout.strip().split("\n")[-1])

    def is_toolchain(mod: str) -> bool:
        return (ws.libdir / (mod.replace(".", "/") + ".olean")).is_file()

    # 6. G-L1 per module: a header import Lake silently dropped from `imports` and that
    #    is no toolchain module is UNRESOLVED (recorded here; refused per member of S)
    for m in mods_all:
        resolved = set(ws.imports[m])
        ws.unresolved[m] = sorted(
            {h for h in ws.header[m] if h not in resolved and not is_toolchain(h)}
        )
    # 7. lossy-translation guard: every Lake-resolved import that is not in a listed
    #    library must come from a dependency (under proofs/.lake/), never from a
    #    same-repo file a dropped library would own
    external = sorted(
        {x for m in mods_all for x in ws.imports[m] if x not in ws.modules}
    )
    if external:
        for x, path in zip(
            external, lake_query(proofs, [f"+{x}:lean" for x in external])
        ):
            rel = _inside(wt, str(path))
            if rel is not None:
                raise Refusal(
                    f"Lake resolves import {x!r} to the same-repo file {rel!r}, which "
                    f"belongs to none of the libraries its configuration export lists "
                    f"({', '.join(ws.libs)}) at pinned master {commit[:12]}; a same-repo "
                    "module the closure cannot place would silently leave S — refusing"
                )
    _LEAN_WORKSPACES[key] = ws
    return ws


def lean_closure(
    repo: Path, commit: str, seed: str, context: str = ""
) -> Tuple[List[str], Dict[str, Any]]:
    """The same-repo files the Lean module at `seed` transitively imports (seed included),
    from Lake: S = {m} ∪ (transImports(m) ∩ modules). A seed that is a module of no
    library ⇒ refusal (Lake would not build it either). G-L1 (architecture condition 1)
    on EVERY member of S: any header import Lake dropped silently that is no toolchain
    module ⇒ refusal naming the importing file, the module and the anchor."""
    ws = lean_workspace(repo, commit)
    m = ws.path2mod.get(seed)
    if m is None:
        raise Refusal(
            f"{seed!r} is a module of no Lake library at pinned master {commit[:12]} "
            f"(libraries {', '.join(ws.libs)}: each root and its transitive imports — a "
            "file no root reaches is not compiled by `lake build` either){context}; the "
            "claim-source closure is Lake's to derive and this seed is outside it"
        )
    members = [m] + [t for t in ws.trans[m] if t in ws.modules and t != m]
    for s in members:
        if ws.unresolved[s]:
            raise Refusal(
                f"{ws.mod2path[s]!r} (module {s!r}) imports "
                f"{', '.join(repr(u) for u in ws.unresolved[s])}, which Lake resolves to "
                f"no module at pinned master {commit[:12]} and which is no toolchain "
                f"module (no `{ws.libdir}/<module>.olean`) — Lake drops an unresolved "
                "import from `imports`/`transImports` silently (QBP#700 G-L1), so the "
                f"claim-source manifest is not computed{context}"
            )
    files = sorted(ws.mod2path[s] for s in members)
    detail = OrderedDict(
        [
            ("tool", "lake"),
            ("seed_module", m),
            ("modules", members),
            (
                "nonlocal_namespaces",
                sorted(
                    {t.split(".", 1)[0] for t in ws.trans[m] if t not in ws.modules}
                ),
            ),
        ]
    )
    return files, detail


# ---- Agda: `agda --dependency-graph` -----------------------------------------------------
_AGDA_CLOSURES: Dict[Tuple[str, str, str], Tuple[List[str], Dict[str, Any]]] = {}


def agda_library_dir(wt: Path, file: Path) -> Path:
    """The directory Agda is run from for `file`: the nearest ancestor (inside the
    pinned tree) holding an `*.agda-lib`, else the file's own directory (Agda then roots
    the project at the cwd — G-A1)."""
    d = file.parent
    stop = wt.resolve()
    while True:
        if any(p.suffix == AGDA_LIB_EXT for p in d.iterdir() if p.is_file()):
            return d
        if d.resolve() == stop or d.parent == d:
            return file.parent
        d = d.parent


def _agda_interface_state(wt: Path) -> List[Path]:
    """Every `_build/` directory and `*.agdai` file under the pinned `proofs/` tree."""
    root = wt / LEAN_SRC_ROOT
    if not root.is_dir():
        return []
    found: List[Path] = []
    for p in root.rglob("*"):
        if (p.is_dir() and p.name == "_build") or (
            p.is_file() and p.suffix == ".agdai"
        ):
            if f"/{LEAN_SRC_ROOT}/.lake/" in p.as_posix():
                continue
            found.append(p)
    return found


def agda_closure(
    repo: Path, commit: str, seed: str, context: str = ""
) -> Tuple[List[str], Dict[str, Any]]:
    """The same-repo files the Agda module at `seed` transitively imports (seed
    included), from Agda: `agda --only-scope-checking --dependency-graph=<dot> <file>`
    run from the member's library dir in the pin worktree; module → file from Agda's own
    `Checking <M> (<path>).` lines (+ the root = the CLI argument); S = reachable(dot) ∩
    files inside the worktree. Architecture condition 2 (G-A1): the `Checking` lines are
    printed only for modules without a fresh interface, so the wrapper ASSERTS a clean
    interface state — no `_build/` and no `*.agdai` anywhere under the pinned `proofs/`
    — before the run and refuses otherwise (the temp worktree is fresh, so this holds;
    the assertion is what makes a stale interface fail closed instead of shrinking S),
    and removes the `_build/` it caused afterwards so the next seed's assertion is real.
    Non-zero exit or no graph written ⇒ refusal carrying Agda's stderr."""
    key = (str(repo), commit, seed)
    if key in _AGDA_CLOSURES:
        return _AGDA_CLOSURES[key]
    agda = require_tool("agda", "the Agda import closure")
    wt = pin_worktree(repo, commit)
    file = wt / seed
    libdir = agda_library_dir(wt, file)
    stale = _agda_interface_state(wt)
    if stale:
        names = ", ".join(str(p.relative_to(wt)) for p in stale[:6])
        raise Refusal(
            f"Agda interface state is not clean at pinned master {commit[:12]}: {names}"
            f"{' …' if len(stale) > 6 else ''} — Agda prints its module → file record "
            "(`Checking M (path)`) only for modules it type-checks from source, so a "
            "stale interface would silently shrink S (QBP#700 G-A1; architecture "
            f"condition 2){context}; the closure is derived in a clean worktree only"
        )
    fd, dot_path = tempfile.mkstemp(prefix="qbp696-agda-", suffix=".dot")
    os.close(fd)
    os.unlink(dot_path)
    try:
        p = run_tool(
            [
                agda,
                "--only-scope-checking",
                f"--dependency-graph={dot_path}",
                str(file.relative_to(libdir)),
            ],
            libdir,
        )
        dot = (
            Path(dot_path).read_text(encoding="utf-8")
            if os.path.isfile(dot_path)
            else ""
        )
    finally:
        if os.path.exists(dot_path):
            os.unlink(dot_path)
        for made in _agda_interface_state(wt):
            if made.is_dir():
                shutil.rmtree(made, ignore_errors=True)
            else:
                made.unlink(missing_ok=True)
    if p.returncode != 0 or not dot:
        raise Refusal(
            f"`agda --only-scope-checking --dependency-graph` on {seed!r} failed (rc "
            f"{p.returncode}{', no graph written' if not dot else ''}) at pinned master "
            f"{commit[:12]}{context}: {(p.stderr or p.stdout).strip()[-1500:]}"
        )
    label = dict(DOT_NODE_RE.findall(dot))
    edges = DOT_EDGE_RE.findall(dot)
    adj: Dict[str, List[str]] = {}
    indeg: Dict[str, int] = {n: 0 for n in label}
    for a, b in edges:
        adj.setdefault(label[a], []).append(label[b])
        indeg[b] = indeg.get(b, 0) + 1
    roots = [label[n] for n, d in indeg.items() if d == 0]
    if len(roots) != 1:
        raise Refusal(
            f"Agda's dependency graph for {seed!r} has {len(roots)} root module(s) "
            f"({', '.join(roots[:5])}); expected exactly the CLI module{context}"
        )
    root = roots[0]
    mod2path: Dict[str, str] = {}
    for ln in p.stdout.split("\n"):
        mt = AGDA_CHECKING_RE.match(ln)
        if mt:
            path = mt.group(2)
            if not os.path.isabs(path):
                path = str(libdir / path)
            mod2path.setdefault(mt.group(1), path)
    mod2path[root] = str(file)
    seen: List[str] = []
    stack = [root]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.append(m)
        stack.extend(adj.get(m, []))
    local: Dict[str, str] = {}
    for m, path in mod2path.items():
        rel = _inside(wt, path)
        if rel is not None:
            local[m] = rel
    files = sorted({local[m] for m in seen if m in local})
    detail = OrderedDict(
        [
            ("tool", "agda"),
            ("library_dir", libdir.relative_to(wt).as_posix()),
            ("seed_module", root),
            ("modules", [m for m in seen if m in local]),
            ("reachable", len(seen)),
            (
                "nonlocal_namespaces",
                sorted({m.split(".", 1)[0] for m in seen if m not in local}),
            ),
        ]
    )
    _AGDA_CLOSURES[key] = (files, detail)
    return files, detail


# ---- Coq: `coqdep -f _CoqProject` (forward-looking, G-C1) ---------------------------------
def coq_closure(
    repo: Path, commit: str, seed: str, context: str = ""
) -> Tuple[List[str], Dict[str, Any]]:
    """The same-repo files the Coq module at `seed` transitively requires (seed
    included), from `coqdep -f _CoqProject` run in the nearest ancestor directory holding
    a `_CoqProject` at the pin (none ⇒ refusal: the logical paths are the project's to
    declare). coqdep has no strict mode (G-C1): ANY stderr line ⇒ refusal. Closure by
    following each make rule's `.vo` prerequisites to their own rule's `.v` source; a
    prerequisite with no rule (a file outside the project listing) ⇒ refusal. Cross-repo
    Coq refs (the notary's) never reach here — they never enter S."""
    coqdep = require_tool("coqdep", "the Coq import closure")
    wt = pin_worktree(repo, commit)
    file = wt / seed
    d = file.parent
    proj: Optional[Path] = None
    while True:
        if (d / COQ_PROJECT).is_file():
            proj = d
            break
        if d.resolve() == wt.resolve() or d.parent == d:
            break
        d = d.parent
    if proj is None:
        raise Refusal(
            f"no {COQ_PROJECT} above {seed!r} at pinned master {commit[:12]}{context}; "
            "Coq module resolution (`-Q`/`-R` logical paths) is the project's to declare "
            "and coqdep needs it — refusing"
        )
    p = run_tool([coqdep, "-f", COQ_PROJECT], proj)
    if p.returncode != 0 or p.stderr.strip():
        raise Refusal(
            f"`coqdep -f {COQ_PROJECT}` in {proj.relative_to(wt).as_posix()!r} at pinned "
            f"master {commit[:12]} {'failed (rc ' + str(p.returncode) + ')' if p.returncode else 'wrote to stderr'}"
            f" — coqdep has no strict mode, so any diagnostic is a refusal (QBP#700 "
            f"G-C1){context}: {p.stderr.strip()[-1500:]}"
        )
    rules: Dict[str, Tuple[str, List[str]]] = {}  # X.vo -> (X.v, [Y.vo, …])
    for ln in p.stdout.split("\n"):
        if ":" not in ln:
            continue
        lhs, rhs = ln.split(":", 1)
        targets = lhs.split()
        if not targets or not targets[0].endswith(".vo"):
            continue
        prereqs = rhs.split()
        vs = [x for x in prereqs if x.endswith(COQ_EXT)]
        vos = [x for x in prereqs if x.endswith(".vo")]
        if len(vs) != 1:
            raise Refusal(
                f"coqdep rule {ln.strip()!r} names {len(vs)} `.v` source(s); expected one"
            )
        rules[targets[0]] = (vs[0], vos)
    by_v = {v: vo for vo, (v, _) in rules.items()}
    seed_rel = file.relative_to(proj).as_posix()
    seed_rel_dot = f"./{seed_rel}"
    start = by_v.get(seed_rel) or by_v.get(seed_rel_dot)
    if start is None:
        raise Refusal(
            f"{seed!r} is not listed by {COQ_PROJECT} in "
            f"{proj.relative_to(wt).as_posix()!r} (coqdep emitted no rule for it) at "
            f"pinned master {commit[:12]}{context}"
        )
    seen: List[str] = []
    stack = [start]
    while stack:
        vo = stack.pop()
        if vo in seen:
            continue
        if vo not in rules:
            raise Refusal(
                f"coqdep names prerequisite {vo!r} for which {COQ_PROJECT} lists no "
                f"source at pinned master {commit[:12]}{context}; a same-repo Coq file "
                "outside the project listing would silently leave S — refusing"
            )
        seen.append(vo)
        stack.extend(rules[vo][1])
    files = sorted(
        os.path.relpath(os.path.normpath(str(proj / rules[vo][0])), str(wt)).replace(
            os.sep, "/"
        )
        for vo in seen
    )
    detail = OrderedDict(
        [
            ("tool", "coqdep"),
            ("project_dir", proj.relative_to(wt).as_posix()),
            ("modules", seen),
            ("nonlocal_namespaces", []),
        ]
    )
    return files, detail


def closure_of(
    repo: Path, commit: str, seed: str, context: str = ""
) -> Tuple[List[str], Dict[str, Any]]:
    """Dispatch a same-repo seed (which exists at the pin) to its prover's tool; any
    other extension is a leaf (today no such seed exists — evidence names proof files).
    """
    if seed.endswith(LEAN_EXT):
        return lean_closure(repo, commit, seed, context)
    if seed.endswith(AGDA_EXTS):
        return agda_closure(repo, commit, seed, context)
    if seed.endswith(COQ_EXT):
        return coq_closure(repo, commit, seed, context)
    return [seed], OrderedDict([("tool", "none (leaf)"), ("modules", [])])


def toolchain_handle(repo: Path, commit: str) -> Dict[str, str]:
    """The closure's handle (QBP#700, RCA): `proofs/lean-toolchain` at the pin, and the
    versions of lake (run in the pin's `proofs/`, so elan picks that toolchain), agda
    and coqc — `not installed` written explicitly, never omitted."""
    wt = pin_worktree(repo, commit)
    proofs = wt / LEAN_SRC_ROOT
    blob = blob_sha(repo, commit, LEAN_TOOLCHAIN_FILE)
    return OrderedDict(
        [
            (
                "lean_toolchain",
                blob_text(repo, blob).strip() if blob else "absent at the pin",
            ),
            ("lake", tool_version("lake", proofs if proofs.is_dir() else wt)),
            ("agda", tool_version("agda", wt)),
            ("coqc", tool_version("coqc", wt)),
        ]
    )


# per-anchor closure record for the report (filled by `pinned_sha_for`, read by
# `grade_ledger`); keyed by anchor id
_CLOSURE_DETAIL: Dict[str, Dict[str, Any]] = {}


# ---- out-of-tree guard (architecture ruling live-test seq 2446) ------------------------
def is_pathlike(value: Any) -> bool:
    """True iff a `proof_file` value LOOKS like a file path (a separator or a proof-source
    extension); "Hurwitz 1898" / "Hurwitz corollary" are citations, not paths."""
    return (
        isinstance(value, str)
        and bool(value)
        and ("/" in value or "\\" in value or value.endswith(PATH_EXTS))
    )


def check_in_tree(path: str, anchor_id: str, what: str, where: str = "") -> str:
    """Refuse a closure seed that resolves outside the repo's proof tree: absolute, a
    `..` segment, or not under `proofs/`. Never a closure seed; the anchor is named.
    Returns the seed to use: `posixpath.normpath(path)` (`proofs//x.lean`,
    `proofs/./x.lean` → `proofs/x.lean`, so an existing file is never mislabelled
    `stale_proof_file` — RT N2). The `..` rule is applied to the ORIGINAL string, as the
    ruling words it ("a `..` segment ⇒ refusal"): `proofs/../docs/x.lean` is refused
    even though it would normalise to `docs/x.lean` (and `proofs/x/../y.lean` even
    though it would normalise back inside the tree)."""
    segs = re.split(r"[\\/]", path)
    norm = posixpath.normpath(path)
    # the absolute-path arm is subsumed by the `proofs/` prefix check (every absolute
    # path fails it too — §I4 live-test seq 2455: an equivalent mutant) and is kept only
    # so the refusal names the actual fault
    if path.startswith(("/", "\\")) or re.match(r"^[A-Za-z]:", path):
        why = "is an absolute path"
    elif ".." in segs:
        why = "contains a `..` segment"
    elif not norm.startswith(LOCAL_TREE_PREFIX):
        why = f"is not under {LOCAL_TREE_PREFIX}"
    else:
        return norm
    raise Refusal(
        f"{anchor_id}: {what} {path!r} {why} — it resolves outside the repo's proof "
        f"tree and is never a closure seed{where} (architecture ruling seq 2446; a "
        "bare-root file is mapped via the lakefile, never guessed)"
    )


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


REPORT_PATH_CONVENTION = (
    "paths are recorded relative to a named base, never as the absolute path of the "
    "checkout the encoder happened to run in (RT N5 on PR #703): `<repo>` = the QBP "
    "checkout (`--repo`), `<evidence-repo>` = the toplevel of the git checkout "
    "`--evidence-dir` lives in — the checkout the evidence-repo identity row (remote + "
    "HEAD) names; its own path is never recorded (RT N7) — `<evidence-dir>` = "
    "`--evidence-dir`; a path under none of them is recorded as given"
)


def record_path(p: Path, bases: List[Tuple[str, Optional[Path]]]) -> str:
    """`p` for the report: `<label>/<relative>` under the first of `bases` that contains
    it (each base's identity is on record elsewhere in the report — the evidence repo's
    remote + HEAD, the ledger's repo), else `p` as given. An ephemeral scratch checkout
    or a review worktree is not the record (RT N5), nor is its path (RT N7)."""
    rp = p.resolve()
    for label, base in bases:
        if base is None:
            continue
        try:
            rel = rp.relative_to(base.resolve())
        except ValueError:
            continue
        return label if str(rel) == "." else f"{label}/{rel.as_posix()}"
    return str(p)


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
                    "file": record_path(p, [("<evidence-dir>", evidence_dir)]),
                    "reason": f"not the engine v2 record shape (top-level keys: {top})",
                }
            )
    return records, ignored


def group_by_claim(
    records: List[Tuple[Path, Dict[str, Any]]],
    anchor_ids: set,
    target_ids: Optional[set] = None,
    kinds: Optional[Dict[str, Any]] = None,
    evidence_dir: Optional[Path] = None,
) -> Tuple[
    Dict[str, List[Tuple[Path, Dict[str, Any]]]],
    List[Dict[str, str]],
    List[Dict[str, Any]],
]:
    """(by_claim over TARGET anchors, unmatched_claim, evidence_for_non_target). A record
    whose claim is a ledger anchor but not a target anchor (e.g. a MEAS-*) is listed, not
    graded and not silently dropped (RT N3a). `target_ids=None` ⇒ every anchor is a target
    (tests of the merge path). `evidence_dir` is the base the record paths are written
    relative to (`<evidence-dir>/…`, RT N5); None ⇒ as given."""
    by_claim: Dict[str, List[Tuple[Path, Dict[str, Any]]]] = OrderedDict()
    unmatched: List[Dict[str, str]] = []
    non_target: List[Dict[str, Any]] = []
    bases: List[Tuple[str, Optional[Path]]] = [("<evidence-dir>", evidence_dir)]
    for p, doc in records:
        cid = doc["claim"]
        if cid not in anchor_ids:
            unmatched.append({"file": record_path(p, bases), "claim": cid})
            continue
        if target_ids is not None and cid not in target_ids:
            non_target.append(
                {
                    "file": record_path(p, bases),
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
    cid: str,
    recs: List[Tuple[Path, Dict[str, Any]]],
    evidence_dir: Optional[Path] = None,
) -> Dict[str, Any]:
    """Fold one anchor's v2 records into the engine inputs: assistants concatenated in
    file order; the correspondence block from the single record that asserts one (two
    asserting records are ambiguous ⇒ refuse); corroborated_by unioned. `files` are
    recorded as `<evidence-dir>/…` when `evidence_dir` is given (RT N5)."""
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
        "files": [record_path(p, [("<evidence-dir>", evidence_dir)]) for p, _ in recs],
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


def collapse_to_one_per_kernel(
    kept: List[Dict[str, Any]],
) -> Tuple[List[Dict[str, Any]], List[str]]:
    """RT C7 (architecture ruling seq 2386; module doc §3c): the engine's GradeClaim
    counts clean ASSISTANTS, not kernels, so `[coq, coq]` with no lean4 would reach PA 2
    from one kernel. Keep the FIRST admissible assistant per prover kind (`assistant`),
    in order; every later same-kind survivor is dropped with flag
    `same_kernel_duplicate:<kind>`. Runs AFTER `filter_assistants_by_target` and BEFORE
    the engine Claim / ledger array are built. ONE function; a ruling flips it here."""
    seen: set = set()
    out: List[Dict[str, Any]] = []
    flags: List[str] = []
    for a in kept:
        kind = a.get("assistant")
        if kind in seen:
            flags.append(f"same_kernel_duplicate:{kind if kind else '?'}")
            continue
        seen.add(kind)
        out.append(a)
    return out, flags


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
    record can be found without re-running the whole batch. The per-seed closure record
    (tool, modules, non-local namespaces) is left in `_CLOSURE_DETAIL[anchor id]` for
    the report."""
    flags: List[str] = []
    where = (
        f" (claim {anchor['id']!r} in record " + ", ".join(record_files) + ")"
        if record_files
        else f" (claim {anchor['id']!r})"
    )
    has_evidence = bool(assistants)
    aid = anchor["id"]
    proof_file = anchor.get("proof_file")
    # seeds: path -> origin ("proof_file" | "evidence_ref"); the prover tools add the
    # imports. seq 2446: every seed is checked to lie inside the proof tree BEFORE it can
    # seed anything; a non-path proof_file (a literature citation) is not a seed at all.
    paths: Dict[str, str] = OrderedDict()
    if is_pathlike(proof_file):
        paths[check_in_tree(proof_file, aid, "declared proof_file", where)] = (
            "proof_file"
        )
    elif has_evidence and isinstance(proof_file, str) and proof_file:
        # today's behaviour kept: a citation cannot pin a claim that evidence is being
        # graded against — the declared source is not a file (architecture 3c)
        raise Refusal(
            f"{aid}: declared proof_file {proof_file!r} is not a repo path (a literature "
            f"citation) while evidence is being graded{where}; the evidence cannot be "
            "tied to a declared source file and pinned_sha must never be empty when "
            "grading evidence"
        )
    for a in assistants:
        ref = a.get("evidence_ref")
        if not evidence_ref_is_local(ref):
            # cross-repo evidence (e.g. the notary's Coq port): validated above
            # (prefix + commit), pinned by its own commit + reproduce; it never
            # enters S — the claim-source manifest is over THIS repo's files only.
            if "cross_repo_evidence" not in flags:
                flags.append("cross_repo_evidence")
            continue
        p = check_in_tree(
            evidence_ref_path(ref), aid, "same-repo evidence_ref path", where
        )
        paths.setdefault(p, "evidence_ref")
    # seq 2394 / QBP#696 (QBP#700): S = the union, over the seeds, of each seed's
    # transitive same-repo import closure AS THE SEED'S OWN PROVER TOOL DERIVES IT at the
    # pinned commit (`closure_of`: Lake facets / agda --dependency-graph / coqdep, run in
    # the hermetic pin worktree); library modules (Mathlib / Std / Lean core; the pinned
    # agda/cubical; Coq's stdlib) never enter — the tools place them outside the tree.
    by_path: Dict[str, str] = OrderedDict()  # path -> blob
    detail: Dict[str, Any] = OrderedDict([("seeds", list(paths)), ("closures", [])])
    context = f" (anchor {aid}{where})"
    for path, origin in paths.items():
        blob = blob_sha(repo, commit, path)
        if blob is None:
            if origin == "evidence_ref":
                raise Refusal(
                    f"{aid}: evidence_ref path {path!r} does not exist at pinned "
                    f"master {commit[:12]}{where}; pinned_sha cannot be computed for "
                    "evidence that names a file the pinned tree does not have (S covers "
                    "every same-repo ref of the record, dropped or kept)"
                )
            if has_evidence:
                raise Refusal(
                    f"{aid}: declared proof_file {path!r} does not exist at "
                    f"pinned master {commit[:12]}{where} while evidence is being graded; "
                    "pinned_sha must never be empty when grading evidence"
                )
            # a path-valued proof_file the pinned tree does not have: inert (nothing
            # to be stale) but NAMED — the report's `stale_proof_file` section (AC5)
            flags.append("stale_proof_file")
            continue
        files, d = closure_of(repo, commit, path, context)
        d = OrderedDict([("seed", path), *d.items()])
        detail["closures"].append(d)
        for f in files:
            if f in by_path:
                continue
            b = blob_sha(repo, commit, f)
            if b is None:
                raise Refusal(
                    f"{aid}: {d['tool']} lists {f!r} in the closure of {path!r}, but it "
                    f"is not a tracked file at pinned master {commit[:12]}{where} (a "
                    "generated or untracked source cannot be pinned by its blob)"
                )
            by_path[f] = b
    _CLOSURE_DETAIL[aid] = detail
    sources = sorted(
        ({"path": p, "blob": b} for p, b in by_path.items()), key=lambda s_: s_["path"]
    )
    if not sources:
        if not has_evidence and "stale_proof_file" not in flags:
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
    evidence_dir: Optional[Path] = None,
) -> Tuple[Dict[str, Dict[str, Any]], Dict[str, Any]]:
    """Grade every target anchor. Returns ({id: result}, engine_output). A result carries
    pa, effective_pa, clean_count, flags (engine), assistants (engine split), evidence
    (merged v2 inputs or None), pinned_sha, sources, report_flags. `evidence_dir` is the
    base the evidence file paths are recorded relative to (RT N5)."""
    targets = target_anchors(ledger)
    results: Dict[str, Dict[str, Any]] = OrderedDict()
    claims: List[Dict[str, Any]] = []
    for a in targets:
        ev = (
            merge_claim_records(a["id"], by_claim[a["id"]], evidence_dir)
            if a["id"] in by_claim
            else None
        )
        rflags: List[str] = []
        # RT C4: S = the same-repo import closure (each prover's own tool, QBP#700) of
        # proof_file ∪ the CLAIM's same-repo refs (seq 2299 / 2394) — over EVERY
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
            # RT C7 (seq 2386): one assistant per prover kind reaches the engine and
            # the ledger array — the engine counts assistants, not kernels.
            kept, dups = collapse_to_one_per_kernel(kept)
            dropped.extend(dups)
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
            "closure": _CLOSURE_DETAIL.pop(a["id"], None),
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
    # Additive reuse hook (no grading effect): the real-ledger reconcile harness
    # (scripts/test_pa_ledger.py, QBP#692 strike-2) drives the Go `pa-reconcile` gate
    # with the SAME engine-input claims this builds, so the checker and the writer
    # never diverge on claim-construction. Mirrors `_edges` above.
    out["_claims"] = claims
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
        f"(S = same-repo import closure of proof_file ∪ same-repo evidence files — Lean "
        f"via the lakefile-derived module map over every lake library, Agda via every "
        f"same-repo Agda root at the pin with unknown-namespace refusal; sorted `path "
        f"blob` lines, git hash-object --stdin; "
        f"architecture rulings seq 2299/2394, scope QBP#696), "
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
                ("closure", r.get("closure")),
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
    # seq 2446 / AC5: path-valued proof_files that do not resolve at the pin (expected
    # empty) and the non-path / absent ones (the two citation strings), both NAMED.
    stale_pf = [
        {"id": cid, "proof_file": by_id[cid].get("proof_file")}
        for cid, r in results.items()
        if "stale_proof_file" in r["report_flags"]
    ]
    no_pf = [
        {"id": cid, "proof_file": by_id[cid].get("proof_file")}
        for cid, r in results.items()
        if "no_proof_file" in r["report_flags"]
    ]
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
            ("path_convention", REPORT_PATH_CONVENTION),
            ("evidence_store_sha", meta.get("evidence_store_sha")),
            # RT N2 (PR #697): the evidence store's identity — repo + HEAD — so the
            # record is reproducible without out-of-band knowledge; `unknown (not a
            # git checkout)` is written explicitly, never omitted.
            ("evidence_repo", meta["evidence_repo"]),
            # QBP#700 / QBP#696: the closure's toolchain handle — lean-toolchain at the
            # pin + the versions of the prover tools whose dependency output S is
            ("closure_toolchain", meta.get("closure_toolchain")),
            ("v2_record_count", meta["v2_record_count"]),
            ("target_anchor_count", len(rows)),
            (
                "targets_without_lean_theorem",
                {"count": len(no_headline), "ids": no_headline},
            ),
            ("stale_proof_file", stale_pf),
            ("no_proof_file", no_pf),
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
                "claim-source manifest hash: S = the transitive closure, over SAME-REPO "
                "imports at the pinned commit, of {proof_file} ∪ {SAME-REPO evidence_ref "
                "paths — grammar [<owner>/<repo>:]<path>@<commit>#<target>, no prefix = "
                "QBP; cross-repo refs never enter S (seq 2342)} (ruling seq 2394; scope "
                "QBP#696). Each seed's closure is DERIVED FROM ITS PROVER'S OWN DEPENDENCY "
                "TOOL run in a temporary git worktree of the pin (QBP#700; architecture "
                "§I4 conditions 1–3), never from a parser of ours: Lean — Lake's facets "
                "under `lake query --no-build` (`translate-config` for the libraries, "
                "`:modules`, `+M:lean`, `+M:transImports` ∩ the libraries' modules; G-L1 on "
                "EVERY member of S: a header import Lake dropped silently that is no "
                "toolchain .olean refuses); Agda — `agda --only-scope-checking "
                "--dependency-graph` from the member's library dir with the clean-"
                "interface state ASSERTED (no _build/, no *.agdai under proofs/; G-A1), "
                "module → file from Agda's `Checking M (path)` lines, S = reachable ∩ "
                "files inside the pin; Coq — `coqdep -f _CoqProject` (required), any stderr "
                "line refuses (G-C1), closure over the .vo prerequisites. Library modules "
                "(Mathlib/Std/Lean, agda/cubical, Coq stdlib) lie outside the tree and "
                "never enter. A .lean seed that is a module of no Lake library refuses; a "
                "missing tool refuses (never a fallback). Seeds outside proofs/ (absolute, "
                "`..`, other prefix) are refused (seq 2446); a non-path proof_file "
                "(citation) is no_proof_file, a missing path-valued one stale_proof_file. "
                "Lines `path <git rev-parse <commit>:path>\\n` sorted by path; pinned_sha = "
                "git hash-object --stdin over the lines (ruling seq 2299)",
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
                "2353, §I4 round 2 seq 2367, RT C5/N11); the survivors are then "
                "collapsed to the FIRST admissible assistant per prover kind — the "
                "engine counts assistants, not kernels — later same-kind survivors "
                "dropped with flag same_kernel_duplicate:<kind> (RT C7; architecture "
                "seq 2386)",
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
    md.append(f"| paths | {REPORT_PATH_CONVENTION} |")
    er = meta["evidence_repo"]
    md.append(
        f"| evidence repo (RT N2) | remote `{er['remote']}`; HEAD `{er['head']}` |"
    )
    md.append(
        f"| evidence store sha (QBP#701 INTER_PIN) | `{meta.get('evidence_store_sha')}` |"
    )
    tc = meta.get("closure_toolchain") or {}
    md.append(
        "| closure toolchain handle (QBP#700) | "
        + "; ".join(f"{k} `{v}`" for k, v in tc.items())
        + " |"
    )
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
    md.append(
        f"| stale `proof_file` pointers (path-valued, missing at the pin; AC5) | "
        f"{len(stale_pf)} |"
    )
    md.append(f"| no `proof_file` (non-path or absent; inert) | {len(no_pf)} |")
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
            "the Fano table; 2 iff a promoted v2 record carries two distinct kernel-clean assistants on the headline (cycle-8: Lean decide + Coq mulCoeff port, cth correspondence); 0 while no such record is in the canonical store",
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
    md.append(
        "## Stale proof_file pointers (path-valued `proof_file` that does not resolve at "
        "the pinned master; seq 2446 / QBP#696 AC5 — expected empty)\n"
    )
    if stale_pf:
        for s in stale_pf:
            md.append(f"- `{s['id']}` — `{s['proof_file']}`")
    else:
        md.append("None.")
    md.append("")
    md.append(
        "## No proof_file (not a path — a literature citation — or absent; inert, "
        "pinned_sha empty)\n"
    )
    if no_pf:
        for s in no_pf:
            md.append(f"- `{s['id']}` — {s['proof_file']!r}")
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
            tools = sorted(
                {c["tool"] for c in (r.get("closure") or {}).get("closures", [])}
            )
            md.append(
                f"- `{r['id']}` → `{r['pinned_sha']}` ← {lines} (closure by "
                f"{', '.join(tools) or '—'})"
            )
        else:
            md.append(
                f"- `{r['id']}` → (no resolvable source; pinned_sha empty, inert)"
            )
    md.append("\n</details>\n")
    return "\n".join(md) + "\n", rep


# ---------------------------------------------------------------------------------------
# evidence repo identity (RT N2 on PR #697)
# ---------------------------------------------------------------------------------------
EVIDENCE_REPO_UNKNOWN = "unknown (not a git checkout)"


def _git_q(evidence_dir: Path, *args: str) -> Optional[str]:
    """Trimmed stdout of `git -C <evidence_dir> <args>`, or None on failure / no output."""
    p = subprocess.run(
        ["git", "-C", str(evidence_dir), *args],
        capture_output=True,
        text=True,
        check=False,
    )
    s = p.stdout.strip()
    return s if p.returncode == 0 and s else None


def evidence_repo_toplevel(evidence_dir: Path) -> Optional[Path]:
    """The toplevel of the git checkout `evidence_dir` lives in (`rev-parse
    --show-toplevel`) — the `<evidence-repo>` base of `record_path`, never itself written
    into the report (RT N7 on PR #703: a scratch checkout's path is not the record; remote
    + HEAD already identify the store). None when `evidence_dir` is not in a checkout.
    """
    top = _git_q(evidence_dir, "rev-parse", "--show-toplevel")
    return Path(top) if top else None


def evidence_repo_identity(evidence_dir: Path) -> Dict[str, str]:
    """{head, remote} of the git checkout `evidence_dir` lives in — `git -C <dir>
    rev-parse HEAD`, `remote get-url origin` — so the AC4 record names the canonical
    evidence commit (e.g. inter main `333134c`), not a local path. A directory that is
    not inside a git checkout records the explicit string `unknown (not a git checkout)`
    in every field; nothing is ever omitted. The checkout's own path is deliberately NOT
    a field (RT N7 on PR #703): it would be the ephemeral worktree the run happened to
    use, and `<evidence-repo>` in the record paths already stands for it."""
    if evidence_repo_toplevel(evidence_dir) is None:
        return OrderedDict(
            [("head", EVIDENCE_REPO_UNKNOWN), ("remote", EVIDENCE_REPO_UNKNOWN)]
        )
    head = _git_q(evidence_dir, "rev-parse", "HEAD")
    remote = _git_q(evidence_dir, "remote", "get-url", "origin")
    return OrderedDict(
        [
            ("head", head if head and HEX40.match(head) else "unknown (no commits)"),
            ("remote", remote or "unknown (no origin remote)"),
        ]
    )


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
    # RT C2 (PR #703): the pin worktree(s) this run made are removed when the run
    # ends — normally, on a Refusal (a SystemExit) or on any other exception — not
    # only at interpreter exit; `atexit` stays registered as the belt.
    try:
        commit = resolve_commit(repo, pinned_master)
        ledger_before = json.loads(ledger_path.read_text(encoding="utf-8"))
        records, ignored = load_evidence(evidence_dir)
        anchor_ids = {a["id"] for a in ledger_before["anchors"]}
        target_ids = {a["id"] for a in target_anchors(ledger_before)}
        kinds = {a["id"]: a.get("provenance_kind") for a in ledger_before["anchors"]}
        by_claim, unmatched, non_target = group_by_claim(
            records, anchor_ids, target_ids, kinds, evidence_dir
        )
        results, engine_out = grade_ledger(
            ledger_before, by_claim, repo, commit, evidence_dir
        )
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
        # The git sha of the evidence store this backfill graded against (QBP#692 strike-2
        # invariant, architect seq 2554): pa-reconcile.yml's INTER_PIN must equal this, so the
        # pin moves atomically with the ledger. Resolved when evidence_dir is a git checkout
        # (it is in CI and in the beekeeper's inter checkout); None otherwise — never fatal.
        _store = _git(evidence_dir, "rev-parse", "HEAD", check=False)
        evidence_store_sha = (
            _store.stdout.strip()
            if _store.returncode == 0 and _store.stdout.strip()
            else None
        )
        evidence_repo = evidence_repo_identity(evidence_dir)
        ev_top = evidence_repo_toplevel(
            evidence_dir
        )  # the base only; never recorded (N7)
        meta = {
            "today": today,
            # RT N5: paths relative to a named base (REPORT_PATH_CONVENTION), never the
            # absolute path of the checkout this run happened to use
            "ledger": record_path(ledger_path, [("<repo>", repo)]),
            "pinned_master_rev": pinned_master,
            "pinned_master_commit": commit,
            "evidence_dir": record_path(evidence_dir, [("<evidence-repo>", ev_top)]),
            "evidence_store_sha": evidence_store_sha,
            "evidence_repo": evidence_repo,
            "closure_toolchain": toolchain_handle(repo, commit),
            "v2_record_count": len(records),
            "version_after": version if changed else None,
        }
        md, rep = build_report(
            ledger_before,
            results,
            plan,
            engine_out,
            meta,
            ignored,
            unmatched,
            non_target,
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
    finally:
        cleanup_pin_worktrees()


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
    er = rep["evidence_repo"]
    print(
        "closure toolchain: "
        + "; ".join(f"{k} {v}" for k, v in (rep.get("closure_toolchain") or {}).items())
    )
    print(
        f"evidence repo: {er['remote']} @ {er['head']}; "
        f"stale proof_file pointers: {len(rep['stale_proof_file'])}; "
        f"no proof_file: {len(rep['no_proof_file'])}"
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
