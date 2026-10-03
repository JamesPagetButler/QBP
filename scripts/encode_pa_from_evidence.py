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
   — FINAL; scope extended to every lake library + Agda by QBP#696): the claim-source
   MANIFEST hash. S = the TRANSITIVE CLOSURE, over SAME-REPO imports, of {anchor
   proof_file} ∪ {SAME-REPO paths named by the claim's v2 evidence_refs}, deduplicated —
   a claim's statement depends on the definitions its file imports (the Fano headline
   names `fanoTableF4`, defined in FanoOrientationF3.lean), so those files are part of
   what the evidence pinned. LEAN module → file is DERIVED FROM `proofs/lakefile.lean` AT
   THE PINNED COMMIT (`lake_module_map`, memoised per pin; `parse_lakefile`): every
   `lean_lib «Name» where … roots := #[…] / srcDir := "…"` block maps each root module to
   `proofs/<srcDir or .>`, so `import QBP.A.B` → `proofs/QBP/A/B.lean` (lib «QBP», roots
   [QBP]) and `import Sedenion` → `proofs/Sprint12-Inherited/Sedenion.lean` (lib
   «QBPSprint12», srcDir "Sprint12-Inherited", bare roots Bi2Se3 … SedenionHessianTraceSq);
   a module whose first component is no lib root (Mathlib, Std, Lean, Aesop, …) is
   non-local — pinned by the lake manifest (inter#153) — and skipped; no lakefile at the
   pin while a `.lean` member has imports ⇒ refusal (the map cannot be guessed). AGDA
   members (`.agda` / `.lagda.md` / `.lagda`) are scanned ANYWHERE in the file (Agda allows
   imports after the module header) for `import X.Y` led only by modifiers (`open` /
   `private` / `abstract` / `instance` — RT N8), comments (`--`, nested `{- -}`)
   stripped, and resolve against EVERY same-repo Agda root at the pin: the member's OWN
   corpus root first (`agda_root_of`: the directory left when the file's `module A.B.C`
   name is peeled off its path — `proofs/agda/` or `proofs/agda-cubical/`), then every
   `include:` directory of every `*.agda-lib` under `proofs/` at the pinned commit
   (`agda_lib_roots`; today `proofs/agda-cubical/qbp-cubical.agda-lib` → the same dir),
   in a deterministic order: `X/Y.agda`, else `.lagda.md`, else `.lagda`. Found ⇒ enters
   S and is scanned transitively. Found under NO root ⇒ accepted as a library import ONLY
   when its first dotted component is in `AGDA_EXTERNAL_NAMESPACES` (`Agda` — the
   compiler's builtins; `Cubical` — agda/cubical, the `depend: cubical-0.9` library);
   any other unresolved module is a REFUSAL naming the importing file, the module and the
   roots searched (Gemini on PR #698: a same-repo module the closure cannot see would
   silently shrink S). Imports are read from the file content AT THE PINNED COMMIT (`git
   cat-file blob`), never from a checkout; Lean reads the header only (imports precede
   every other command) (`lean_header_imports`, `lean_module_path`, `local_imports_of`).
   An imported LEAN module whose file does not exist at the pinned commit is a refusal
   naming the anchor, the claim, the record and the importing file. OUT-OF-TREE GUARD
   (architecture ruling live-test seq 2446): a path-valued `proof_file` or a same-repo
   evidence_ref path that is absolute, contains a `..` segment, or does not start with
   `proofs/` is a refusal naming the anchor and is NEVER a closure seed
   (`check_in_tree`); a `proof_file` that is not a path at all (the literature citations
   `PROOF-hurwitz` "Hurwitz 1898", `PROOF-born` "Hurwitz corollary") is `no_proof_file`,
   inert; a path-valued `proof_file` that does not exist at the pin is `stale_proof_file`
   (inert without evidence, refusal with it) and is listed in the report's
   `stale_proof_file` section (AC5). The walk is a seen-set BFS, so an import cycle
   terminates. evidence_ref grammar (§I4 ruling on PR #695, live-test
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
   commit; a declared proof_file that does not exist at the pinned commit — or is not a
   path at all (a citation) — while evidence is being graded (pinned_sha must never be
   empty when grading evidence — architecture 3c).
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
   origin` + `--show-toplevel`; a directory that is not a git checkout is recorded as the
   explicit string `unknown (not a git checkout)`, never omitted — `evidence_repo_identity`),
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
# seq 2394 + QBP#696: the claim-source manifest closes over SAME-REPO imports. The Lean
# module → file map is DERIVED from `proofs/lakefile.lean` at the pinned commit (every
# `lean_lib` block's `roots`, default the lib name, and `srcDir`, default "."): today
# lib «QBP» (roots [QBP], srcDir .) → proofs/QBP/…, lib «QBPSprint12» (srcDir
# "Sprint12-Inherited", bare roots Bi2Se3 … SedenionHessianTraceSq) → proofs/Sprint12-
# Inherited/<Root>.lean. A module whose first component is no lib root (Mathlib, Std,
# Lean, Aesop, …) is non-local: pinned by the lake manifest (inter#153), skipped. Agda
# members resolve `import X.Y` against every same-repo Agda root at the pin — their own
# corpus root first (proofs/agda, proofs/agda-cubical), then every `include:` dir of
# every `*.agda-lib` under proofs/ — and a module found under none is a library import
# ONLY when its namespace is listed in AGDA_EXTERNAL_NAMESPACES; otherwise a refusal.
LEAN_SRC_ROOT = "proofs"
LAKEFILE = "proofs/lakefile.lean"
LEAN_EXT = ".lean"
AGDA_EXTS = (".agda", ".lagda.md", ".lagda")  # resolution order at the pin
AGDA_LIB_EXT = ".agda-lib"
# The top-level namespaces an UNRESOLVED Agda import may belong to without refusing —
# the libraries the corpus is checked against, pinned outside this repo (inter#153), so
# their modules never enter S. Gathered from the corpus at 516dfcb (every `import` line
# of the 17 `.agda` files under proofs/ + the one `.agda-lib`):
#   `Agda`    — the compiler's own builtins (`Agda.Primitive`, `Agda.Builtin.Cubical.Path`):
#               the only library the 4 proofs/agda members import; shipped with agda,
#               never an .agda-lib `depend:`.
#   `Cubical` — the agda/cubical library: proofs/agda-cubical/qbp-cubical.agda-lib has
#               `depend: cubical-0.9`, whose library NAME (`cubical-0.9`) differs from
#               the module namespace it exports (`Cubical.*`), so the namespace is listed
#               explicitly — a `depend:` line cannot be mapped to a namespace mechanically.
# A new external library needs a row here (and a review) before its modules are skipped;
# until then its imports refuse. Same-repo modules are never listed: a module that exists
# under a same-repo root is found there first, whatever its namespace.
AGDA_EXTERNAL_NAMESPACES = frozenset({"Agda", "Cubical"})
# RT N8 (PR #698): the tokens that may precede `import` on a declaration line. Agda
# accepts `private open import X` / `abstract import X` / `instance open import X` on one
# line (2.8.0 type-checks them); anything else before `import` (`x = import`,
# `y = foo import Z`) makes it an identifier, not a declaration (RT N5).
AGDA_IMPORT_MODIFIERS = frozenset({"open", "private", "abstract", "instance"})
# seq 2446: every closure seed (proof_file, same-repo evidence_ref path) must live under
# this tree; an absolute path, a `..` segment, or any other prefix is refused.
LOCAL_TREE_PREFIX = "proofs/"
# A proof_file is PATH-VALUED iff it looks like one: a separator or a proof-source
# extension. The two literature citations (`PROOF-hurwitz` "Hurwitz 1898", `PROOF-born`
# "Hurwitz corollary") are neither → `no_proof_file`, inert.
PATH_EXTS = (LEAN_EXT, ".v", *AGDA_EXTS)

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


def strip_lean_comments(text: str, strings: bool = False) -> str:
    """Drop `/- … -/` block comments (nested, as Lean nests them; `/-- … -/` doc comments
    included) and `-- …` line comments, so a commented-out `import` is never followed.
    `strings=True` copies a `"…"` literal verbatim (`\"` escapes honoured) so a `--` or
    `/-` INSIDE a string is text, as Lean's lexer has it — the lakefile parser needs this
    (`srcDir := "a--b"`, RT M1 on PR #698); the import scanner does not (imports precede
    every string literal in a Lean file) and keeps the default.
    """
    out: List[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if strings and not depth and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i : min(j + 1, n)])
            i = j + 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def lean_header_imports(text: str) -> List[str]:
    """EVERY module a Lean file imports, in order, deduplicated — local or not.

    Reads the HEADER only — Lean puts every `import` (after an optional `prelude`) before
    the first other command, so the scan stops at the first non-import token. Comments
    are stripped first. `import runtime X` and `«quoted»` names are tolerated. Which of
    these are same-repo is decided by the lakefile-derived module map
    (`lean_local_imports` / `lean_module_path`), never by a name prefix."""
    toks = strip_lean_comments(text).split()
    mods: List[str] = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if t == "prelude":
            i += 1
            continue
        if t != "import":
            break
        i += 1
        if i < len(toks) and toks[i] == "runtime":
            i += 1
        if i >= len(toks):
            break
        m = toks[i].replace("«", "").replace("»", "")
        i += 1
        if m not in mods:
            mods.append(m)
    return mods


# ---- lakefile-derived module map (QBP#696) ---------------------------------------------
LAKE_BLOCK_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(lean_lib|package)\s+(?:«([^»]+)»|([A-Za-z_][\w.]*))?"
)  # a leading `@[default_target]` on the SAME line is tolerated (RT M1)
LAKE_STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
LAKE_LIB_TOKEN_RE = re.compile(r"\blean_lib\b")
LAKE_NAME_RE = re.compile(r"`(?:«([^»]+)»|([A-Za-z_][\w.]*))")
LAKE_SRCDIR_RE = re.compile(r"\bsrcDir\s*:=\s*\"([^\"]*)\"")
LAKE_ROOTS_RE = re.compile(r"\broots\s*:=\s*#\[([^\]]*)\]")


def _lake_field_tail_check(body: str, m: "Optional[re.Match[str]]") -> None:
    """RT N7: refuse when anything but whitespace follows a matched `roots` / `srcDir`
    literal on its physical line — the regex read a literal, Lake would evaluate an
    expression (`#[`A] ++ #[`B]`, `"a" / "b"`), and the two must never disagree
    silently."""
    if m is None:
        return
    end = m.end()
    nl = body.find("\n", end)
    tail = body[end:] if nl < 0 else body[end:nl]
    if tail.strip():
        start = body.rfind("\n", 0, end) + 1
        line = body[start:] if nl < 0 else body[start:nl]
        raise Refusal(
            f"{LAKEFILE}: `{line.strip()}` continues past the parsed literal with "
            f"`{tail.strip()}` — the field is an expression this parser does not "
            "evaluate (RT N7 on PR #698), and a half-read `roots` / `srcDir` would "
            "silently make an import non-local and shrink S, so the module map is not "
            "derived"
        )


def parse_lakefile(text: str) -> "OrderedDict[str, str]":
    """root module → source directory (relative to the lakefile's directory) from a Lake
    DSL lakefile. For each top-level `lean_lib «Name» where` block: `roots := #[`A, `B]`
    (default `[Name]`) and `srcDir := "dir"` (default "."), prefixed by the `package`
    block's `srcDir` when it sets one (Lake resolves a library's srcDir under the
    package's). `lean_exe` / `require` blocks define no library. The first lib to claim
    a root wins. FAILS CLOSED (RT M1 on PR #698): zero `lean_lib` blocks ⇒ refusal, and
    a `lean_lib` token count (comments stripped, string literals blanked) that differs
    from the number of blocks parsed ⇒ refusal naming both counts — a lakefile this
    parser only half-reads must never silently make an import non-local and shrink S.
    RT N7 (PR #698): the same rule for a half-read FIELD — after a matched `roots := #[…]`
    or `srcDir := "…"` literal, anything but whitespace on the rest of that physical line
    (`roots := #[`A] ++ #[`B]`, `srcDir := "a" / "b"` — legal Lake DSL whose tail the
    literal regex would drop) ⇒ refusal naming the lakefile and the line.

    Today (516dfcb): {QBP: ".", Bi2Se3: "Sprint12-Inherited", …, SedenionHessianTraceSq:
    "Sprint12-Inherited"}."""
    stripped = strip_lean_comments(text, strings=True)
    blocks: List[List[str]] = []
    for ln in stripped.split("\n"):
        if not ln.strip():
            continue
        if ln[0].isspace():
            if blocks:
                blocks[-1].append(ln)
        else:
            blocks.append([ln])
    pkg_src = "."
    libs: List[Tuple[str, str, List[str]]] = []  # (name, srcDir, roots)
    for b in blocks:
        m = LAKE_BLOCK_RE.match(b[0])
        if not m:
            continue
        body = "\n".join(b)
        sm = LAKE_SRCDIR_RE.search(body)
        src = sm.group(1) if sm else "."
        _lake_field_tail_check(body, sm)
        if m.group(1) == "package":
            pkg_src = src
            continue
        name = m.group(2) or m.group(3) or ""
        rm = LAKE_ROOTS_RE.search(body)
        _lake_field_tail_check(body, rm)
        roots = (
            [g1 or g2 for g1, g2 in LAKE_NAME_RE.findall(rm.group(1))] if rm else [name]
        )
        libs.append((name, src, [r for r in roots if r]))
    if not libs:
        raise Refusal(
            f"{LAKEFILE} parsed to zero `lean_lib` blocks; the Lean module map cannot "
            "be derived (parser stale against the lakefile format?) and no import can "
            "be classified local / non-local"
        )
    n_tokens = len(LAKE_LIB_TOKEN_RE.findall(LAKE_STRING_RE.sub('""', stripped)))
    if n_tokens != len(libs):
        raise Refusal(
            f"{LAKEFILE} has {n_tokens} `lean_lib` token(s) but {len(libs)} `lean_lib` "
            "block(s) were parsed; a half-read lakefile would silently drop a library "
            "and shrink S (RT M1), so the module map is not derived"
        )
    out: "OrderedDict[str, str]" = OrderedDict()
    for _name, src, roots in libs:
        d = posixpath.normpath(posixpath.join(pkg_src, src))
        for r in roots:
            out.setdefault(r, d)
    return out


_MODULE_MAP_BY_COMMIT: Dict[Tuple[str, str], Dict[str, str]] = {}


def lake_module_map(repo: Path, commit: str) -> Dict[str, str]:
    """root module → directory under the repo (`proofs/<srcDir>`), from `proofs/lakefile.
    lean` AT `commit` (read from the blob, never a checkout), memoised per (repo, pin).
    No lakefile at the pin ⇒ refusal (the map is derived, never guessed)."""
    key = (str(repo), commit)
    if key not in _MODULE_MAP_BY_COMMIT:
        blob = blob_sha(repo, commit, LAKEFILE)
        if blob is None:
            raise Refusal(
                f"{LAKEFILE} does not exist at pinned master {commit[:12]}; the Lean "
                "module map is derived from it and cannot be guessed, so no `import` "
                "can be classified local / non-local"
            )
        _MODULE_MAP_BY_COMMIT[key] = {
            root: posixpath.normpath(f"{LEAN_SRC_ROOT}/{d}")
            for root, d in parse_lakefile(blob_text(repo, blob)).items()
        }
    return _MODULE_MAP_BY_COMMIT[key]


def lean_module_path(module: str, module_map: Dict[str, str]) -> Optional[str]:
    """`A.B.C` → `<dir of lib root A>/A/B/C.lean` when `A` is a lake-library root in
    `module_map` (`QBP.Foundations.X` → proofs/QBP/Foundations/X.lean; `Sedenion` →
    proofs/Sprint12-Inherited/Sedenion.lean; `QBP` → proofs/QBP.lean); None when it is
    no root (Mathlib / Std / Lean / Aesop … — non-local, lake-manifest pinned)."""
    d = module_map.get(module.split(".", 1)[0])
    if d is None:
        return None
    return f"{d}/{module.replace('.', '/')}{LEAN_EXT}"


def lean_local_imports(text: str, module_map: Dict[str, str]) -> List[str]:
    """The SAME-REPO modules a Lean file imports (header only, comments stripped,
    deduplicated): those of `lean_header_imports` whose first component is a lake-library
    root in `module_map` — `QBP.…` and the «QBPSprint12» bare roots alike; a near-miss
    namespace (`QBPX.Y`) or a library module (`Mathlib.…`) is not."""
    return [m for m in lean_header_imports(text) if lean_module_path(m, module_map)]


_IMPORTS_BY_BLOB: Dict[str, List[str]] = {}


def lean_header_imports_of_blob(repo: Path, blob: str) -> List[str]:
    """`lean_header_imports` of a git blob, memoised by blob sha (content-addressed, so
    148 anchors sharing a few dozen files read each file once per run)."""
    if blob not in _IMPORTS_BY_BLOB:
        _IMPORTS_BY_BLOB[blob] = lean_header_imports(blob_text(repo, blob))
    return _IMPORTS_BY_BLOB[blob]


# ---- Agda (QBP#696) --------------------------------------------------------------------
def strip_agda_comments(text: str) -> str:
    """Drop `{- … -}` block comments (nested, as Agda nests them; `{-# … #-}` pragmas go
    with them — they carry no import) and `-- …` line comments. A `{-` inside a line
    comment does not open a block; a `--` inside a block is text."""
    out: List[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("{-", i):
                depth += 1
                i += 2
            elif text.startswith("-}", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("{-", i):
            depth += 1
            i += 2
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def agda_scan(text: str) -> Tuple[Optional[str], List[str]]:
    """(declared top-level module name or None, imported modules in order, deduplicated)
    of an Agda file. Imports are `import X.Y …` on ANY line of the file (Agda allows them
    after the module header and inside nested modules) where EVERY token before `import`
    is a modifier in `AGDA_IMPORT_MODIFIERS` (`open`, `private`, `abstract`, `instance` —
    `open import X`, `private open import X`, `import X`; RT N8) — so an identifier or
    value named `import` elsewhere on a line (`x = import`, `y = foo import Z`) is not a
    declaration (RT N5); the module name is the token after `import` (`using` /
    `hiding` / `renaming` / `as` / `public` clauses follow it). Comments stripped first.
    """
    stripped = strip_agda_comments(text)
    toks = stripped.split()
    module: Optional[str] = None
    for i, t in enumerate(toks[:-1]):
        if t == "module" and toks[i + 1] != "_":
            module = toks[i + 1]
            break
    mods: List[str] = []
    for ln in stripped.split("\n"):
        w = ln.split()
        if "import" not in w:
            continue
        i = w.index("import")
        if not all(t in AGDA_IMPORT_MODIFIERS for t in w[:i]):
            continue
        if len(w) > i + 1 and w[i + 1] not in mods:
            mods.append(w[i + 1])
    return module, mods


_AGDA_SCAN_BY_BLOB: Dict[str, Tuple[Optional[str], List[str]]] = {}


def agda_scan_of_blob(repo: Path, blob: str) -> Tuple[Optional[str], List[str]]:
    if blob not in _AGDA_SCAN_BY_BLOB:
        _AGDA_SCAN_BY_BLOB[blob] = agda_scan(blob_text(repo, blob))
    return _AGDA_SCAN_BY_BLOB[blob]


def is_agda_path(path: str) -> bool:
    return path.endswith(AGDA_EXTS)


def agda_root_of(path: str, module: Optional[str]) -> str:
    """The corpus root an Agda member resolves its imports against: the directory left
    when the file's own declared `module A.B.C` name is peeled off its path (Agda: path
    relative to an include root == module name) — `proofs/agda-cubical` for
    `proofs/agda-cubical/S3FromCD.agda`, `proofs/agda` for `proofs/agda/QBPHSpace.agda`;
    the file's own directory when no header matches."""
    if module:
        rel = module.replace(".", "/")
        for ext in AGDA_EXTS:
            suffix = f"/{rel}{ext}"
            if path.endswith(suffix):
                return path[: -len(suffix)]
    return posixpath.dirname(path)


def agda_candidate_paths(module: str, root: str) -> List[str]:
    """`X.Y` under `root` → [`root/X/Y.agda`, `root/X/Y.lagda.md`, `root/X/Y.lagda`]; the
    first that exists at the pin is the import's file; none ⇒ a library module."""
    rel = module.replace(".", "/")
    return [f"{root}/{rel}{ext}" for ext in AGDA_EXTS]


def parse_agda_lib(text: str) -> Tuple[List[str], List[str]]:
    """(`include:` directories, `depend:` library names) of an `.agda-lib` file: each
    field is `key: v1 v2 …`, values whitespace-separated, continued on indented lines;
    `--` line comments stripped. Relative directories are relative to the lib file's
    own directory (resolved by the caller)."""
    fields: Dict[str, List[str]] = {}
    cur: Optional[str] = None
    for raw in text.split("\n"):
        ln = raw.split("--", 1)[0].rstrip()
        if not ln.strip():
            continue
        m = re.match(r"^([A-Za-z][\w-]*)\s*:(.*)$", ln)
        if m and not ln[0].isspace():
            cur = m.group(1)
            fields.setdefault(cur, []).extend(m.group(2).split())
        elif cur is not None and ln[0].isspace():
            fields[cur].extend(ln.split())
    return fields.get("include", []), fields.get("depend", [])


_AGDA_LIB_ROOTS_BY_COMMIT: Dict[Tuple[str, str], List[str]] = {}


def agda_lib_roots(repo: Path, commit: str) -> List[str]:
    """Every same-repo Agda include root declared at `commit`: the `include:` directories
    of every `*.agda-lib` under `proofs/` in the pinned tree (`git ls-tree -r`), resolved
    relative to the lib file's directory and normalised, sorted, deduplicated. Memoised
    per (repo, pin). Today (516dfcb): proofs/agda-cubical/qbp-cubical.agda-lib has
    `include: .` → ["proofs/agda-cubical"]; proofs/agda has no .agda-lib (its members
    import only `Agda.*` builtins) and is reached only as a member's OWN root."""
    key = (str(repo), commit)
    if key not in _AGDA_LIB_ROOTS_BY_COMMIT:
        p = _git(repo, "ls-tree", "-r", "--name-only", commit, "--", LEAN_SRC_ROOT)
        roots: set = set()
        for path in p.stdout.split("\n"):
            if not path.endswith(AGDA_LIB_EXT):
                continue
            blob = blob_sha(repo, commit, path)
            if blob is None:  # pragma: no cover — ls-tree just listed it
                raise Refusal(f"{path} listed at {commit[:12]} but unreadable")
            includes, _depends = parse_agda_lib(blob_text(repo, blob))
            for inc in includes:
                roots.add(
                    posixpath.normpath(posixpath.join(posixpath.dirname(path), inc))
                )
        _AGDA_LIB_ROOTS_BY_COMMIT[key] = sorted(roots)
    return _AGDA_LIB_ROOTS_BY_COMMIT[key]


def agda_roots_for(
    repo: Path, commit: str, path: str, module: Optional[str]
) -> List[str]:
    """The roots an Agda member's imports are resolved under, in resolution order: its
    OWN corpus root (`agda_root_of`) first, then every other `.agda-lib` include root at
    the pin (`agda_lib_roots`, sorted). Deterministic; the own root is never dropped even
    when no .agda-lib declares it."""
    own = agda_root_of(path, module)
    return [own] + [r for r in agda_lib_roots(repo, commit) if r != own]


def local_imports_of(
    repo: Path, commit: str, path: str, blob: str, context: str = ""
) -> List[Tuple[str, str]]:
    """The same-repo files `path` (content `blob`, at `commit`) imports, as
    [(dep_path, module)]. `.lean`: header imports through the lakefile-derived module
    map (a dep that does not exist at the pin is left for the caller to refuse);
    `.agda`/`.lagda*`: imports resolved under every same-repo Agda root at the pin
    (`agda_roots_for`: own root first, then the .agda-lib include roots); found ⇒ kept;
    found nowhere ⇒ skipped as a library module ONLY when its first component is in
    `AGDA_EXTERNAL_NAMESPACES`, else a refusal naming the importer, the module and the
    roots searched (`context` names the anchor); anything else (Coq) is a leaf.
    """
    if path.endswith(LEAN_EXT):
        mods = lean_header_imports_of_blob(repo, blob)
        if not mods:
            return []  # nothing to classify: no lakefile needed
        module_map = lake_module_map(repo, commit)
        out: List[Tuple[str, str]] = []
        for m in mods:
            dep = lean_module_path(m, module_map)
            if dep is not None:
                out.append((dep, m))
        return out
    if is_agda_path(path):
        module, mods = agda_scan_of_blob(repo, blob)
        roots = agda_roots_for(repo, commit, path, module)
        found: List[Tuple[str, str]] = []
        for m in mods:
            hit = next(
                (
                    cand
                    for root in roots
                    for cand in agda_candidate_paths(m, root)
                    if blob_sha(repo, commit, cand) is not None
                ),
                None,
            )
            if hit is not None:
                found.append((hit, m))
            elif m.split(".", 1)[0] not in AGDA_EXTERNAL_NAMESPACES:
                raise Refusal(
                    f"{path!r} imports {m!r}, found under none of the same-repo Agda "
                    f"roots at pinned master {commit[:12]} ({', '.join(roots)}) and its "
                    f"namespace {m.split('.', 1)[0]!r} is not a known external library "
                    f"({', '.join(sorted(AGDA_EXTERNAL_NAMESPACES))}){context}; a "
                    "same-repo module the closure cannot see would silently shrink S "
                    "(Gemini on PR #698), so the claim-source manifest is not computed"
                )
        return found
    return []


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
    record can be found without re-running the whole batch."""
    flags: List[str] = []
    where = (
        f" (claim {anchor['id']!r} in record " + ", ".join(record_files) + ")"
        if record_files
        else f" (claim {anchor['id']!r})"
    )
    has_evidence = bool(assistants)
    aid = anchor["id"]
    proof_file = anchor.get("proof_file")
    # seeds: path -> origin ("proof_file" | "evidence_ref"); the closure adds "import"s.
    # seq 2446: every seed is checked to lie inside the proof tree BEFORE it can seed
    # anything; a non-path proof_file (a literature citation) is not a seed at all.
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
    # seq 2394 / QBP#696: S = the transitive closure of the seeds over SAME-REPO imports,
    # read from each member's content AT the pinned commit — Lean through the lakefile-
    # derived module map (every lake library), Agda through every same-repo Agda root at
    # the pin — own corpus root first, then the .agda-lib include roots; an unresolved
    # module outside a known external namespace refuses (`local_imports_of`). Seen-set
    # BFS: a cycle terminates; a file reached twice enters once. A Coq ref is a leaf;
    # library modules (Mathlib / Std / Lean core; the pinned agda / cubical) never enter
    # (lake-manifest pinned, inter#153).
    imported_from: Dict[str, Tuple[str, str]] = (
        {}
    )  # dep path -> (importer path, module)
    sources: List[Dict[str, str]] = []
    seen: set = set()
    queue: List[str] = list(paths)
    while queue:
        path = queue.pop(0)
        if path in seen:
            continue
        seen.add(path)
        blob = blob_sha(repo, commit, path)
        if blob is None:
            origin = paths.get(path, "import")
            if origin == "evidence_ref":
                raise Refusal(
                    f"{aid}: evidence_ref path {path!r} does not exist at pinned "
                    f"master {commit[:12]}{where}; pinned_sha cannot be computed for "
                    "evidence that names a file the pinned tree does not have (S covers "
                    "every same-repo ref of the record, dropped or kept)"
                )
            if origin == "import":
                importer, module = imported_from[path]
                raise Refusal(
                    f"{aid}: {importer!r} imports local module {module!r} → {path!r}, "
                    f"which does not exist at pinned master {commit[:12]}{where}; the "
                    "claim-source manifest S closes over same-repo imports (seq 2394, "
                    "lake-library map per QBP#696) and cannot be computed over a "
                    "dangling import"
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
        sources.append({"path": path, "blob": blob})
        for dep, module in local_imports_of(
            repo, commit, path, blob, f" (anchor {aid}{where})"
        ):
            if dep in seen or dep in paths:
                continue
            imported_from.setdefault(dep, (path, module))
            queue.append(dep)
    sources.sort(key=lambda s_: s_["path"])
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
        # RT C4: S = the QBP-local import closure of proof_file ∪ the CLAIM's same-repo
        # refs (seq 2299 / 2394) — over EVERY assistant of the merged record, BEFORE the
        # target filter. The filter decides
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
            # RT N2 (PR #697): the evidence store's identity — repo + HEAD — so the
            # record is reproducible without out-of-band knowledge; `unknown (not a
            # git checkout)` is written explicitly, never omitted.
            ("evidence_repo", meta["evidence_repo"]),
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
                "imports read at the pinned commit, of {proof_file} ∪ {SAME-REPO "
                "evidence_ref paths — grammar [<owner>/<repo>:]<path>@<commit>#<target>, "
                "no prefix = QBP; cross-repo refs never enter S (seq 2342)} (ruling seq "
                "2394; scope QBP#696). Lean: module → file from proofs/lakefile.lean at "
                "the pin — each lean_lib's roots (default the lib name) + srcDir "
                "(default .) — so `import QBP.A.B` → proofs/QBP/A/B.lean and `import "
                "Sedenion` → proofs/Sprint12-Inherited/Sedenion.lean; a module in no "
                "lake library (Mathlib/Std/Lean/Aesop) is non-local (lake-manifest "
                "pinned, inter#153), skipped; a dangling local import refuses; a "
                "`roots`/`srcDir` field with an expression tail refuses (RT N7). Agda: "
                "`import X.Y` led only by open/private/abstract/instance (RT N8), "
                "anywhere in a .agda/.lagda member, comments stripped, resolved under "
                "EVERY same-repo Agda root at the pin — the member's own corpus root "
                "(proofs/agda, proofs/agda-cubical) first, then every `include:` dir of "
                "every *.agda-lib under proofs/ (X/Y.agda | .lagda.md | .lagda); found "
                "nowhere ⇒ skipped as a library module only if its namespace is in "
                "AGDA_EXTERNAL_NAMESPACES (Agda, Cubical), else refusal naming importer, "
                "module and roots searched (Gemini, PR #698). Seeds outside "
                "proofs/ (absolute, `..`, other prefix) are refused (seq 2446); a "
                "non-path proof_file (citation) is no_proof_file, a missing path-valued "
                "one stale_proof_file. Lines `path <git rev-parse <commit>:path>\\n` "
                "sorted by path; pinned_sha = git hash-object --stdin over the lines "
                "(ruling seq 2299)",
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
    er = meta["evidence_repo"]
    md.append(
        f"| evidence repo (RT N2) | remote `{er['remote']}`; HEAD `{er['head']}`; "
        f"toplevel `{er['toplevel']}` |"
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
            md.append(f"- `{r['id']}` → `{r['pinned_sha']}` ← {lines}")
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


def evidence_repo_identity(evidence_dir: Path) -> Dict[str, str]:
    """{head, remote, toplevel} of the git checkout `evidence_dir` lives in — `git -C
    <dir> rev-parse HEAD`, `remote get-url origin`, `rev-parse --show-toplevel` — so the
    AC4 record names the canonical evidence commit (e.g. inter main `333134c`), not only
    a local path. A directory that is not inside a git checkout records the explicit
    string `unknown (not a git checkout)` in every field; nothing is ever omitted."""

    def q(*args: str) -> Optional[str]:
        p = subprocess.run(
            ["git", "-C", str(evidence_dir), *args],
            capture_output=True,
            text=True,
            check=False,
        )
        s = p.stdout.strip()
        return s if p.returncode == 0 and s else None

    top = q("rev-parse", "--show-toplevel")
    if top is None:
        return OrderedDict(
            [
                ("head", EVIDENCE_REPO_UNKNOWN),
                ("remote", EVIDENCE_REPO_UNKNOWN),
                ("toplevel", EVIDENCE_REPO_UNKNOWN),
            ]
        )
    head = q("rev-parse", "HEAD")
    remote = q("remote", "get-url", "origin")
    return OrderedDict(
        [
            ("head", head if head and HEX40.match(head) else "unknown (no commits)"),
            ("remote", remote or "unknown (no origin remote)"),
            ("toplevel", top),
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
        "evidence_repo": evidence_repo_identity(evidence_dir),
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
    er = rep["evidence_repo"]
    print(
        f"evidence repo: {er['remote']} @ {er['head']} (toplevel {er['toplevel']}); "
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
