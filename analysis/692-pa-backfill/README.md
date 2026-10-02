# QBP#692 — PA backfill records

Each run of the PA encoder leaves one pair of files here:

| file | what |
|---|---|
| `backfill-<date>.md` | the AC4 before/after table for every target anchor (id, provenance_kind, before pa_local/pa_effective or `—`, after, assistants, flags, pinned_sha), the drop list (any decrease vs the committed value), AC3 spot values, the `ignored_non_v2` and `unmatched_claim` lists, pinned master commit, engine pin, and the per-anchor pinned_sha manifests (S + per-file blobs) |
| `backfill-<date>.json` | the same, machine-readable (`anchors[]` rows carry `sources`, `pinned_sha`, `evidence_files`, engine `flags`) |

`pinned_sha`, S and the blobs live HERE and not in the ledger (no ledger home at schema 0.3.5; the `pa-reconcile` CI job re-derives them the same way).

## Re-run

```
cd /home/prime/Documents/QBP            # or the worktree
git fetch origin master
python3 scripts/encode_pa_from_evidence.py --pinned-master origin/master [--dry-run]
```

Exit 0 = grades written (ledger version minor-bumped, one changelog entry); exit 1 = already applied (every target anchor carries exactly the computed grades; nothing written); any `REFUSED:` message = a stop with the reason (unresolvable evidence_ref path, ambiguous correspondence, schema-invalid assistant entry, engine failure). Needs `go` (builds `tools/cth-pa/cmd/pa-grade` once per run), `git`, `pyyaml`, `jsonschema`. Tests: `python3 -m pytest scripts/test_pa_encoder.py -v`. Badge: `python3 scripts/render_pa_badge.py --anchor <id>` / `--all`.

Re-run when the v2 cycle 7/8 notary records (hessian independent recomputation; Fano Coq cross-prover + Lean side with correspondence) are promoted into `inter/notary-evidence/` — until then every target anchor is honestly 0/0.

## Encoder

`scripts/encode_pa_from_evidence.py` is the only writer of `pa_local` / `pa_effective` / `proof_assistants`. It reads every `*.yaml`/`*.json` under `--evidence-dir` (the default, `/home/prime/Documents/inter/notary-evidence`, is the beekeeper's checkout and is a default only — CI and other checkouts pass `--evidence-dir` explicitly), grades only records in the engine's v2 shape (top-level `claim` + `proof_assistants[]` with `declared{}`/`derived{}` per assistant — `tools/cth-pa/testdata/pa/01_lean_clean.json`), lists everything else as `ignored_non_v2` without reading a grade out of it, projects each assistant onto the engine's own fields verbatim (nothing synthesised, missing fields stay missing so the engine fails closed), keeps only the assistants that attest the anchor's headline (the **commit-9 guard rule**, `filter_assistants_by_target` — see below), computes `pinned_sha` as the claim-source manifest hash (S = {anchor `proof_file`} ∪ {same-repo paths in the claim's `evidence_ref`s — grammar `[<owner>/<repo>:]<path>@<commit>#<target>`, no prefix = QBP; a cross-repo ref must carry a commit and never enters S}; sorted `path <git rev-parse <pinned-master>:path>` lines; `git hash-object --stdin`; architecture ruling live-test seq 2299), builds one `pa.Claim` per target anchor (`provenance_kind ∈ {proof, derivation}` ∪ `PROOF-*`, 147 at 6.13.0) and one `derivation` edge per `prediction_chain` entry whose target is also a target anchor (conservative — only lowers; typed relevance/mention edges come with the Phase-1 chain migration), runs ONE `pa-grade` invocation with `require_signature: false`, and writes the engine's `pa` / `effective_pa` through the confined writer `scripts/cth_ledger_edit.py`. The `proof_assistants` array is written only on proof/derivation anchors with at least one admissible assistant (never `[]`); evidence filed on a non-target anchor is listed as `evidence_for_non_target`, never graded; `internal-compute` anchors (`PROOF-hessian`) get grades and never the array. There is no `--pa` argument and no way to pass a grade in; `scripts/test_pa_encoder.py` pins each of these rules.

### Guard rule (commit 9 of PR #695; §I4 seq 2367/2372, cth seq 2371, Red Team C5/C6/N11/N14)

An assistant counts toward an anchor only if it attests **that** anchor's `lean_theorem`, by exactly one of two routes:

| route | who | condition |
|---|---|---|
| **direct match** | the `lean4` assistant with a **same-repo** `evidence_ref` — and nobody else | `#target` is fully qualified and `== lean_theorem` verbatim, **or** `#target` is a short (dot-free) name equal to `lean_theorem`'s last dotted component **and** the ref's path `== proof_file` (a short name identifies the headline only inside the headline's own file) |
| **correspondence `maps`** | an assistant of a **different prover** than the headline's — Coq/Agda, local or cross-repo — and never `lean4` | the record's correspondence has `corresponds: true`, a non-empty `checked_by` that is no assistant's `producer`, and a structured `maps: [{target, lean_theorem}]` entry equal to this assistant's `#target` and this anchor's `lean_theorem` **verbatim** (no short-name relaxation inside `maps`) |
| **kernel collapse** (commit 10; Red Team C7, architecture seq 2386) | every survivor of the two routes above | the engine's `GradeClaim` counts clean *assistants*, not kernels, so the survivors are collapsed to the **first** admissible assistant per prover kind (`assistant` field) before the engine Claim and the ledger array are built; each later same-kind survivor is dropped with flag `same_kernel_duplicate:<kind>` — `[coq, coq]` (or one Coq entry listed twice) with no `lean4` grades 1, never 2; Fano `lean4` + `coq` stays 2 (`collapse_to_one_per_kernel`, one function) |

Everything else is dropped before the engine with report flag `target_not_headline:<assistant>` and is listed per anchor in the report's "Target filter" section. **Why `maps` is cross-prover only — kernel diversity:** a correspondence attests that a *different* kernel checked the same statement. A Lean theorem that is not `lean_theorem` is a different Lean statement, and a map from it to the headline carries zero kernel diversity — it is a declared Lean→Lean derivation (a chain edge, never a PA record), so it cannot lift the headline whether the Lean file is in QBP or in another repo (`maps_may_rescue`, one function; repo-locality is a provenance axis — `cross_repo_evidence`, S, staleness — never a maps criterion). An anchor with no `lean_theorem` admits nothing by either route (flag `no_lean_theorem`, counted — 22 at 6.16.0). Grammar: `[<owner>/<repo>:]<path>@<commit>#<target>`; no prefix or the self-prefix `JamesPagetButler/QBP:` (any casing) = this repo and enters S; a cross-repo ref must carry a 7–40 hex `@<commit>` and never enters S. S is taken over **every** same-repo ref of the record before the filter, so a dropped companion never shrinks the manifest; a same-repo path that does not exist at the pinned master is a refusal that names the anchor, the claim and the evidence record file.

### The committed record

The committed `backfill-2026-10-02.*` pair is the genuine 6.15.0 → 6.16.0 record and was produced by the **commit-4 encoder run**; its JSON predates and therefore lacks `evidence_for_non_target`, `target_filter`, `dropped_assistants` and `targets_without_lean_theorem`. **Do not re-run the encoder to "refresh" it.** A `--dry-run` writes to scratch (removed at exit; pass `--report <path>` to keep one) and never touches this directory; a real re-run that changes grades is a **new backfill with its own dated report**, reviewed as such — the AC4 before/after table is the record of the last applied run, not a file to be regenerated in place.
