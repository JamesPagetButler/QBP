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

`scripts/encode_pa_from_evidence.py` is the only writer of `pa_local` / `pa_effective` / `proof_assistants`. It reads every `*.yaml`/`*.json` under `--evidence-dir` (the default, `/home/prime/Documents/inter/notary-evidence`, is the beekeeper's checkout and is a default only — CI and other checkouts pass `--evidence-dir` explicitly), grades only records in the engine's v2 shape (top-level `claim` + `proof_assistants[]` with `declared{}`/`derived{}` per assistant — `tools/cth-pa/testdata/pa/01_lean_clean.json`), lists everything else as `ignored_non_v2` without reading a grade out of it, projects each assistant onto the engine's own fields verbatim (nothing synthesised, missing fields stay missing so the engine fails closed), keeps only the assistants whose `evidence_ref` `#target` names the anchor's `lean_theorem` or is paired with it by a non-producer correspondence's structured `maps[]` (the rest are dropped with flag `target_not_headline:<assistant>` — a companion cannot lift a headline), computes `pinned_sha` as the claim-source manifest hash (S = {anchor `proof_file`} ∪ {same-repo paths in the claim's `evidence_ref`s — grammar `[<owner>/<repo>:]<path>@<commit>#<target>`, no prefix = QBP; a cross-repo ref must carry a commit and never enters S}; sorted `path <git rev-parse <pinned-master>:path>` lines; `git hash-object --stdin`; architecture ruling live-test seq 2299), builds one `pa.Claim` per target anchor (`provenance_kind ∈ {proof, derivation}` ∪ `PROOF-*`, 147 at 6.13.0) and one `derivation` edge per `prediction_chain` entry whose target is also a target anchor (conservative — only lowers; typed relevance/mention edges come with the Phase-1 chain migration), runs ONE `pa-grade` invocation with `require_signature: false`, and writes the engine's `pa` / `effective_pa` through the confined writer `scripts/cth_ledger_edit.py`. The `proof_assistants` array is written only on proof/derivation anchors with at least one admissible assistant (never `[]`); evidence filed on a non-target anchor is listed as `evidence_for_non_target`, never graded; `internal-compute` anchors (`PROOF-hessian`) get grades and never the array. There is no `--pa` argument and no way to pass a grade in; `scripts/test_pa_encoder.py` pins each of these rules.
