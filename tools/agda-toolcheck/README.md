# agda-toolcheck — the Agda toolchain baseline suite (QBP#823 W1)

"Trust but verify" for the prover toolchain: a **base suite** that pins what
QBP's Agda proofs rely on, run on the *current* pins, so any future Agda or
agda/cubical move can be checked against a recorded baseline. Personas carry
no version numbers; **this directory and the `agda` skill are where version
knowledge lives.**

The suite lives under `tools/`, not `proofs/`: a tool test is not a theory
statement, so it must trip neither the Tier-3 theory gate nor the anchor
audits that watch `proofs/**`. It still runs the real QBP proofs where they
live (the project layer below).

The pins are read from the repo, never assumed:

| what | file |
|---|---|
| Agda version | `.github/workflows/agda-cubical.yml`, `agda-substrate.yml` (the bindist URL) |
| agda/cubical commit | `.github/workflows/agda-cubical.yml` (`git checkout <sha>`) |
| library name + flags | `proofs/agda-cubical/qbp-cubical.agda-lib` |

## Layout

| path | layer | expectation |
|---|---|---|
| `tool/*.agda` | builtins only (`--cubical --safe`, no library) — one file per core feature | must PASS |
| `lib/*.agda` | pinned agda/cubical — one file per library module QBP imports, checking the symbols QBP uses with their types (`lib/qbp-toolcheck-lib.agda-lib` depends on `cubical-0.9`) | must PASS |
| `mustfail/*.agda` | negative controls; each header carries `-- EXPECT: <error substring>` | must be REJECTED with that message. A `MUSTFAIL-KNOWN-HOLE` file also carries `FIXED-IN: <Agda version>`: on a pin below it, acceptance is KNOWN-HOLE (reported, not a failure); on a pin at/after it, acceptance is **a suite failure** (regression) and rejection is FIXED |
| `forbidden_tokens.sh` | the lexical control, **raw text, no comment stripping** (a comment-aware scanner was bypassed twice in the PR #826 review: a `"{-"` string literal and an `a--b` identifier). Token list = `scripts/agda_forbidden_tokens.py` from PR #826 — words `postulate primTrustMe primEraseEquality REWRITE TERMINATING NON_TERMINATING NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK NON_COVERING INJECTIVE`, flags `--type-in-type --rewriting --allow-unsolved-metas --allow-incomplete-matches --no-positivity-check --no-termination-check --omega-in-omega`, holes `{!` — plus `--require-safe` (every file's OPTIONS carries `--safe`). **When `scripts/agda_forbidden_tokens.py` is present in the repo (once PR #826 lands) the scan is delegated to it, so the suite and CI share one scanner**; until then the built-in grep applies the same list. Convention: never write a forbidden token in a gated Agda file, even in a comment (all 17 comply) | exit 0 iff no hit |
| `control/*.agda` | the control's own controls, never type-checked, each with `PLANTED: n`: `PlantedForbidden` (9 — one per forbidden construct, with decoys `postulated`, `rewriting-free`, `--safe`), `B1StringFakeComment` (1 — `s = "{-"` then a let-bound axiom), `B2IdentifierDashDash` (1 — `a--b` then an axiom on the same line) | the scan must yield exactly n hits per fixture or the suite fails |
| project layer | `proofs/agda/*.agda` + `proofs/agda-cubical/*.agda`, run exactly as CI (`cd dir && agda --safe f`), then `forbidden_tokens.sh --require-safe` over them and the three fixture checks | must PASS |
| `run.sh` | the runner (one `boxrun` scope, `/usr/bin/time` per file) | exit 0 iff nothing unexpected |
| `results/results-<agda>-<cubical7>.{json,md}` | the committed baseline record (per file: status, rc, wall s, max RSS) — written **only** by `run.sh --update-baseline`; an ordinary run writes to `results/runs/<run-id>/` (git-ignored) | committed |
| `FEATURES.md` | feature table for the current pins + candidate triage for the next upgrade | |
| `BASELINE.md` | the baseline run's table and box conditions | |
| `triage_changelog.py`, `triage_overrides.json`, `triage/` | the R5 changelog-triage generator and its output | |

## Run

```bash
tools/agda-toolcheck/run.sh                   # all layers, wrapped in boxrun (--wait); writes results/runs/<id>/
tools/agda-toolcheck/run.sh --layer lib       # one layer
tools/agda-toolcheck/run.sh --update-baseline # deliberate: rewrite the committed results/results-*.{json,md}
TOOLCHECK_MEM_MB=8000 TOOLCHECK_TIMEOUT=3600 tools/agda-toolcheck/run.sh
tools/agda-toolcheck/run.sh --no-boxrun       # CI only (no box lease there)
TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 tools/agda-toolcheck/run.sh --layer mustfail   # grading test only: must exit 1 (LetPostulate ACCEPTED)
```

Exit codes: `0` green · `1` unexpected result(s) (see the table) · `2` usage /
missing tool · `87` RSS cap hit · `124` deadline · `75` box busy.

## Upgrading (R4) — what to do with this suite

1. Candidate named → fetch the changelogs with `gh api` (see FEATURES.md
   "How this triage was produced") and regenerate the triage table.
2. Every item in a bucket; relevant → a test in `tool/` or `lib/`
   (the **new-feature suite**), breaking → the named usage checked.
3. On an upgrade branch: bump the pins in the files above, re-run `run.sh`,
   compare `results/` against `BASELINE.md` (a big slowdown is a finding, R6),
   flip any `KNOWN-HOLE` that became `FIXED`, re-pin any `WRONG-ERROR`.
4. Commit the new `results-*.json` as the next baseline.
