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
| `forbidden_tokens.sh` | the lexical control, **raw text, no comment stripping**; arguments are files or directories — directories are walked recursively (nothing excluded, `_build` included), every source form Agda loads is scanned (`.agda`, `.lagda`, `.lagda.*`, `.agda-lib`) and any symlink under a scanned root is a finding, as in PR #826's script at `45a050e`; (a comment-aware scanner was bypassed twice in the PR #826 review: a `"{-"` string literal and an `a--b` identifier). Token list = `scripts/agda_forbidden_tokens.py` from PR #826 — words `postulate primTrustMe primEraseEquality REWRITE TERMINATING NON_TERMINATING NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK NON_COVERING INJECTIVE`, flags `--type-in-type --rewriting --allow-unsolved-metas --allow-incomplete-matches --no-positivity-check --no-termination-check --omega-in-omega`, holes `{!` — plus `--require-safe` (every file's OPTIONS carries `--safe`). **When `scripts/agda_forbidden_tokens.py` is present in the repo (once PR #826 lands) the scan is delegated to it, so the suite and CI share one scanner**; until then the built-in grep applies the same list. Convention: never write a forbidden token in a gated Agda file, even in a comment (all 17 comply) | exit 0 iff no hit |
| `control/*.agda` | the control's own controls, never type-checked, each with `PLANTED: n`: `PlantedForbidden` (9 — one per forbidden construct, with decoys `postulated`, `rewriting-free`, `--safe`), `B1StringFakeComment` (1 — `s = "{-"` then a let-bound axiom), `B2IdentifierDashDash` (1 — `a--b` then an axiom on the same line) | the scan must yield exactly n hits per fixture or the suite fails |
| project layer | `proofs/agda/*.agda` + `proofs/agda-cubical/*.agda`, run exactly as CI (`cd dir && agda --safe f`), then `forbidden_tokens.sh --require-safe` over them and the three fixture checks | must PASS |
| `MANIFEST` | `layer<TAB>file` for every file the suite must find and run. Suite layers (`tool`, `lib`, `mustfail`, `control`): the found set must **equal** the listed set; project layers (`substrate`, `cubical`): every listed file must be found (new QBP files are allowed and checked). A missing, renamed or empty directory can never go green with zero tests | `manifest-<layer>` control rows PASS |
| `run.sh` | the runner: grader **self-test first** (19 synthetic cases: PASS/FAIL/CRASH, REJECTED/WRONG-ERROR/ACCEPTED incl. empty `EXPECT:` and a message that appears only in the `Checking …` echo, the pin-keyed hole, `ver_ge`), then one `boxrun` scope, `/usr/bin/time` per file. A signal exit (rc ≥ 128) is `CRASH` in every layer and never counts as REJECTED. The `EXPECT:` substring is matched against the error lines only (progress echoes stripped) and must be non-empty | exit 0 iff nothing unexpected |
| `results/runs/<run-id>/` | **every** run's record (`results-<agda>-<cubical7>.{json,md}` + `logs/`), git-ignored | |
| `results/results-<agda>-<cubical7>.{json,md}` | the committed baseline — copied from the run dir by `run.sh --update-baseline` **only after the whole run graded green**; a failed run never touches it (demonstrated in `BASELINE.md` §Demonstrations) | committed |
| `FEATURES.md` | feature table for the current pins + candidate triage for the next upgrade | |
| `BASELINE.md` | the baseline run's table and box conditions | |
| `triage_changelog.py`, `triage_overrides.json`, `triage/` | the R5 changelog-triage generator and its output | |

## Run

```bash
tools/agda-toolcheck/run.sh                   # all layers, wrapped in boxrun (--wait); writes results/runs/<id>/
tools/agda-toolcheck/run.sh --layer lib       # one layer
tools/agda-toolcheck/run.sh --update-baseline # also copy the record to results/results-*.{json,md} — only if green
tools/agda-toolcheck/run.sh --self-test       # grader self-test only (no agda, no boxrun)
TOOLCHECK_MEM_MB=8000 TOOLCHECK_TIMEOUT=3600 tools/agda-toolcheck/run.sh
tools/agda-toolcheck/run.sh --no-boxrun       # CI only (no box lease there)
tools/agda-toolcheck/forbidden_tokens.sh --require-safe proofs/agda proofs/agda-cubical   # the lexical control alone
# test seams (never for a baseline; each disables --update-baseline and is recorded in the JSON):
TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 tools/agda-toolcheck/run.sh --layer mustfail   # F2: LetPostulate must come out ACCEPTED, exit 1
TOOLCHECK_INJECT_FAIL=1 tools/agda-toolcheck/run.sh --layer tool --update-baseline  # (5): exit 1, baseline byte-identical
TOOLCHECK_MANIFEST=<alt> tools/agda-toolcheck/run.sh --layer tool                  # (6): a listed-but-missing file → manifest FAIL
```

Statuses: `PASS` · `FAIL` · `CRASH` (rc ≥ 128) · `REJECTED` · `WRONG-ERROR` (rejected, but not with the `EXPECT:` text, or no `EXPECT:`) · `ACCEPTED` (a must-fail that passed) · `KNOWN-HOLE` / `FIXED` / `FIXED-EARLY` (pin-keyed). Unexpected = `FAIL`, `CRASH`, `WRONG-ERROR`, `ACCEPTED`, plus any manifest / fixture / pin mismatch.

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
