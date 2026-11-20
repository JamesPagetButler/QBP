# agda-toolcheck — the Agda toolchain baseline suite (QBP#823 W1)

"Trust but verify" for the prover toolchain: a **base suite** that pins what
QBP's Agda proofs rely on, run on the *current* pins, so any future Agda or
agda/cubical move can be checked against a recorded baseline. Personas carry
no version numbers; **this directory and the `agda` skill are where version
knowledge lives.**

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
| `mustfail/*.agda` | negative controls; each header carries `-- EXPECT: <error substring>` | must be REJECTED with that message; a `MUSTFAIL-KNOWN-HOLE` file is reported KNOWN-HOLE / FIXED |
| project layer | `proofs/agda/*.agda` + `proofs/agda-cubical/*.agda`, run exactly as CI (`cd dir && agda --safe f`) plus the `no-forbidden-token` lexical control | must PASS |
| `run.sh` | the runner (one `boxrun` scope, `/usr/bin/time` per file) | exit 0 iff nothing unexpected |
| `results/results-<agda>-<cubical7>.{json,md}` | the baseline record (per file: status, rc, wall s, max RSS) | committed |
| `FEATURES.md` | feature table for the current pins + candidate triage for the next upgrade | |
| `BASELINE.md` | the baseline run's table and box conditions | |
| `triage_changelog.py`, `triage_overrides.json`, `triage/` | the R5 changelog-triage generator and its output | |

## Run

```bash
proofs/agda-toolcheck/run.sh                 # all layers, wrapped in boxrun (--wait)
proofs/agda-toolcheck/run.sh --layer lib     # one layer
TOOLCHECK_MEM_MB=8000 TOOLCHECK_TIMEOUT=3600 proofs/agda-toolcheck/run.sh
proofs/agda-toolcheck/run.sh --no-boxrun     # CI only (no box lease there)
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
