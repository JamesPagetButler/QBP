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
| `forbidden_tokens.sh` | the lexical control as a thin wrapper around the **one** scanner, PR #826's `scripts/agda_forbidden_tokens.py` (raw text, no comment stripping; recursive walk, `.agda`/`.lagda`/`.lagda.*`/`.agda-lib`, symlinks and `.agda-lib` `include:` escapes are findings; built-in must-hit self-test). **Fail-closed: no fallback — if the script is absent the control is FAIL with "requires PR #826's scanner", so #825 merges after #826.** The wrapper adds `--require-safe` (every `.agda`/`.lagda*` file's OPTIONS carries `--safe`). Convention: never write a forbidden token in a gated Agda file, even in a comment (all 17 comply) | exit 0 iff no hit |
| control `no-nested-source` | the gated trees are flat by convention and CI type-checks `*.agda` flat; any `.agda`/`.lagda*` found below the top level of `proofs/agda` or `proofs/agda-cubical` (`_build/` included) is an **unchecked nested source** → FAIL (it is not type-checked by the suite either — exactly one rule, matching CI) | PASS |
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
tools/agda-toolcheck/forbidden_tokens.sh --require-safe proofs/agda proofs/agda-cubical   # the lexical control alone (needs scripts/agda_forbidden_tokens.py)
# test seams — DENY BY DEFAULT: every TOOLCHECK_* variable except MEM_MB/TIMEOUT/TAG is a seam; all are recorded
# in run.test_seams and any of them REFUSES --update-baseline (exit 3 after a green run); an unknown TOOLCHECK_FOO=1 counts too:
TOOLCHECK_FAKE_AGDA_VERSION=2.9.0 tools/agda-toolcheck/run.sh --layer mustfail   # F2: LetPostulate must come out ACCEPTED, exit 1
TOOLCHECK_INJECT_FAIL=1 tools/agda-toolcheck/run.sh --layer tool --update-baseline  # (5): exit 1, baseline byte-identical
TOOLCHECK_MANIFEST=<alt> tools/agda-toolcheck/run.sh --layer tool                  # (6): a listed-but-missing file → manifest FAIL
TOOLCHECK_SHARED_SCANNER=<stub> TOOLCHECK_FOO=1 tools/agda-toolcheck/run.sh --layer tool --update-baseline  # (8): refused, exit 3, baseline untouched
TOOLCHECK_ALLOW_PIN_MISMATCH=1 tools/agda-toolcheck/run.sh                        # candidate run on a non-CI pin: allowed, but a seam → never a baseline
```

A baseline (`--update-baseline`) is written only when the run is green, no `TOOLCHECK_*` seam is set, **and** `pin_match` and `agda_match` are both true — the exact toolchain CI pins. The JSON records `toolchain.binaries` (resolved path + sha256 of `agda`, `python3`, `jq`, `/usr/bin/time` and the scanner script actually used). `TOOLCHECK_TAG` must match `^[A-Za-z0-9_-]{1,32}$`.

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
