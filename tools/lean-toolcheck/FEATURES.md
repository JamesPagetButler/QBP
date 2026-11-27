# Lean toolcheck — feature table for the current pins

**What this is:** the Lean/Mathlib feature surface QBP's proofs rely on, one row per feature, each tied to a
focused test file and to the QBP files that use it (issue #823 W5; policy of record
[`docs/lean-version-cadence.md`](../../docs/lean-version-cadence.md), #489). Version knowledge lives here and in
`BASELINE.md` — not in personas or skills (#823 R1).

**Pins (read from the repo, not hard-coded):** `proofs/lean-toolchain` = `leanprover/lean4:v4.30.0` ·
`proofs/lakefile.lean` Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` (stable tag `v4.30.0`) — as of
this table's date, 2026-11-20. Re-read them before trusting the table.

**How to run:** `tools/lean-toolcheck/run.sh` (all files) or `tools/lean-toolcheck/run.sh T04 MF02` (prefixes),
from any directory. Each file is one `lake env lean` run with cwd = `proofs/` (so the Lean environment, the pins
and the Mathlib `.oleans` are `proofs/`'s), under `boxrun` (lease, thermal guard, RSS cap). A normal run writes
only to `results/runs/<run-id>/` (gitignored); the committed baseline `results/results-<toolchain>-<mathlib-sha7>.{json,md}`
changes only with `run.sh --update-baseline` on a full GREEN run. Exit 0 = every file behaved as expected
(tool tests pass, must-fails caught, known-limit probes reported). Expectation regexes are matched against ONE
Lean message (`LINE:COL: severity: text`) or ONE checker `::error::` line, never the whole log. An empty suite, an
empty layer or an unmatched prefix is RED. A Lean crash (exit ≥ 128) fails the run and is
never retried.

> **Coverage, stated plainly: the suite's axiom audit covers the `#print axioms` sites its lexer finds — nothing else; the
> suite convention is ONE site per theorem.** Sites are found anywhere on a line, in code with comments and string bodies
> blanked. A suite file with a brace inside a string literal is REFUSED (the lexer does not model interpolation; write
> `\x7B`/`\x7D`). The real CI gate (QBP#827) enumerates declarations with Lean itself instead of a Python lexer.

> **Limit, stated plainly: the vacuity check is SYNTACTIC ONLY.** `scripts/check_lean_foundations.py` catches the
> literal `: True :=` (MF03). A vacuous statement in any other spelling (`x = x → True`, the #472 shape behind a
> beta-redex `(fun _ => True) 3`) passes BOTH the checker and the axiom audit; those are pinned as report-only
> KNOWN-LIMIT rows (KL01). Only a human reading the statement catches them. Likewise the checker has no rule for a
> user `axiom`; there the axiom audit is the only detector (MF05).

**Why `tools/`, not `proofs/`:** these are tool tests, not theory. Outside `proofs/` they are not a `lean_lib`,
not in `lake build` (the must-fail controls are meant to fail), not theory-bearing for the Tier-3 gate, and not
scanned by the inverse anchor audit or `scripts/check_layer_imports.py` — with no gate exclusion or baseline
change (director decision on PR #824, option (b)).

Usage counts below are from a comment-stripped grep of `proofs/**/*.lean` (80 files, excluding `.lake/`) on
2026-11-20 at `origin/master` `1892146`.

## 1. Feature table (base suite)

| ID | Feature | Used by (QBP files; count) | Test file | Status @ v4.30.0 / c5ea003 |
|---|---|---|---|---|
| T00 | Mathlib **import surface** — all 65 Mathlib modules QBP imports | every Mathlib-importing QBP file | `tests/T00_ImportSurface.lean` (+ `run.sh` refuses a stale list) | ✅ PASS (all thms ⊆ std3) |
| T01 | kernel `decide` / `decide +kernel` on `Fin n`, `Bool`, `List (Fin n)`; `maxRecDepth` / `maxHeartbeats` | 30 files, 707 uses — `Foundations/SeamSpectrum`, `SeamKernel`, `NoAutonomousDynamics`, `Octonion32Count` (`+kernel`), `FanoGenesis` (`+kernel`), `Breakdown` | `tests/T01_DecideFin.lean` | ✅ PASS (all thms ⊆ std3) |
| T02 | user `Decidable` instances (`unfold; infer_instance`), `deriving DecidableEq`, `Finset.univ.filter` / `card` by `decide` | `Octonion32Count`, `SedenionOctonionCount`, `Breakdown`, `FanoSubalgebras`, `QBPHorizonFoundations` | `tests/T02_DecidableInstances.lean` | ✅ PASS (all thms ⊆ std3) |
| T03 | `fin_cases` (on `Fin n` and on `∈ Finset`) | 6 files — `SeamKernel`, `CDBridge`, `SeamSpectrum`, `HolographicSubalgebra`, `OctonionAutBranching`, `CDAlg` | `tests/T03_FinCases.lean` | ✅ PASS (all thms ⊆ std3) |
| T04 | `ring` / `ring_nf` (ℝ, ℤ, ℚ, generic `CommRing`) | 32 files / 330 uses; `ring_nf` 6 files | `tests/T04_Ring.lean` | ✅ PASS (all thms ⊆ std3) |
| T05 | `field_simp` with explicit `≠ 0` hypotheses | 10 files — `Exp`, `Cosmo/RedshiftEvolution`, `Optics/Fraunhofer`, `SpectralMoments` | `tests/T05_FieldSimp.lean` | ✅ PASS (all thms ⊆ std3) |
| T06 | `linarith`, `nlinarith [hints]`, `positivity` | 20 / 9 / 7 files — `Substrate/RuleFlow*`, `Hosting`, `CDAlg`, `SpectralMoments` | `tests/T06_LinarithPositivity.lean` | ✅ PASS (all thms ⊆ std3) |
| T07 | `norm_num` (+ `Real.sqrt` path), `push_cast`, `exact_mod_cast` | 36 / 18 / 8 files — `Breakdown`, `Alternator`, `OctonionLaws` | `tests/T07_NormNumCasts.lean` | ✅ PASS (all thms ⊆ std3) |
| T08 | `module` tactic, `linear_combination`, `abel` | 16 / 10 / 16 files — `CrystalHosting` (59× `module`), `Substrate/RuleFlow`, `InFlightAlgebra`, `OctonionLaws` | `tests/T08_ModuleLinComb.lean` | ✅ PASS (all thms ⊆ std3) |
| T09 | `simp` family: `simp […]`, `simp only`, `simpa using`, `at h ⊢`, `simp_rw`, `dsimp only`, `@[simp]`, `@[scoped simp]` + `open scoped … in`; the `qJ_sq` Quaternion simp set | 33 (`simp only`) / 39 (bare) / 17 (`simpa`) files; 75 `@[simp]` lemmas; `Experiments/DoubleSlit` `qJ_sq` (broke in PR #491) | `tests/T09_SimpFamily.lean` | ✅ PASS (all thms ⊆ std3) |
| T10 | Mathlib `Quaternion` (`ℍ[ℝ]`, `ext`, `star`, `normSq`, `map_mul`) + constructed non-commutativity witness | 12 files — `TowerLaws`, `DoubleSlit`, `CDBridge`, `Exp`, `UnitQuaternion`, `Hurwitz` | `tests/T10_Quaternion.lean` | ✅ PASS (all thms ⊆ std3) |
| T11 | non-associative hierarchy: coordinate `structure` + `@[ext]`, `AddCommGroup` (`nsmulRec`/`zsmulRec`), `Module`, `NonUnitalNonAssocRing`, `IsScalarTower`, `SMulCommClass`; `decide`d non-associativity witness | `CDAlg` (instances), `ArtinSpan` (`NonUnitalNonAssocRing` + scalar tower), `CDLifting`, `Alternator`, `Breakdown` | `tests/T11_NonAssocHierarchy.lean` | ✅ PASS (all thms ⊆ std3) |
| T12 | big operators over `Fin n`: `Fin.sum_univ_{succ,four,eight}`, `Finset.sum_comm`, `sum_congr`, `sum_add_distrib`, `mul_sum`; closed sum by `decide` | 23 files / 470 uses — `Alternator` (136), `CDAlg`, `CDLifting`, `G2Transitivity`, `SeamSpectrum` | `tests/T12_FinsetSum.lean` | ✅ PASS (all thms ⊆ std3) |
| T13 | real analysis: `Real.sqrt` lemmas, `sin`/`cos`/`π`, `exp`/`log`, `HasDerivAt`, `deriv` | 10 / 8 / 4 / 4 files — `Substrate/RuleFlow`, `Exp`, `Experiments/General3D`, `Optics/Fraunhofer` | `tests/T13_RealAnalysis.lean` | ✅ PASS (all thms ⊆ std3) |
| T14 | linear algebra: `LinearMap` (`→ₗ`, `ker`), `Module.finrank`, `Matrix.det` (2×2), `EuclideanSpace` norm, `Polynomial.eval` | 6 / 4 / 1 / 1 files — `SeamSpectrum`, `SeamKernel`, `TransitionState`, `HolographicSubalgebra`, `LeftMulDet` | `tests/T14_LinearAlgebra.lean` | ✅ PASS (all thms ⊆ std3) |
| T15 | `Complex`: `I_sq`, `ext`, `normSq`, `conj`; "order lost at ℂ" witness | 3 files — `TowerLaws`, `Hurwitz`, `Breakdown` | `tests/T15_Complex.lean` | ✅ PASS (all thms ⊆ std3) |
| T16 | core tactics/decls: `omega`, `rcases`/`obtain`/`rintro`, `induction … with`, `constructor`, `calc`, `unfold`, `show`/`change`, `split_ifs`, `by_contra`, `funext`, `noncomputable def`, `structure` | 11–26 files each — `OctonionAutBranching`, `NoAutonomousDynamics`, `CDLifting`, `DoubleSlit` | `tests/T16_CoreTactics.lean` | ✅ PASS (all thms ⊆ std3) |
| T17 | `Float` / `String` / `IO` API of the differential-test oracle (compile only; nothing `#eval`'d) | `Oracle/FloatCompute`, `Oracle/Main`, `Units/Oracle`, `Units/GenTestVectors` | `tests/T17_FloatOracle.lean` | ✅ PASS (all thms ⊆ std3) |
| T18 | kernel reduction through core `Fin` folds: `Fin.foldr` by `decide`, `Fin.foldl` by `decide +kernel` and by `Fin.foldl_succ` | indirect — the Fin-indexed kernel `decide` sweeps (`Octonion32Count`, `SedenionOctonionCount`, `FanoGenesis`, `SeamSpectrum`); lean4#14267 / #14554 | `tests/T18_FinFold.lean` | ✅ PASS (all thms ⊆ std3) |
| T19 | Lean comment lexing — nested block comments (3 deep), a `#print axioms` line hidden inside one, comment markers inside a string literal | every QBP file with doc or nested comments (the grader reads them all) | `tests/T19_NestedComments.lean` | ✅ PASS (all thms ⊆ std3) |
| T20 | features OUTSIDE the pass-file subset: `local notation` (from T16) and `attribute [local simp]` (from T09) | `notation` 5 files; local simp sets | `tests/T20_SubsetRefusedFeatures.lean` | ✅ compile check only (`lean-ok`) + `subset-refused` confirmed; NOT axiom-graded — QBP's files using these are audited by QBP#827 / PR #829 |
| — | `#print axioms` via `lean --json` (the completeness gate's parser): a report counts only as an `information` message positioned at its `#print axioms` command; reports merge worst-case | 48 files / 1 395 `#print axioms` lines | every test file ends with `#print axioms`; `toolcheck.py` parses them | ✅ parsed for all audited theorems (counts in BASELINE.md) |

### Must-fail controls (a must-fail that passes is a suite FAILURE)

| ID | Control | Must be detected by | Expected message (regex in the file header) | Status |
|---|---|---|---|---|
| MF01 | `sorry`, direct + inherited through a lemma, + `admit` | axiom audit (`sorryAx` on all three theorems) + Lean warning + foundations checker RATCHET (which counts the word `sorry` only — `admit` is caught by the audit alone) | Lean warning "declaration uses sorry" (v4.30.0 quotes it in backticks; regex is quote-agnostic) · `sorryAx` ×3 · `RATCHET violated — sorry: 1 > baseline 0` | ✅ caught (warning + `sorryAx` ×3 + checker) |
| MF02 | `native_decide` | foundations checker HARD-BAN + axiom audit (non-standard axiom, **name-agnostic**) | `HARD-BAN violated — native_decide: 1 occurrence` · axiom ∉ std3 | ✅ caught (checker + axiom `…_native.native_decide.ax_1_1`) |
| MF03 | vacuous, LITERAL `: True := by trivial` and `: True := trivial` | foundations checker HARD-BAN + RATCHET (**the axiom audit is clean — it cannot see vacuity**; the checker sees only this literal spelling — see KL01) | `HARD-BAN violated — vacuous-proof …: 1 occurrence` · `RATCHET violated — vacuous-… theorem: 2 > baseline 0` | ✅ caught by the checker only (axiom audit clean) |
| MF04 | false `decide` (`(2 : Fin 5) + 3 = 1`; `(1 : Int) - 2 = 0`, which is *true* over `Nat`) | Lean rejects (non-zero exit) | `proved that the proposition … is false` (both, line-pinned) | ✅ caught (Lean exit 1, both messages) |
| MF05 | user `axiom cheat : False` + `theorem one_eq_two : 1 = 2 := cheat.elim` | **axiom audit only** (`#print axioms` lists `QBPToolcheck.MF05.cheat`); the foundations checker ACCEPTS the file (recorded as a known limit) | `axiom … ⊇ QBPToolcheck.MF05.cheat` · non-std axiom | ✅ caught by the audit; checker-accepts confirmed |
| MF06 | **spoofed axiom audit**: `spoofed` uses `sorry`; the file then `#eval IO.println`s fake "does not depend on any axioms" lines (before and after the real report, plain and forged-JSON) | axiom audit via `lean --json`: only an `information` message positioned at the `#print axioms` command counts, and reports merge worst-case; + checker RATCHET | `axiom … ⊇ sorryAx` · `^::error::RATCHET violated — sorry: 1 > baseline 0\.` | ✅ caught (3 spoof messages ignored); the pre-fix grader was fooled (reported `[]`) |
| MF07 | **same-line site** (Gemini r2 (b)): `#print axioms clean #print axioms dirty` on ONE line; `dirty` rests on a user axiom | sites found anywhere on a line (column = the `#`); the pre-fix grader only saw line starts and discarded the real report | `axiom … dirty ⊇ QBPToolcheck.MF07.cheat` · non-std | ✅ caught; replayed as a pass-labelled attack in `selftest_grader.py` |
| MF08 | **interpolation desync** (Gemini r2 (c)): `s!" { " /- " } "` makes a non-interpolating lexer see a comment opener in code and blank the rest of the file, hiding `dirty`'s site | the grader REFUSES any file with a brace inside a string literal (supported subset; interpolation is not lexed); on a refused file it audits every axiom report Lean emitted | `grader-refuses` · `axiom … dirty ⊇ QBPToolcheck.MF08.cheat` | ✅ refused and the axiom still reported; replayed as a pass-labelled attack |
| MF09 | **non-ASCII column** (Gemini r3 (e)): `def …αβγ : Nat := 1 #print axioms dirty` — a multi-byte prefix before a same-line site | the site column is computed in Lean's `pos.column` unit (`LEAN_COLUMN_UNIT`) from the ORIGINAL source line; probe on v4.30.0: Lean counts CODEPOINTS (19 vs UTF-8 byte offset 22), so there was no mismatch — the fix is the explicit, self-tested pin | `axiom … dirty ⊇ QBPToolcheck.MF09.cheat` | ✅ caught; `selftest_grader.py` pins the unit on this file's real output and replays it as a pass-labelled attack |
| MF10 | **form-feed line desync** (Gemini r4 (f)): a literal `\f` in the header comment; `run_cmd Lean.logInfo "'…dirty' does not depend on any axioms" #print axioms dirty` after an empty line | lines split at `\n` only (Lean's `FileMap` rule). The pre-fix grader took the site column from `src.splitlines()[ln-1]`, which after the `\f` is the previous (empty) Lean line, so it expected the report at column 0 — the forged `logInfo` — and discarded the real one | `axiom … dirty ⊇ QBPToolcheck.MF10.cheat` | ✅ caught; replayed as a pass-labelled attack; self-test pins Lean's line on the real output |
| MF11 | **lone-CR line desync** (found fixing r4 (f)): a literal lone `\r` in the header comment; `#print axioms dirty` then a forged `run_cmd Lean.logInfo` on the next line | source read as bytes with only Lean's `\r\n` → `\n`; the pre-fix grader's text-mode read turned the lone `\r` into a line break, shifted every site one line down onto the forged message, and discarded the real report | `axiom … dirty ⊇ QBPToolcheck.MF11.cheat` | ✅ caught; replayed as a pass-labelled attack; self-test pins Lean's line on the real output |
| MF12 | **escaped quote before a site** (Red Team M07): `def …s : String := "a\"b" #print axioms dirty` | the lexer honours `\"`; a lexer that ignored escapes would open a new string at the closing quote, hide the site and never audit `dirty` (fail-open) | `axiom … dirty ⊇ QBPToolcheck.MF12.cheat` | ✅ caught |
| MF13 | **clean file, brace in a string** (Red Team M13/M19): honestly proved, but `"a { b"` | the grader REFUSES it; replayed as a pass-labelled file it must FAIL by refusal alone, and with the brace removed from the source copy its `grader-refuses` expectation must FAIL | `grader-refuses` | ✅ refused; both selftest plants FAIL |
| MF14 | **code run during elaboration forges stdout and exits** (Red Team 1(b)): an `#eval` appends a forged clean `--json` report for `dirty` at the `#print axioms` site to `/dev/stdout`, then `IO.Process.exit 0` | the real report is never printed and Lean exits 0, so every stdout rule is satisfied by the forgery (real run: `dirty` graded clean). Only the code-execution refusal (now the pass-file subset) catches it: a pass file may not run code | `subset-refused` | ✅ refused; replayed as a pass-labelled attack: the `19bbbd4` grader PASSES it, the new one FAILS |
| MF15 | **`syntax` + `attribute [command_elab …]`** (Red Team r2 T80): a plain `def` registered as a command handler by the `attribute` command, then the new command; the handler forges a clean report and exits 0 | pass-file subset: rule A (`syntax`, `attribute`, the user command in column 0) and rule D | `subset-refused` | ✅ refused; replay PASSES under `c333116`, FAILS now |
| MF16 | **handler not first in `@[…]`** (T81): `@[inline, command_elab …] def …` | rule C checks EVERY item of every `@[…]` | `subset-refused` | ✅ refused; replay PASSES under `c333116` |
| MF17 | **`macro` builds an `#eval` node** (T82), no import: `mkAtom "#eval"` sits in a string, invisible to a token scan | rules A and D (`macro`) | `subset-refused` | ✅ refused; replay PASSES under `c333116` |
| MF18 | **`term_elab` handler** (T83) fired from inside an ordinary `def` | rules A and D (`syntax`, `attribute`) | `subset-refused` | ✅ refused; replay PASSES under `c333116` |
| MF19 | **indented `axiom` + indented `simproc`** (Red Team r3 T84): the simproc forges the report and exits 0 when `simp only [qbpForge19]` fires | rules H (command keywords anywhere) and D; the STRUCTURAL audit fails it closed (no `.olean`) | `subset-refused` · `audit-fails` | ✅; replay PASSES under `ce7074d`, FAILS now, and FAILS by the structural audit alone with every subset rule off |
| MF20 | **`open Nat in simproc …` at column 0, Mathlib-only import** (T85) | rules A, H, I (`… in` must be followed by an allowed command) and D; structural audit (no `.olean`) | `subset-refused` · `audit-fails` | ✅; as MF19 |
| MF21 | **`simproc_pattern%` forges the `.olean`** (Red Team r4 T88): an INDENTED `simproc_pattern%` (a non-word command head) fires a plain `def` Simproc via `simp only`. In the fresh compile it writes a CLEAN module of the same name to its own `-o` path and exits 0, so the auditor reports clean (#829 limit S1, QBP#836) | rule H now covers EVERY command head, including the non-word ones and any `name%` token. The subset is the precondition for the structural verdict | `subset-refused` | ✅ refused. The replay PASSES under `5b4792e` and FAILS now. With every subset rule off, the audit alone is EXPECTED to be fooled, and the selftest documents that |
| MF22 | **a real `axiom` hidden by a forged `.olean`** (Red Team r4 T86): `dirty` rests on a user `axiom cheat`; an `#eval` reads its own `-o` path, compiles a CLEAN module of the same name there, and exits 0 (in the `--json` run it forges the stdout report, as MF14). The auditor reports no non-standard axiom (S1) | restates the old "auditor alone 6/6" claim: it held only for files that exit before any `.olean` exists. The subset (rules A/H/D `axiom`, rule B `#eval`) is the only detector | `subset-refused` | ✅ refused. With every subset rule off it is EXPECTED to PASS the audit (selftest row `S1-limit[T86s]`) |
| MF23 | **raw-string lexer desync** (Red Team r5 T89): `def rs : String := r"\" simproc_pattern% … -- "`. Lean ends the raw string at the second quote and parses a `simproc_pattern%` command; the `67a214b` Python lexer read `\"` as an escape and blanked it | rule R (raw-string opener refused in the raw source) + the Lean-parser layer (rule L: kind `simproc_pattern%` not allowed; rule P: Lean sees a command start the Python layer does not) | `subset-refused` | ✅ refused. Pass-labelled replay: `67a214b` grader **PASS**, now **FAIL** |
| MF24 | **guillemet lexer desync** (Red Team r5 T90): two `def`s named with guillemets around the block-comment opener/closer, an indented `simproc_pattern%` between them. The `67a214b` lexer read a block comment | rule R (`«` refused) + the Lean-parser layer | `subset-refused` | ✅ refused. Pass-labelled replay: `67a214b` grader **PASS**, now **FAIL** |
| MF25 | **a file that writes a suite input** (Red Team r6 concern 1): an `#eval` appends to `../../subset_kinds.json` relative to its working directory | every code-running Lean process runs in a throwaway copy of the suite; the copy is hashed per file (`suite_copy_writes`); a run-level manifest of every input (suite contents, repo inputs, package and toolchain trees by stat) is verified after the last Lean process | `subset-refused` + `writes-detected` | ✅ the write landed in the COPY's `subset_kinds.json`, was attributed to MF25 only, and the real tree was unchanged (`inputs.verify.json` ok) |
| MF91 | **a detached process that outlives its file** (Red Team r7, its MF91): an `#eval` starts `setsid bash -c '…'`, which heartbeats into its cwd for 60 s and after ~2 s appends to `../../toolcheck.py` (the throwaway copy's) | every Lean process is PID 1 of its own PID namespace (`unshare … --pid --mount-proc --kill-child`); the survivor check re-hashes the throwaway area 1.2 s after the file; the grader runs from a private, manifest-checked copy; inputs are re-verified after grading | `subset-refused` + `writes-detected` | ✅ the daemon dies with the Lean process (heartbeats only while it lived, no late writes). With namespaces OFF (`TOOLCHECK_TEST_NO_PIDNS=1`) the survivor is reported and the run is **INVALID** |

### Known limits (report-only: "confirmed" or "CHANGED", never a failure)

| ID | Limit | Probe | Status @ v4.30.0 |
|---|---|---|---|
| KL01 | **vacuity detection is syntactic**: `theorem refl_implies_true (x : Nat) : x = x → True` and `theorem alternativity : (fun (_ : Nat) => True) 3` (the #472 shape behind a beta-redex) pass the checker AND have a clean `#print axioms` | `known-limits/KL01_VacuityBypass/` (Red Team F3 on PR #824) | 🟡 confirmed (checker exit 0; both `does not depend on any axioms`) |
| KL02 | elaborator `decide` is stuck on `Fin.foldl` ("did not reduce to `isTrue` or `isFalse`"); `decide +kernel` works (T18) | `known-limits/KL02_FinFoldlDecide/` — expected to report CHANGED at the #723 target (lean4#14267, #14554) | 🟡 confirmed |
| KL03 | **the foundations checker's own comment stripper is string-blind**: a string literal containing a block-comment opener makes `scripts/check_lean_foundations.py` delete everything up to the next closer, so a `native_decide` in that span passes its HARD-BAN (the axiom audit still catches it — a hard expectation) | `known-limits/KL03_CheckerStringComment/` (found in the Gemini fix round; this PR changes no gate script) | 🟡 confirmed (checker exit 0; audit shows the native axiom) |

### Project layer (QBP's own proofs)

| Layer | How it is checked on the current pins | Status |
|---|---|---|
| All QBP Lean targets (`QBP`, `QBPSprint12`, `oracle`, `gen_test_vectors`) | CI `lake build (zero errors)` run 41149457423 job 124382272424 — built tree `proofs/` = `ed876f0` = `origin/master` `proofs/` today (PR #787 head `f019660`) | ✅ green (3611 jobs, 0 errors, 0 sorry warnings, 1 383 axiom reports, 0 non-standard) — BASELINE.md §Project layer |

Not covered by an isolated test (rebuild-only): topology/locale API (`LocaleDynamics`: `Order.Nucleus`,
`Topology.Category.Locale`, `Condensed.TopCatAdjunction`), ODE/Gronwall and calculus-of-variations imports
(`Substrate/RuleFlow*`), measure-theory integrals (`IntegralEqImproper`), `MvPolynomial.funext`. They are
in T00's import surface (module paths), and their proofs are checked by the project layer.

## 2. Candidate triage, next upgrade — DRAFT (no bump done)

**Scope:** Lean `v4.30.0` → `v4.36.0` (latest stable on 2026-11-20, released 2026-11-16); cadence target per
P2 = latest stable − 1 = **`v4.35.0`** (Mathlib tag `v4.35.0` = `56a005855ea17e0b0958f73ec801ae140b0a1679`;
`v4.36.0` = `fc4f59e5…` also exists). #823 R2's "newest stable ≈ 2 weeks old" gives the same target today
(v4.36.0 is 4 days old). This is the R5 template for #723; the bump itself is #723's PR.

**Full per-item table:** [`triage/lean-v4.30.0-to-v4.36.0.md`](triage/lean-v4.30.0-to-v4.36.0.md) — every
release-note item, one disposition and one reason each, plus the Mathlib usage scan.

### Counts

| Source | Items | breaking → touches QBP | breaking, no touch | relevant → test | not relevant |
|---|---|---|---|---|---|
| Lean release notes v4.31.0 – v4.36.0 (incl. point releases 4.32.1, 4.32.2, 4.33.1, 4.34.1) | 960 | 8 | 6 | 154 | 792 |
| Mathlib v4.30.0 → v4.35.0, QBP usage only | 3 modules + 1 lemma + 2 index false-positives | 4 (warnings) | — | — | 2 |

**Method (and its limits).** Release notes were read as text from `leanprover/reference-manual`
`Manual/Releases/v4_3*.lean` (the GitHub release bodies only link there). A rule pass assigned each item a
disposition against a usage index of QBP's comment-stripped sources (tactics, identifiers, constructs); about
75 items — every kernel/soundness, transparency/defeq, `Decidable`, `simp`/`simpa`, instance-search, Float and
deprecation item, and every rule-flagged breaking item — were then hand-dispositioned (the `OVERRIDES` in the
generator, reproduced as reasons in the table). The remaining "not relevant" reasons are rule-assigned by
section and keyword (e.g. "Sym/vcgen machinery — QBP does not use it"); they are honest one-liners, not a
line-by-line reading of ~790 items (lean4#14554 was moved to relevant on Red Team review). The Mathlib scan cannot see simp-set *contents* or instance changes —
for those the rebuild (G1) is the test. Generators (re-runnable for the next range; they reproduce the
committed table byte-for-byte): [`triage/tools/`](triage/tools/README.md).

### Top items that will bite #723 (ranked)

| # | Item | Why it bites QBP | Test / migration |
|---|---|---|---|
| 1 | **Kernel soundness point releases** — 4.32.1 (lean4#14498), 4.32.2 (lean4#14577), 4.33.1 (lean4#14806, #14807, #14838, #14582), 4.34.1 (lean4#15289, #15288, #15241) | The pinned v4.30.0 kernel has known paths to `False` (each needs a crafted proof term / in-process metaprogram; honest proofs are not affected, but AI-written proofs are exactly the untrusted-author case). Cadence policy §4.1: "security / correctness advisory → bump immediately regardless of lag". | Target must be ≥ 4.34.1 — v4.35.0 qualifies. MF04 + the rebuild. **Escalated** (see the PR body). |
| 2 | **`Decidable p` becomes a structure** (v4.35.0, lean4#8309) | The object every kernel `decide` reduces. 707 `decide` uses / 30 files; hand-written `Decidable` instances; memory-bound sweeps (`Octonion32Count` 4.6 GiB peak, #633). | T01, T02, T11, T12, MF04; **re-measure peak RSS** of the heavy `decide` modules (R6). |
| 3 | **`simpa using h` closes at reducible transparency** (v4.31.0, lean4#13636) + stricter `@[defeq]` (lean4#13492) + matcher/equation-lemma transparency (lean4#13363, #13512) + `respectTransparency.types` on by default (v4.33.0, lean4#13895) + instance-search transparency (v4.35.0, lean4#14624) | 70 `simpa` (17 files), 75 `@[simp]` lemmas (many `:= rfl`), hand-built instance stacks (`CDAlg`, `ArtinSpan`). Migration notes: `simpa using!`, `set_option backward.defeqAttrib.useBackward true in`, `@[implicit_reducible]`. | T09, T11, T16; rebuild. Migration fixes must stay tactic-only (P3). |
| 4 | **`Lean.ofReduceBool` removed** (v4.35.0, lean4#14953) | `native_decide` is then asserted by per-call axioms. Name-keyed checks go blind; QBP docs/docstrings that say "carries `Lean.ofReduceBool`" (`Sprint12-Inherited/SedenionHessianTraceSq.lean`, `docs/cth/proof-anchor-best-practices.md`, operations-matrix manifest) become stale. `scripts/check_anchor_manifest.py` is subset-based — unaffected. | MF02 is name-agnostic on purpose. Docstring wording is a #723 follow-up. |
| 5 | **Mathlib `deprecated_module`: `Mathlib.Data.Real.Basic`, `.Complex.Basic`, `.Real.Sign` → `Mathlib.Basic.*`** (Mathlib 2026-08-27) | Imported by `CPPhase`, `SpectralAction/ProfileFit`, `Breakdown`, `TowerLaws`, `QBPHorizonFoundations` — and by this suite's own T04–T07, T09, T13, T15, T16. Warnings, not errors. | T00 surfaces it; change the imports on the bump branch. |
| 6 | **Mathlib `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`** (`setOf` → `Set.ofPred`, 2026-07-09) | 3 `simp only` sites in `CrystalHosting` (2) and `Substrate/Hosting` (1). Deprecation warning. | Rename on the bump branch. |
| 7 | `Float` redefined over `Float.Model` (v4.33.0, lean4#14091) | The Float oracle exes. | T17 + CI oracle build. |
| 8 | Defeq/unification heuristics (v4.35.0, lean4#14583); app elaborator beta-reduces (v4.31.0, lean4#13807); `constructor` warns on ambiguity (v4.35.0, lean4#14854) | Elaboration of anything; 182 `show`/`change`, 65 `constructor`. | Rebuild only (no isolated test is possible for heuristics). |

Not a bite: the `v4.36.0`-only items (target is v4.35.0); `grind`/`bv_decide`/`mvcgen`/`Sym`/contracts/`do`
items (QBP uses none); Lake features beyond `build`/`env`/`exe cache get`.

## Change history

| Date | Change |
|---|---|
| 2026-11-20 | v1 — table, must-fail controls, project-layer row, draft triage (issue #823 W5) |
| 2026-11-20 | v1.1 — Red Team fix round on PR #824: MF05 custom axiom; `admit` in MF01; KNOWN-LIMIT rows KL01 (vacuity is syntactic) + KL02 (Fin.foldl `decide`); T18 Fin folds; lean4#14554 reclassified relevant; runs no longer rewrite the committed baseline (`--update-baseline`); preflight robust to a fresh checkout |
| 2026-11-20 | v1.2 — Gemini fix round on PR #824: axiom audit via `lean --json`, position-tied + worst-case merge (MF06 spoof control); nesting-aware comment lexer (T19); expectation regexes anchored to single messages; empty suite / layer / prefix is RED; null-safe file globs |
| 2026-11-20 | v1.3 — Gemini r2: sites found anywhere on a line (MF07); braces inside string literals refused (MF08, interpolation not lexed); string bodies blanked for site detection; coverage statement (lexer-found sites, one per theorem) |
| 2026-11-20 | v1.4 — Gemini r3 (e): probe shows Lean `pos.column` = codepoints; grader computes the column in that unit from the original source line (`LEAN_COLUMN_UNIT`); MF09 + self-test pin; `#eval` output confirmed positioned at its own command |
| 2026-11-24 | v1.5 — Gemini r4 (f): probe shows Lean v4.30.0 breaks lines at `\n` only (`\r\n` normalised; lone `\r`, `\f`, `\v`, `\x1c`–`\x1e`, `\x85`, U+2028/9 are not breaks); grader reads bytes, applies only `\r\n` → `\n`, splits at `\n` everywhere (`read_lean_source` / `lean_lines`); MF10 (form feed) + MF11 (lone CR) + self-test line-rule pins. Red Team (19bbbd4): stdout is not a trusted channel, so pass files are graded fail-closed — one report per site, none unpositioned, no non-Lean stdout, no code-executing construct (`EXEC_RE`, MF14); MF12 escaped quote; MF13 clean-brace refusal; MF09 gains an astral `𝔽` (pins codepoints vs UTF-16 too); guard-dependent selftest plants; `mutants_grader.py` (24/25 killed, M04 equivalent) |
| 2026-11-25 | v1.6 — Red Team r2 (`c333116`): the `EXEC_RE` denylist is replaced by the pass-file SUBSET (column-0 command allowlist, `#print axioms` as the only `#` command, attribute allowlist checked item by item, refused syntax/handler/evaluation keywords anywhere); +MF15–MF18 (T80–T83); `local notation` (T16) and `attribute [local simp]` (T09) moved to T20, a compile-only file outside the subset; 42 per-construct selftest plants; mutants per rule and per list entry; a toolcheck PASS is stated NOT to be an axiom certificate (QBP#827 / PR #829) |
| 2026-11-25 | v1.7 — Red Team r3 (`ce7074d`) + director ruling: the axiom VERDICT for pass files is now STRUCTURAL — the PR #829 auditor (`scripts/LeanAxiomAudit.lean`) on an `.olean` compiled in a fresh process (`structural_audit`); the token subset is defense in depth: rule H (every command keyword at any position, keyword set generated from Lean: `command_heads.json`), rule I (`… in` combinators), `axiom`/simprocs denied; +MF19/MF20 (T84/T85); MF05 `audit-nonstd`; MF14–MF20 `audit-fails`; structural-only selftest (all subset rules off); audit-guard plants; rule-isolation unit checks; PR blocked on #829 |
| 2026-11-25 | v1.8 — Red Team r4 pre-check (`5b4792e`): rule H keeps EVERY Lean command head, including the 14 non-word ones (`simproc_pattern%`, `$`, `?`, `#check'`, …), plus any `name%` token; +MF21 (T88: forged `.olean`); the layering is restated (the subset is the PRECONDITION for the structural verdict until QBP#836); `structural_audit` calls #829's own `grade_run` (no copy; `dangling` is now checked) plus compile/auditor exit 0; the rule-H pin includes the T00 import list; re-integrated against #829 @ `6b07147` |
| 2026-11-25 | v1.9 — Red Team r5 delta (`67a214b`) + director decision: the subset PRECONDITION now comes from Lean's own parser (`LeanSubsetParse.lean`, parse only; rules L/P in `lean_parse_subset`; allowlist `subset_kinds.json` generated by `gen_subset_kinds.py` from the tool tests). Rule R refuses raw strings and `«`. +MF23 (T89), +MF24 (T90). The PR #829 auditor files are pinned by sha256 (`auditor_pin.json`) |
| 2026-11-25 | v1.10 — Red Team r6 (`9c61306`, APPROVE-WITH-CONCERN): cross-run persistence: throwaway suite copy per code-running Lean process with per-file write attribution, a pre/post input manifest held in memory by `run.sh` (now one function), grade-time re-hash; +MF25; the Lean-parser record schema is required and typed (`HEADER_FIELDS`/`COMMAND_FIELDS`/`DONE_FIELDS`) |
| 2026-11-26 | v1.11 — Red Team r7 (`7955bb8`, CHANGES REQUESTED, MF91): per-Lean-process PID namespaces (`unshare --user --map-root-user --fork --pid --mount-proc --kill-child`; preflight failure if unavailable); per-file survivor check (`late_writes`); grader run from a private manifest-checked copy; inputs re-verified after grading; baseline copy sha-checked; `tree_digest` also stats symlink targets; `main "$@"; exit $?` on one line; +MF91 |
