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
| T09 | `simp` family: `simp […]`, `simp only`, `simpa using`, `at h ⊢`, `simp_rw`, `dsimp only`, `@[simp]`, `attribute [local simp]`, `@[scoped simp]` + `open scoped … in`; the `qJ_sq` Quaternion simp set | 33 (`simp only`) / 39 (bare) / 17 (`simpa`) files; 75 `@[simp]` lemmas; `Experiments/DoubleSlit` `qJ_sq` (broke in PR #491) | `tests/T09_SimpFamily.lean` | ✅ PASS (all thms ⊆ std3) |
| T10 | Mathlib `Quaternion` (`ℍ[ℝ]`, `ext`, `star`, `normSq`, `map_mul`) + constructed non-commutativity witness | 12 files — `TowerLaws`, `DoubleSlit`, `CDBridge`, `Exp`, `UnitQuaternion`, `Hurwitz` | `tests/T10_Quaternion.lean` | ✅ PASS (all thms ⊆ std3) |
| T11 | non-associative hierarchy: coordinate `structure` + `@[ext]`, `AddCommGroup` (`nsmulRec`/`zsmulRec`), `Module`, `NonUnitalNonAssocRing`, `IsScalarTower`, `SMulCommClass`; `decide`d non-associativity witness | `CDAlg` (instances), `ArtinSpan` (`NonUnitalNonAssocRing` + scalar tower), `CDLifting`, `Alternator`, `Breakdown` | `tests/T11_NonAssocHierarchy.lean` | ✅ PASS (all thms ⊆ std3) |
| T12 | big operators over `Fin n`: `Fin.sum_univ_{succ,four,eight}`, `Finset.sum_comm`, `sum_congr`, `sum_add_distrib`, `mul_sum`; closed sum by `decide` | 23 files / 470 uses — `Alternator` (136), `CDAlg`, `CDLifting`, `G2Transitivity`, `SeamSpectrum` | `tests/T12_FinsetSum.lean` | ✅ PASS (all thms ⊆ std3) |
| T13 | real analysis: `Real.sqrt` lemmas, `sin`/`cos`/`π`, `exp`/`log`, `HasDerivAt`, `deriv` | 10 / 8 / 4 / 4 files — `Substrate/RuleFlow`, `Exp`, `Experiments/General3D`, `Optics/Fraunhofer` | `tests/T13_RealAnalysis.lean` | ✅ PASS (all thms ⊆ std3) |
| T14 | linear algebra: `LinearMap` (`→ₗ`, `ker`), `Module.finrank`, `Matrix.det` (2×2), `EuclideanSpace` norm, `Polynomial.eval` | 6 / 4 / 1 / 1 files — `SeamSpectrum`, `SeamKernel`, `TransitionState`, `HolographicSubalgebra`, `LeftMulDet` | `tests/T14_LinearAlgebra.lean` | ✅ PASS (all thms ⊆ std3) |
| T15 | `Complex`: `I_sq`, `ext`, `normSq`, `conj`; "order lost at ℂ" witness | 3 files — `TowerLaws`, `Hurwitz`, `Breakdown` | `tests/T15_Complex.lean` | ✅ PASS (all thms ⊆ std3) |
| T16 | core tactics/decls: `omega`, `rcases`/`obtain`/`rintro`, `induction … with`, `constructor`, `calc`, `unfold`, `show`/`change`, `split_ifs`, `by_contra`, `funext`, `noncomputable def`, `structure`, local `notation` | 11–26 files each — `OctonionAutBranching`, `NoAutonomousDynamics`, `CDLifting`, `DoubleSlit` | `tests/T16_CoreTactics.lean` | ✅ PASS (all thms ⊆ std3) |
| T17 | `Float` / `String` / `IO` API of the differential-test oracle (compile only; nothing `#eval`'d) | `Oracle/FloatCompute`, `Oracle/Main`, `Units/Oracle`, `Units/GenTestVectors` | `tests/T17_FloatOracle.lean` | ✅ PASS (all thms ⊆ std3) |
| T18 | kernel reduction through core `Fin` folds: `Fin.foldr` by `decide`, `Fin.foldl` by `decide +kernel` and by `Fin.foldl_succ` | indirect — the Fin-indexed kernel `decide` sweeps (`Octonion32Count`, `SedenionOctonionCount`, `FanoGenesis`, `SeamSpectrum`); lean4#14267 / #14554 | `tests/T18_FinFold.lean` | ✅ PASS (all thms ⊆ std3) |
| T19 | Lean comment lexing — nested block comments (3 deep), a `#print axioms` line hidden inside one, comment markers inside a string literal | every QBP file with doc or nested comments (the grader reads them all) | `tests/T19_NestedComments.lean` | ✅ PASS (all thms ⊆ std3) |
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
