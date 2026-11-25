# `tools/lean-toolcheck/` — Lean/Mathlib toolcheck suite (QBP #823 W5)

The base suite for "trust but verify" Lean/Mathlib upgrades (policy of record:
[`docs/lean-version-cadence.md`](../../docs/lean-version-cadence.md)). Version knowledge lives here, not in personas.

```bash
tools/lean-toolcheck/run.sh                    # full suite; results → results/runs/<run-id>/ (gitignored)
tools/lean-toolcheck/run.sh T04 MF02           # subset by file-name prefix
tools/lean-toolcheck/run.sh --update-baseline  # full run; if GREEN, also rewrite the committed results/results-*.{json,md}
```

Each file is one `lake env lean` with cwd = `proofs/` (pins, Lean env and Mathlib `.oleans` are `proofs/`'s), under
`boxrun` (one lease, thermal guard, 8000 MB RSS cap). Needs the pinned `.oleans`; never builds Mathlib, never runs
`lake update`. On CI only: `BOXRUN=none` (refused unless `CI` is set).

| Dir | What | Graded as |
|---|---|---|
| `tests/` | T00–T19: one feature per file, ends in `#print axioms`, inside the pass-file subset · T20: `local notation` + `attribute [local simp]`, outside the subset (compile check only) | T00–T19 must pass: all axioms ⊆ {propext, Classical.choice, Quot.sound}, checker accepts, file inside the subset · T20 `lean-ok` + `subset-refused` |
| `must-fail/` | MF01 sorry/admit · MF02 native_decide · MF03 literal `: True :=` · MF04 false `decide` · MF05 custom `axiom` · MF06 spoofed axiom audit · MF07 same-line site · MF08 interpolation (refused) · MF09 non-ASCII prefix before a same-line site · MF10 form feed / MF11 lone CR in a comment (line-count desync) · MF12 escaped quote before a site · MF13 clean file with a brace in a string (refused) · MF14 `#eval` forges stdout and exits · MF15–MF18 the same forge through user syntax/handlers: `syntax` + `attribute [command_elab]`, `@[inline, command_elab]`, a `macro` that builds `#eval`, `term_elab` · MF19/MF20 the same through a `simproc` (indented; behind `open Nat in`, Mathlib-only import). All are `subset-refused` + `audit-fails` (no `.olean`); MF05 is `audit-nonstd` (the auditor sees `cheat`) · MF21 an indented `simproc_pattern%` that forges the `.olean` itself · MF22 a REAL `axiom cheat` hidden by an `#eval` that forges the `.olean` (both `subset-refused`; the audit alone is fooled, S1) | must be caught **with the expected message**; a must-fail that passes is a suite failure |
| `known-limits/` | KL01 non-literal vacuity · KL02 `Fin.foldl` under `decide` · KL03 checker blind to a `native_decide` after a string containing a comment opener | report-only: "confirmed" / "CHANGED", never a failure |

**Limits, stated plainly.** The vacuity check is **syntactic only**: the foundations checker matches the literal
`: True :=`; `x = x → True` or `(fun _ => True) 3` pass both the checker and the axiom audit (KL01) — only a human
reading the statement catches them. The checker has no rule for a user `axiom`; the axiom audit is the only
detector there (MF05). The checker's comment stripper is also string-blind: after a string containing a
block-comment opener it misses a `native_decide` (KL03; the audit still catches it). A Lean crash (exit ≥ 128)
fails the run and is never retried.

> **Two layers. Neither is sufficient alone. The subset is the PRECONDITION for the structural verdict.**
>
> 1. **Structural verdict.** A pass file's axiom verdict comes from the **PR #829 / issue #827 out-of-process
>    auditor** (`scripts/LeanAxiomAudit.lean`). `run.sh` compiles each file to an `.olean` in a fresh process and
>    runs the auditor on it: `lean --run`, `LEAN_PATH` unset, toolchain library first,
>    `importModules (loadExts := false)`, no initializers, and a nonce drawn after the compile. The result line is
>    graded by **#829's own `grade_run`**: imported, never copied. On top of that, the grader requires compile exit 0,
>    auditor exit 0, an `.olean`, and a scope of exactly this module. The file's own `#print axioms` output is a
>    cross-check only.
> 2. **Pass-file subset.** The structural audit is sound **only if no user code runs during the compile**. The compile
>    is not sandboxed (#829's limit S1, QBP#836). Code that does run can write the very `.olean` the auditor reads:
>    MF21 (Red Team r4 T88) compiles a clean module of the same name to its own `-o` path, and the auditor then
>    reports clean. MF22 (Red Team r4 T86) does the same from an `#eval`, and hides a REAL `axiom cheat`. So, **until QBP#836 adds a sandbox, the subset is the precondition for the verdict, not defense
>    in depth.** The subset rules below must keep every pass file free of code that runs.
>
> **Writing the `.olean` to a path the file cannot predict** does not help. The file reads its own `-o` argument
> from `/proc/self/cmdline` at run time, so any path the runner picks is visible to it. Verifying the `.olean`
> independently would need a second, trusted compile, which is the sandbox again. Both are left to QBP#836, as a
> stated limit. There is no kernel re-check either (lean4checker's job).
>
> **Status: this PR is blocked on PR #829.** Until #829 is on master, a run without `TOOLCHECK_AUDITOR=<PR #829's
> LeanAxiomAudit.lean>` (with `check_lean_axiom_audit.py` beside it) is a **PREFLIGHT FAILURE**, never a
> stdout-only GREEN.

**How the grader reads Lean.** Lean runs with `--json`. An axiom report counts only as an `information` message
positioned at its `#print axioms` command, and reports merge worst-case, so `#eval`-printed text cannot add a clean
report or clear a real one (MF06). Stdout is **not** a trusted channel, so these are **cross-checks** on top of the structural verdict,
each fail-closed for a **pass** file:
exactly one positioned report per `#print axioms` site, no axiom-like message off a site, no stdout line that is not
a Lean message, and the whole file inside the **pass-file subset** below. Sites are found anywhere on a line (MF07),
with the column in Lean's unit — codepoints, pinned by probe and self-test (MF09) — and lines counted Lean's way:
bytes read, only `\r\n` → `\n`, split at `\n` only, never `str.splitlines()` or text-mode universal newlines
(MF10 form feed, MF11 lone CR; pinned by self-test), in source with comments and string bodies blanked by a
nesting-, string- and escape-aware lexer (T19, MF12).

**The pass-file subset** (`subset_violations` in `toolcheck.py`; the minimum T00–T19 need). It is checked on the
code-only text (comments and string bodies blanked, so neither can trigger or hide a rule), one `\n`-line at a time:

| Rule | Allowed | Everything else is refused, e.g. |
|---|---|---|
| **A. top-level commands.** A code line starting in column 0 is a command; after any leading `@[…]` its first word must be allowed. Indented lines are continuations | `import` `namespace` `end` `open` `variable` `set_option` `theorem` `def` `noncomputable def` `instance` `structure` `inductive` `#print axioms` | `axiom`, `section`, `lemma`, `abbrev`, `example`, `alias`, `macro`, `syntax`, `notation`, `attribute`, `local …`, `#check`, any user-defined command |
| **H. command heads, anywhere** (indented, after a term, after `… in`) | the same allowlist as A | **every** leading token of Lean's `command` category: all 232, word or not, from `command_heads.json`. The file is generated by `gen_command_heads.py` from Lean itself, with Lean + the T00 surface loaded, and pinned to the toolchain, the Mathlib sha **and the T00 import list**; **0** unindexed command parsers. Examples: `axiom` `simproc` `example` `section` `local` `deriving instance`, the non-word heads `simproc_pattern%` `compile_def%` (and the other `…%` heads) `$` `?` `#check'`, and any `name%` elaborator token. `@[` is rule C's; `/--` and `/-!` are doc comments, which the lexer blanks |
| **I. `open … in` / `set_option … in`** | followed by an allowed command, on the same line or on the next line in column 0 | `open Nat in simproc …`, `open Nat in <user command>`, a following indented line |
| **B. `#` commands, anywhere** (also mid-line) | `#print axioms` | `#eval`, `#guard`, `#sample`, `#test`, `#check`, `#print <other>` |
| **C. attributes, anywhere.** Every `@[…]` must close on its line; every item, after an optional `scoped`, must be allowed | `simp`, `ext` | `inline`, `local …`, `command_elab`/`term_elab`/`tactic`/`macro`/`init`/`builtin_*` at ANY position in the list |
| **D. keywords, anywhere** (also mid-line) | — | `attribute` `macro` `macro_rules` `syntax` `declare_syntax_cat` `notation` `infix` `infixl` `infixr` `prefix` `postfix` `elab` `elab_rules` `run_cmd` `run_elab` `run_meta` `run_tac` `by_elab` `initialize` `builtin_initialize` `implemented_by` `extern` `unsafe` `native_decide` `+native` `ofReduceBool` `reduceBool` `plausible` `slim_check` `axiom` `simproc` `dsimproc` `simproc_decl` `dsimproc_decl` |

**Limit of the subset, stated plainly:** it is a text scan, not a parser, and it is NOT the soundness boundary
(the structural audit is). It cannot see a command that a module outside the T00 import surface adds
(the pin catches a changed surface), or a token-free command parser (none exists at these pins). Because the
subset is the precondition for the structural verdict (above), these are limits of the verdict too.

> **Coverage, stated plainly: the audit covers the `#print axioms` sites the lexer finds — nothing else. The suite's
> convention is ONE site per theorem.** A theorem without a site is not audited. The lexer does not model string
> interpolation, so a suite file with any brace inside a string literal is **refused** (MF08); write literal braces
> as `\x7B` / `\x7D`. (The real CI gate, QBP#827, does not rely on a Python lexer for coverage: it enumerates
> declarations with Lean itself.) Every expectation regex is matched against one Lean message (`LINE:COL: severity: text`) or one
checker `::error::` line. An empty suite, an empty layer or a prefix that matches nothing is RED.

Grader self-test (planted negative controls on a real run's raw logs): `python3 -I tools/lean-toolcheck/selftest_grader.py tools/lean-toolcheck <results/runs/ID/raw> <workdir>`.

See [`FEATURES.md`](FEATURES.md) (feature table + draft upgrade triage) and [`BASELINE.md`](BASELINE.md) (current
numbers, box conditions, observed flake).
