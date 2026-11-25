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
| `must-fail/` | MF01 sorry/admit · MF02 native_decide · MF03 literal `: True :=` · MF04 false `decide` · MF05 custom `axiom` · MF06 spoofed axiom audit · MF07 same-line site · MF08 interpolation (refused) · MF09 non-ASCII prefix before a same-line site · MF10 form feed / MF11 lone CR in a comment (line-count desync) · MF12 escaped quote before a site · MF13 clean file with a brace in a string (refused) · MF14 `#eval` forges stdout and exits · MF15–MF18 the same forge through user syntax/handlers: `syntax` + `attribute [command_elab]`, `@[inline, command_elab]`, a `macro` that builds `#eval`, `term_elab` (all `subset-refused`) | must be caught **with the expected message**; a must-fail that passes is a suite failure |
| `known-limits/` | KL01 non-literal vacuity · KL02 `Fin.foldl` under `decide` · KL03 checker blind to a `native_decide` after a string containing a comment opener | report-only: "confirmed" / "CHANGED", never a failure |

**Limits, stated plainly.** The vacuity check is **syntactic only**: the foundations checker matches the literal
`: True :=`; `x = x → True` or `(fun _ => True) 3` pass both the checker and the axiom audit (KL01) — only a human
reading the statement catches them. The checker has no rule for a user `axiom`; the axiom audit is the only
detector there (MF05). The checker's comment stripper is also string-blind: after a string containing a
block-comment opener it misses a `native_decide` (KL03; the audit still catches it). A Lean crash (exit ≥ 128)
fails the run and is never retried.

> **A toolcheck PASS is NOT an axiom certificate.** It says: Lean accepted the file, every `#print axioms` site
> reported only {propext, Classical.choice, Quot.sound}, and the file stays inside a small supported subset of
> Lean. Code a file defines or runs can forge Lean's stdout and exit before the real report (MF14–MF18), so no
> stdout-based audit is sound outside that subset. **The sound audit is out-of-process: QBP#827 / PR #829.**

**How the grader reads Lean.** Lean runs with `--json`. An axiom report counts only as an `information` message
positioned at its `#print axioms` command, and reports merge worst-case, so `#eval`-printed text cannot add a clean
report or clear a real one (MF06). Stdout is **not** a trusted channel, so a **pass** file is graded fail-closed:
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
| **B. `#` commands, anywhere** (also mid-line) | `#print axioms` | `#eval`, `#guard`, `#sample`, `#test`, `#check`, `#print <other>` |
| **C. attributes, anywhere.** Every `@[…]` must close on its line; every item, after an optional `scoped`, must be allowed | `simp`, `ext` | `inline`, `local …`, `command_elab`/`term_elab`/`tactic`/`macro`/`init`/`builtin_*` at ANY position in the list |
| **D. keywords, anywhere** (also mid-line) | — | `attribute` `macro` `macro_rules` `syntax` `declare_syntax_cat` `notation` `infix` `infixl` `infixr` `prefix` `postfix` `elab` `elab_rules` `run_cmd` `run_elab` `run_meta` `run_tac` `by_elab` `initialize` `builtin_initialize` `implemented_by` `extern` `unsafe` `native_decide` `+native` `ofReduceBool` `reduceBool` `plausible` `slim_check` |

**Limit of the subset, stated plainly:** there is no Lean parser here. A command imported from Mathlib/Batteries
that is placed mid-line after a term (not in column 0) is caught only if rule B or D names it.

> **Coverage, stated plainly: the audit covers the `#print axioms` sites the lexer finds — nothing else. The suite's
> convention is ONE site per theorem.** A theorem without a site is not audited. The lexer does not model string
> interpolation, so a suite file with any brace inside a string literal is **refused** (MF08); write literal braces
> as `\x7B` / `\x7D`. (The real CI gate, QBP#827, does not rely on a Python lexer for coverage: it enumerates
> declarations with Lean itself.) Every expectation regex is matched against one Lean message (`LINE:COL: severity: text`) or one
checker `::error::` line. An empty suite, an empty layer or a prefix that matches nothing is RED.

Grader self-test (planted negative controls on a real run's raw logs): `python3 -I tools/lean-toolcheck/selftest_grader.py tools/lean-toolcheck <results/runs/ID/raw> <workdir>`.

See [`FEATURES.md`](FEATURES.md) (feature table + draft upgrade triage) and [`BASELINE.md`](BASELINE.md) (current
numbers, box conditions, observed flake).
