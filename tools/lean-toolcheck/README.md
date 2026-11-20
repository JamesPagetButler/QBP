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
| `tests/` | T00–T19: one feature per file, ends in `#print axioms` | must pass, all axioms ⊆ {propext, Classical.choice, Quot.sound}, checker accepts |
| `must-fail/` | MF01 sorry/admit · MF02 native_decide · MF03 literal `: True :=` · MF04 false `decide` · MF05 custom `axiom` · MF06 spoofed axiom audit | must be caught **with the expected message**; a must-fail that passes is a suite failure |
| `known-limits/` | KL01 non-literal vacuity · KL02 `Fin.foldl` under `decide` · KL03 checker blind to a `native_decide` after a string containing a comment opener | report-only: "confirmed" / "CHANGED", never a failure |

**Limits, stated plainly.** The vacuity check is **syntactic only**: the foundations checker matches the literal
`: True :=`; `x = x → True` or `(fun _ => True) 3` pass both the checker and the axiom audit (KL01) — only a human
reading the statement catches them. The checker has no rule for a user `axiom`; the axiom audit is the only
detector there (MF05). The checker's comment stripper is also string-blind: after a string containing a
block-comment opener it misses a `native_decide` (KL03; the audit still catches it). A Lean crash (exit ≥ 128)
fails the run and is never retried.

**How the grader reads Lean.** Lean runs with `--json`; only Lean's own message stream is trusted. An axiom report
counts only as an `information` message positioned at its `#print axioms` command, and reports merge worst-case, so
printed text cannot fake or clear an audit (MF06). Expected theorem names come from a nesting- and string-aware
comment lexer (T19). Every expectation regex is matched against one Lean message (`LINE:COL: severity: text`) or one
checker `::error::` line. An empty suite, an empty layer or a prefix that matches nothing is RED.

See [`FEATURES.md`](FEATURES.md) (feature table + draft upgrade triage) and [`BASELINE.md`](BASELINE.md) (current
numbers, box conditions, observed flake).
