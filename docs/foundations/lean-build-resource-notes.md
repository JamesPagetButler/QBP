# Lean build resource notes — per-module peak RSS (pre-run resource estimate table)

Workspace hard gate `pre-run-resource-estimate` (`~/Documents/CLAUDE.md`): before launching a
long-running compute job, write down an upper bound for RAM and disk and confirm headroom; if the
estimate exceeds 50 % of what is available, launch under a kill condition. For Lean this means
`run-bounded <mem> <sec> lake build …` / `… lean <file>` (rootless cgroup `MemoryMax` + `timeout`),
and *this table* is the written estimate. The Lean CI job (`.github/workflows/lean-foundations.yml`,
`lake build` step) points here.

## How a row is measured

```
cd <worktree>/proofs
export LEAN_PATH="$(cd <main-checkout>/proofs && lake env printenv LEAN_PATH)"  # reuse the oleans; never rebuild Mathlib for a measurement
run-bounded 12G 1800 /usr/bin/time -v lean QBP/Foundations/<Module>.lean
```

Record `Maximum resident set size (kbytes)` (KiB) and `Elapsed`. Standalone `lean` on one module;
the import floor (Mathlib oleans mapped in) is ≈ 3.35 GiB on this toolchain and is included in
every figure. `lake build` runs modules in parallel (`-j` = cores), so a library-wide peak is the
sum of the modules building at the same time — under a tight cap use `lake build -j1`/`-j2`.

## Table

| module (`proofs/QBP/…`) | kernel-heavy content | peak RSS (standalone `lean`) | wall | cap that suffices | measured |
|---|---|---|---|---|---|
| import floor (`Mathlib.Data.Fin.VecNotation` + `Mathlib.Tactic`, definitions only) | — | 3 514 720 kB = 3.35 GiB | 8 s | — | 2026-10-18, lean 4.30.0 |
| `Foundations/Octonion32Count.lean` **before #633** (b1bd7ae…master 2026-10-18) | 3 monolithic `decide +kernel` sweeps over 155/15/140 eight-dim candidates on a `![...]` table | **> 12 GiB — killed at cap; 15 628 384 kB = 14.9 GiB at the kill** | 3:23 (killed) | none ≤ 12 GiB (`lake build` OOM at 10 GB #633, 6 GB #683) | 2026-10-18 |
| `Foundations/Octonion32Count.lean` **after #633** | bit-packed table + 7 kernel chunks of 20 candidates + derived 155-count | **4 637 692 – 4 799 656 kB = 4.4 – 4.6 GiB** | 1:37 | 6 GiB (module alone); 10 GB worktree cap ✓ | 2026-10-21 |
| `Foundations/OctonionAutBranching.lean` (#755) | small kernel `decide`s over `Fin (2^2)`/`Fin (2^3)` index tables (XOR splits, `mulCoeff 3` doubling rows, `halfEquivQ`) | **3 541 408 kB = 3.38 GiB** (≈ import floor) | 0:06 (module alone); clean-cache `lake build` of its closure 4:53, peak 5 480 916 kB = 5.2 GiB (dependency modules) | 8 GiB module, 9 GiB closure `run-bounded` ✓ | 2026-10-29 |

Every other Foundations module built green under the 10 GB cap in #633 (29 modules); none has a
written figure yet — add a row when one is measured or when a new kernel-heavy module lands. A
module that would push a standalone `lean` above ~8 GiB needs a row here *before* it lands.

## Rules learned from #633 (`analysis/633-octonion32count/measurement-2026-10-18.md`)

1. **A kernel `decide` never frees its cache inside one declaration.** Memory is linear in the
   number of candidates evaluated by one `decide +kernel`: ≈ 140 MB per 8-dim candidate through a
   `![...]` (`Matrix.vecCons`/`Fin.cases`) table, ≈ 27 MB through a bit-packed `Nat.testBit`
   table. Bound candidates per declaration (chunk with `List.take`/`List.drop` and glue with
   `List.take_append_drop`), do not rely on the table encoding alone.
2. **Never let the elaborator unify against heavy closed terms.** State generic facts over
   variables and instantiate them explicitly; `calc`, `congr`, and `simp`/`rw` with lemma-side
   metavariables on a 155-element concrete list make `isDefEq` evaluate the decidable predicate.
3. **Never state or compare a `Nat` sum of two heavy closed terms.** A definitional check on
   `Nat.add` makes `Meta.reduceNat?` and the kernel's `reduce_nat` `whnf` both summands (looking
   for literals), i.e. evaluate everything. Rewrite the summands to literals first (`rw [h8, h42]`)
   or derive the sum from a variable-only lemma.
4. Doc comments: a `-/` inside prose (e.g. `155-/140`) closes the comment; Lean then elaborates
   whatever follows as code.
