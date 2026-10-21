# #633 — `Octonion32Count.lean` peak-RSS measurement and factoring

| | |
|---|---|
| issue | QBP#633 (housekeeping) — `Octonion32Count.lean` OOM-kills `lake build` under a 10 GB cap; related #683 (6 GB cap, exit 137) |
| module | `proofs/QBP/Foundations/Octonion32Count.lean` (imports `Mathlib.Data.Fin.VecNotation`, `Mathlib.Tactic`) |
| toolchain | `leanprover/lean4:v4.30.0` (`proofs/lean-toolchain`), oleans from the main checkout's `.lake/build` via `LEAN_PATH` (no Mathlib build) |
| machine | AMD FX-8350 (8 cores), 32 GB DDR3; `free -g` at start: total 31, used 12, available 16; `df -h /`: 49 GB free |
| cap (hard gate `pre-run-resource-estimate`) | every Lean run under `run-bounded 12G 1800 /usr/bin/time -v lean <file>` (rootless `systemd-run --scope -p MemoryMax=12G -p MemorySwapMax=0` + `timeout 1800`); never two elaborations at once |
| dates | baseline + benchmarks 2026-10-18; bisect + final runs 2026-10-21 |

**Units.** `/usr/bin/time -v` reports "Maximum resident set size (kbytes)" in KiB; the tables give that raw figure and GiB (= kB / 1 048 576). RSS can exceed the 12 GiB cgroup cap because the shared Mathlib olean page cache (≈3.3 GiB) is counted in the process RSS but is charged to whoever first touched it, not to this scope.

## 1. Baseline — the module as merged (monolithic `decide +kernel` sweeps)

Command (from `W/proofs`): `run-bounded 12G 1800 /usr/bin/time -v lean QBP/Foundations/Octonion32Count.lean`

| run | result | wall | user / sys | peak RSS |
|---|---|---|---|---|
| baseline, unmodified module | **killed at the 12 GiB cap (exit 137)** | 3:22.66 (killed) | 175.7 s / 28.5 s | **15 628 384 kB = 14.9 GiB RSS at kill** (still climbing — a lower bound on the true peak) |

So the honest baseline figure is **> 12 GiB, killed at cap** (14.9 GiB RSS at the kill). This is the measurement #633 asked for; it exceeds the ~8 GB threshold, so factoring was required (AC 2).

Output tail:

```
cmd: run-bounded 12G 1800 /usr/bin/time -v lean QBP/Foundations/Octonion32Count.lean
Command terminated by signal 9
	Command being timed: "lean QBP/Foundations/Octonion32Count.lean"
	User time (seconds): 175.72
	System time (seconds): 28.47
	Elapsed (wall clock) time (h:mm:ss or m:ss): 3:22.66
	Maximum resident set size (kbytes): 15628384
	Exit status: 0
run-bounded: job hit its 12G memory cap and was killed (box protected)
exit=137
```

## 2. Where the memory goes (micro-benchmarks, scratch copies of the module's §1–§4 definitions)

| scratch file | kernel work | wall | peak RSS | per-unit cost |
|---|---|---|---|---|
| B0: import + definitions only | none | 7.9 s | 3 514 720 kB = 3.35 GiB | import floor |
| B1: 1 passing candidate, `![...]` table | 8³·2 associator checks | 8.9 s | 3 681 176 kB | ≈ 160 MB |
| B8: 8 passing candidates (`baseCopies`), `![...]` table | 8 × above | 21.3 s | 4 644 976 kB | **≈ 140 MB, ≈ 1.7 s per candidate** |
| BF1: `sgnTable = sgnFast` on all 32×32 entries | 1024 `![...]` lookups | 12.2 s | 3 996 360 kB | ≈ 0.5 GiB |
| BF2: 155 candidates, bit-packed table (`sgnFast`), one `decide` | 155 × 8³·2 | 62 s | 7 724 808 kB | **≈ 27 MB, ≈ 0.35 s per candidate** |

Reading: a kernel `decide` never frees its whnf-cache inside one declaration, so memory is linear in the number of candidates per declaration — 155 candidates ≈ 21 GiB with the `![...]` table (hence the OOM), ≈ 4 GiB even with cheap lookups. Each `![...]` lookup (`Matrix.vecCons` → `Fin.cases` → `Fin.induction`, up to 31 recursion steps carrying `Fin` proofs) costs ≈ 35 KB of cache; a bit-packed `Nat.testBit` lookup (GMP-accelerated) is ≈ 5× cheaper. Neither alone is enough: the fix must bound **candidates per kernel declaration**.

## 3. The factoring (statements unchanged; `#print axioms` unchanged)

1. **§4b `sgnFast`** — `sgnRowMask : Fin 32 → Nat` (32 hex masks, bit `b` of mask `a` set iff `sgnTable a b = -1`), `sgnFast a b := if (sgnRowMask a).testBit b.val then -1 else 1`; `sgnTable_eq_sgnFast` kernel-checks equality on all 1024 entries; `isAlternative_iff_fast` / `isAssociative_iff_fast` transport every sweep. The masks were generated mechanically from the `![...]` table and are re-checked by `crosscheck_sgn_masks.py` in this directory.
2. **§7 chunking** — the one unavoidable brute-force sweep (the D1 discriminator over the 140 crossing candidates) runs as 7 private kernel declarations of 20 candidates each, glued by `forall_mem_split` / `forall_mem_split_at` (`List.take_append_drop`, `List.drop_drop`).
3. **§9 derivation instead of re-sweeping** — the 155-count used to be three independent monolithic sweeps (155 + 15 + 140 candidates). Now `crossing_subspaces_eq_crossingData` kernel-checks `subspaces.filter (any ≥ 16) = crossingData.map (·.2.2)` as ordered lists (a fact the old file only asserted in a comment), so the crossing part is Theorem 5's 42 (`List.countP_filter`, `List.countP_map`); the 15 base candidates are swept directly (8 pass; the `&&` short-circuits the other 140 away); the generic, variable-only partition lemma `countP_eq_add_of_parts` gives 50 = 8 + 42.

Two traps found on the way (both recorded in the module's docstrings, both measured):

- **Elaborator unification on heavy closed terms** (factored attempt 1, killed at 15 652 772 kB after 3:58): `calc` / `congr 1` / `List.countP_filter.symm` on the concrete 155-element terms made `isDefEq` evaluate `isAlternative` on the `![...]` table *in the elaborator*. Fix: all generic reasoning is stated over variables and instantiated explicitly (first-order unification only).
- **`Nat.add` of two heavy closed terms** (attempts 2–3 and bisect prefix P8, killed at 11.3–15.7 GiB): a lemma whose *statement* was `baseAlternativeCount + crossAlternativeCount = alternativeSubspaceCount` runs away however it is proved, because a definitional check on `Nat.add` makes both `Meta.reduceNat?` and the kernel's `reduce_nat` `whnf` the summands to look for literals — i.e. evaluate the whole 155-count on the slow table. (`generalize subspaces = l` did not save it.) Fix: that lemma is gone; the 50 is obtained from `countP_eq_add_of_parts` (only `8 + 42` is ever reduced) and the split's third conjunct uses the original `rw [hbase, hcross, h50]` pattern, which rewrites the summands to literals before any comparison.

### Bisect (cumulative prefixes of the factored file, `run-bounded 8G 420`)

| prefix ends before | wall | peak RSS | result |
|---|---|---|---|
| P1 §4c helpers (after `sgnTable_eq_sgnFast` + bridges) | 0:12.6 | 4 011 988 kB | ok |
| P2 §7 (after lines + base copies) | 1:06 | 4 214 052 kB | ok (after fixing a doc-comment that contained `-/`) |
| P3 §8 (after the 7 chunks + discriminator) | 1:28 | 4 620 172 kB | ok |
| P4 §9 (after `forty_two_split`) | 1:29 | 4 664 764 kB | ok |
| P5 base sweep | 1:28 | 4 650 612 kB | ok |
| P6 `crossAlternativeCount_eq_crossingAlternativeCount` | 1:37 | 4 787 916 kB | ok |
| P7 `base_add_cross_eq_total` (the heavy-sum lemma) | 1:37 | 4 662 988 kB | ok |
| P8 = P7 + heavy-sum lemma | 6:25 (killed) | 11 464 772 kB | **killed at 8 GiB cap** |
| P8 with `generalize subspaces = l` | 3:12 (killed) | 11 266 048 kB | **killed at 8 GiB cap** |

## 4. Before / after

Same command, same cap, same machine, same oleans:

| | wall | user | peak RSS | exit |
|---|---|---|---|---|
| **before** (merged module, monolithic sweeps) | 3:22.66, killed | 175.7 s | **> 12 GiB cap; 15 628 384 kB = 14.9 GiB RSS at kill, still climbing (lower bound on the true peak)** | 137 |
| **after** (this PR, attempt 4) | **1:37.39** | 98.6 s | **4 799 656 kB = 4.58 GiB** | 0 |
| **after** (this PR, final file, docstring-only edits) | **1:37.37** | 98.9 s | **4 637 692 kB = 4.42 GiB** | 0 |
| **after** — independent re-measurement, Red Team review of PR #727 @ 1b677e1 (`run-bounded 8G 1200`, same recipe) | **1:36.73** | 98.4 s | **4 743 364 kB = 4.52 GiB** | 0 |

The import floor alone is 3.35 GiB, so the module's own kernel work is now ≈ 1.1–1.3 GiB (down from > 11.5 GiB). The issue's thresholds: peak ≤ ~8 GB ✓; a 10 GB worktree cap suffices ✓ (so does the 6 GB cap of #683, with ≈ 1.5 GiB headroom).

Final output tail (standalone `lean`, includes the `#print axioms` audit):

```
cmd: run-bounded 12G 1800 /usr/bin/time -v lean QBP/Foundations/Octonion32Count.lean  (final, docstring-unit edits only)
'QBP.Foundations.Octonion32Count.alternative_subspace_count_32_eq_fifty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QBP.Foundations.Octonion32Count.base_plus_crossing_eq_fifty' depends on axioms: [propext, Classical.choice, Quot.sound]
'QBP.Foundations.Octonion32Count.base_copies_persist' depends on axioms: [propext, Classical.choice, Quot.sound]
'QBP.Foundations.Octonion32Count.base_copies_inside_sedenion' depends on axioms: [propext, Classical.choice, Quot.sound]
'QBP.Foundations.Octonion32Count.all_sedenion_lines_associative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QBP.Foundations.Octonion32Count.crossing_pass_iff_discriminator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QBP.Foundations.Octonion32Count.crossingAlternativeCount_eq_predCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QBP.Foundations.Octonion32Count.forty_two_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'QBP.Foundations.Octonion32Count.sgnTable_eq_sgnFast' depends on axioms: [propext]
'QBP.Foundations.Octonion32Count.crossing_subspaces_eq_crossingData' depends on axioms: [propext]
	User time (seconds): 98.89
	System time (seconds): 1.55
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:37.37
	Maximum resident set size (kbytes): 4637692
	Exit status: 0
exit=0
```

## 5. `#print axioms` (final file)

| theorem | axioms |
|---|---|
| `alternative_subspace_count_32_eq_fifty` | propext, Classical.choice, Quot.sound |
| `base_plus_crossing_eq_fifty` | propext, Classical.choice, Quot.sound |
| `base_copies_persist` | propext, Classical.choice, Quot.sound |
| `base_copies_inside_sedenion` | propext, Classical.choice, Quot.sound |
| `all_sedenion_lines_associative` | propext, Classical.choice, Quot.sound |
| `crossing_pass_iff_discriminator` | propext, Classical.choice, Quot.sound |
| `crossingAlternativeCount_eq_predCount` | propext, Classical.choice, Quot.sound |
| `forty_two_split` | propext, Classical.choice, Quot.sound |
| `sgnTable_eq_sgnFast` (new) | propext |
| `crossing_subspaces_eq_crossingData` (new) | propext |

All ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`, no `Lean.ofReduceBool` (no `native_decide`), no new axioms. `scripts/check_lean_foundations.py` and `scripts/check_layer_imports.py` pass.

## 6. Proposed CI / worktree cap for this module

- Standalone `lean` on this module: **≤ 4.6 GiB**. A `run-bounded 6G` cap now suffices for the module alone; the 10 GB cap of #633 and the 6 GB cap of #683 both suffice.
- `lake build QBP.Foundations` builds modules **in parallel** (`-j` = cores by default), so the library-wide peak is the sum of the concurrently building modules, not this figure; under a tight cap use `lake build -j1` or `-j2`. (Not re-measured here: the task was scoped to the module; the figure is recorded in `docs/foundations/lean-build-resource-notes.md` for the CI job.)
- GitHub `ubuntu-latest` runners have 16 GB RAM; the old module could not have been safely built there in parallel with anything else.

## 7. Reproduce

```
cd <worktree>/proofs
export LEAN_PATH="$(cd /path/to/main/checkout/proofs && lake env printenv LEAN_PATH)"   # reuse oleans; no Mathlib build
run-bounded 12G 1800 /usr/bin/time -v lean QBP/Foundations/Octonion32Count.lean
python3 ../analysis/633-octonion32count/crosscheck_sgn_masks.py QBP/Foundations/Octonion32Count.lean
```

## 8. #633 acceptance criteria

- [x] AC1 — peak RSS measured (`/usr/bin/time -v` under `run-bounded`): before > 12 GiB (killed; 14.9 GiB), after 4.4–4.6 GiB; recorded in the module docstring (header + §4b/§7/§9 notes) and in `docs/foundations/lean-build-resource-notes.md`.
- [x] AC2 — peak exceeded ~8 GB, so the enumeration was factored (bit-packed table + 7 kernel chunks + derived count); every theorem statement identical; `#print axioms` re-run and unchanged.
- [x] AC3 — figure added to the per-module resource table `docs/foundations/lean-build-resource-notes.md`, which the Lean CI job (`lean-foundations.yml`, `lake build` step) now points at in a comment (no memory settings changed).
