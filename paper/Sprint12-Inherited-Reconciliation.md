# Sprint 12 Inherited Lean Corpus — Toolchain Reconciliation Log

**Status:** Active (PR8 of #81; integration work under qbp-implementor Integration role per Beekeeper 2026-05-13)
**Source:** `archive/lean-project/` (7 .lean files; package `«qbp»`; toolchain v4.18.0; authored 2026-03–04 per file headers)
**Target:** `proofs/Sprint12-Inherited/` (folded as `lean_lib «QBPSprint12»` inside `«QBPProofs»` Lake project; toolchain v4.30.0-rc2)
**Goal per Beekeeper directive 2026-05-13:** force incompatibilities to surface; document each; resolve incrementally. BMA will re-audit these against new theory post-launch.

> "this is the fundamental reconciliation we must do to find the incompatibilities and then we will have to resolve them. this is the real work."
> — Beekeeper, 2026-05-13

---

## Pre-build structural incompatibilities (found before `lake build`)

| ID | Incompatibility | Source | Status |
|---|---|---|---|
| S-1 | `archive/lean-project/lakefile.lean` declares `srcDir := "QBP"` but the 7 .lean files live at the archive root, not in `archive/lean-project/QBP/`. The archive Lake project as-is would not build cleanly. | grep + ls on archive/lean-project/ | RESOLVED-IN-MIGRATION: in `proofs/lakefile.lean`, `«QBPSprint12»` uses `srcDir := "Sprint12-Inherited"` matching the actual file location |
| S-2 | No `import` statements in any of the 7 .lean files. Lean 4 code with zero imports uses only built-in primitives. Files rely entirely on `native_decide` on Bool computations. | `grep -E "^import " archive/lean-project/*.lean` returns 0 matches | NOTED: matches the design intent per Sedenion.lean header "All proofs use `native_decide` on Bool computations — zero `sorry`." No imports needed for Bool-decidable theorems |
| S-3 | No explicit `namespace` declarations in any .lean file. Theorem names are top-level. Risk: collision with theorems in `proofs/QBP/` if any names match. | `grep -E "^namespace " archive/lean-project/*.lean` returns 0 matches | UNRESOLVED: will surface during `lake build` if any name clash |
| S-4 | Theorem count discrepancy: state report (`archive/QBP-Repo-State-Report-2026-05-08.md` §4) claims **208 theorems**; my actual `grep -c "^theorem "` finds **69**. `archive/00-START-HERE.md` claims **~82 theorems**. Per-file: Bi2Se3=6, Crystallisation=6, Elements=12, Graphene=11, Kitaev=13, Quaternion=11, Sedenion=10 = 69. | `grep -c "^theorem " archive/lean-project/*.lean` per file | NOTED: 208 was wrong. 69 is the actual `theorem`-declaration count. Helper `def`/`example`/`#check` may explain the gap to 82 in the earlier count; 208 may have been a line-count-style miscount. Anchored to 69 going forward. |
| S-5 | `sorry` occurrences in `Elements.lean` (line 8) and `Sedenion.lean` (line 6) are **header comments** declaring "zero sorry", NOT proof gaps. Real sorry count = 0. | `grep "sorry" archive/lean-project/*.lean` then header-line inspection | RESOLVED: matches the synthesis claim; no proof gaps |

---

## Build incompatibilities (found during `lake build` on v4.30.0-rc2)

| ID | Incompatibility | Location | Status |
|---|---|---|---|
| B-1 | `proofwidgets` dependency fails to resolve on v4.30.0-rc2: `Unknown constant Lake.Hash.ofHashable` at `proofs/.lake/packages/proofwidgets/lakefile.lean:63:52`. Pre-existing breakage in the `proofs/` Lake project, not Sprint12-specific. | proofs/.lake/packages/proofwidgets/lakefile.lean:63 | RESOLVED via `lake update` — manifest refresh fixed the deps |
| B-2 | `let mut` outside an explicit `do` block fails to parse on v4.30.0-rc2. In Lean 4.18 the `for x in xs do` construct admitted implicit do-block semantics in a function body; v4.30 requires explicit `Id.run do` (or `do` in a monadic context). Affects 9 `def`s in Sedenion.lean: `countAntiCommutingPairs`, `normSqProduct`, `isZD`, and 6 others at lines 113, 130, 150, 178, 209, 216, 225, 239, 267. | Sprint12-Inherited/Sedenion.lean:{113,130,150,178,209,216,225,239,267} | UNRESOLVED — pending mechanical fix (wrap bodies in `Id.run do`, change last expr to `return ...`) |
| B-3 | Orphan doc-comment `/-- ... -/` at lines 255–263 spans a section explanation; v4.30 parser rejects it because no declaration immediately follows (line 264 is blank; line 265 starts a new `/--`). Lean 4 doc comments must attach to a following decl. | Sprint12-Inherited/Sedenion.lean:255–263 | UNRESOLVED — change `/--` to `/-` for section-explainer block, OR merge into the v265 doc comment |
| B-4 | Cascade failure: `native_decide` tactics at lines 359, 363, 368, 373 fail because the `def`s they evaluate (`countAntiCommutingPairs`, `countZeroDivisors`, `checkAllHessianTraces128`, `checkAllHessianTracesSq1152`) contain implicit `sorry` due to B-2 parser errors. Will resolve when B-2 fixes. | Sprint12-Inherited/Sedenion.lean:{359,363,368,373} | DERIVATIVE-OF-B-2 — no separate work |
| B-5 | Cascade: `#eval` at lines 397, 398, 399 depend on the `sorry` axiom via the B-2 broken defs. Will resolve when B-2 fixes. | Sprint12-Inherited/Sedenion.lean:{397,398,399} | DERIVATIVE-OF-B-2 — no separate work |
| B-6 | Unused-variable warnings (`h1`, `h2`) at Sedenion.lean:67/68 and 75/76. Lint-level; not blocking. | Sprint12-Inherited/Sedenion.lean:{67,68,75,76} | NON-BLOCKING — defer to later cleanup |
| B-7 | All 6 other files (Bi2Se3, Crystallisation, Elements, Graphene, Kitaev, Quaternion) **build clean on v4.30.0-rc2** after B-1 resolution. Per-file error count: 0. The Sedenion.lean issues are isolated. | n/a | CONFIRMED-CLEAN |

**Net first-pass build result on v4.30.0-rc2:** 6 of 7 files build clean. Sedenion.lean has 1 real syntactic incompatibility (B-2: `let mut` requires `Id.run do` wrapper) + 1 orphan-doc-comment issue (B-3); everything else is cascade or lint.

## Second pass — after applying Sedenion B-2/B-3 fixes

Once Sedenion was fixed and the build advanced, the SAME class of issues surfaced in other files:

| ID | Incompatibility | Files affected | Status |
|---|---|---|---|
| B-8 | `let mut` outside `do` block — same as B-2 | Elements.lean (4 defs: shellCapacitySum, aufbauOrder, cumulativeElectrons, checkNobleGases); Quaternion.lean (3 defs: quaternionNormSqProduct, checkHurwitzQuaternion, checkHurwitzFailsSedenion) | RESOLVED — Id.run do wrapping |
| B-9 | Orphan `/--` doc comments — same as B-3 | Bi2Se3.lean (3: lines 102, 125, 136); Elements.lean (line 162); Graphene.lean (line 250) | RESOLVED — `/--` → `/-` for section-explainer blocks |

## Third pass — `List.get?` removed in v4.30

| ID | Incompatibility | Location | Status |
|---|---|---|---|
| B-10 | `List.get?` no longer exists in v4.30.0-rc2 stdlib. Replacement: `xs[i]?` (Option-returning indexer). | Elements.lean:130, 144 (in `cumulativeElectrons` + `checkNobleGases`) | RESOLVED — replaced `order.get? i` with `order[i]?` |

## Fourth pass — real theorem-content failure (theory-axis per D4)

| ID | Incompatibility | Location | Status |
|---|---|---|---|
| **B-11 (THEORY-AXIS — APPROVED 2026-05-14)** | Crystallisation.lean `theorem variation_correlation` failed `native_decide` because `checkCorrelationConstraint` evaluates to `false`, not `true`. Root cause: `let a_check := 1 - 2 * 1 + 1` was inferred as `Nat`, where truncated subtraction `1 - 2 = 0` makes `a_check = 1` (NOT `0` as the inline comment claims). The author's stated intent (C3 correlation constraint with signed exponent arithmetic) requires `Int`. | Crystallisation.lean:112 (def), Crystallisation.lean:232 (theorem) | **RESOLVED + ADJUDICATED.** Added explicit `: Int` annotations matching the author's stated intent. Theory-axis adjudication per Beekeeper D4 ([pr407-conflict-resolution channel seq=23, 2026-05-14](https://github.com/JamesPagetButler/QBP/pull/414)): **APPROVED by qbp-oppenheimer**. Ruling: *"The intended C3 correlation-constraint claim is ΔΛ/Λ − 2(ΔG/G) + Δα/α = 0 (exact). This is a real arithmetic identity over real numbers, not a Nat-truncated computation. The `Int` annotation makes the Lean code consistent with the mathematical claim. The Nat-truncated version was a false representation of the claim — it would have evaluated to a non-zero residue and the theorem would have been vacuously trivial."* **Scope note:** B-11 is the Nat-truncation incident specifically (one theorem in one file). It is **distinct from the 208/69 counting-methodology incident (B-12 below)** — the two were initially conflated but were recognised as separate per Red Team + Gemini + Oppenheimer review of this PR (2026-05-14). B-11's institutional weight is the false-verified-theorem pattern (`native_decide` masked the underlying error); B-12's institutional weight is the audit-methodology pattern (a number flowed downstream unchallenged). |
| **B-12 (METHODOLOGY — APPROVED 2026-05-14)** | The inherited claim *"208 theorems / 0 sorries"* in `archive/historical/README.md` and `archive/QBP-Repo-State-Report-2026-05-08.md §4` does not match any actual count of any location. Per qbp-architecture's empirical audit ([pr407-conflict-resolution seq=27, 2026-05-14](https://github.com/JamesPagetButler/QBP/pull/414)): canonical `archive/lean-project/` has **69** theorem-class declarations (`grep -E "^(theorem\|lemma\|example)"`); `archive/historical/lean-standalone/` has **161** (with **96** real sorries — these are the WIP standalones, not the canonical corpus); duplicates at `archive/qbp-lean/QBP/` and `archive/` root flat-renames are byte-identical to the canonical 69. The 208 figure most likely came from a regex-too-broad count (counting `def` declarations as theorems). | `archive/historical/README.md`, `archive/QBP-Repo-State-Report-2026-05-08.md §4`, and any consumer doc citing "208" | **RESOLVED for this PR.** Canonical headline anchored at **69 theorems verified on v4.30.0-rc2** at `proofs/Sprint12-Inherited/`. Correction of the source-of-error documents at the 3 known locations is **deferred to a post-merge housekeeping PR** per `toddle-design` seq=21 closeout action item assigned to qbp-implementor: *"FanoGenesis dup cleanup + 208 counting-methodology corrections (3 locations) + Hessian content-drop logging."* PIVOT-S3-001 lineage: same family of failures (number flowing downstream unchallenged) that the new `docs/workflows/review_anchoring.md` standing rule (PR #413, anchor type #5 *derived dimensional/algebraic identity with substitution chain shown*) is the direct corrective for. |

## Out of scope for this PR (deferred to post-merge housekeeping)

The following are recognised but **explicitly deferred** to a separate housekeeping PR per `toddle-design` seq=21 closeout (2026-05-14):

| Deferred item | Reason | Tracking |
|---|---|---|
| Byte-identical FanoGenesis dup at `archive/QBP_FanoGenesis.lean` (md5-equal to `archive/historical/lean-standalone/QBP_FanoGenesis.lean`) | Untracked across both locations; not modified by this PR | Housekeeping PR (post-#414-merge) |
| Byte-identical `archive/qbp-lean/QBP/*.lean` duplicates (7 files) | Duplicates of canonical `archive/lean-project/` | Same housekeeping PR |
| Byte-identical `archive/lean-project-*.lean` flat-renames at archive root (7 files) | Duplicates of canonical | Same housekeeping PR |
| Correct "208 theorems" claim in 3 source-of-error docs (per B-12) | Methodology fix; not blocking this PR's Lean-fold | Same housekeeping PR |
| Hessian content-drop logging entry | Architect's audit finding ("presumably absorbed into Sedenion" verbal hedge) — institutional record per PR #413 anchor rule | Same housekeeping PR |

The dedup work is **not load-bearing for this PR's "force incompatibilities to surface" deliverable** (Beekeeper directive 2026-05-13). The 7-file canonical corpus is what BMA will re-audit; duplicates can be removed cleanly post-merge without changing the build state.

## Final build result

```
Build completed successfully (9 jobs).
Exit: 0
```

All 7 files build clean on Lean 4.30.0-rc2 within the `«QBPProofs»` Lake project. Remaining: 16 unused-variable warnings (`h1`, `h2` in pattern matches; B-6-class, non-blocking).

## Summary of changes by file

| File | Theorems | Changes applied | Build status (v4.30.0-rc2) |
|---|---|---|---|
| Bi2Se3.lean | 6 | 3 orphan-doc → /- | ✅ clean |
| Crystallisation.lean | 6 | 1 type annotation (Nat → Int) for C3 correctness | ✅ clean **(content fix; theory-axis review recommended)** |
| Elements.lean | 12 | 4 Id.run do; 2 List.get? → xs[i]?; 1 orphan-doc → /- | ✅ clean |
| Graphene.lean | 11 | 1 orphan-doc → /- | ✅ clean |
| Kitaev.lean | 13 | none | ✅ clean (built clean as-is) |
| Quaternion.lean | 11 | 3 Id.run do | ✅ clean |
| Sedenion.lean | 10 | 9 Id.run do; 1 orphan-doc → /- | ✅ clean |
| **TOTAL** | **69** | **21 mechanical + 1 semantic (B-11)** | **✅ 9 jobs build clean** |

<!-- placeholder for any follow-up build runs -->

---

## Theorem-by-theorem reconciliation map (post-build)

(Will populate once `lake build` surfaces what survives on v4.30.0-rc2.)

| File | Theorem | v4.18.0 status (claimed) | v4.30.0-rc2 status (this PR) | Resolution |
|---|---|---|---|---|

---

## BMA re-audit handoff (future)

Per Beekeeper directive: "In the end we want BMA to go back of each of our experiments on its own and resolve them cleanly with the new work."

When BMA is operational, this document becomes the input to BMA's re-audit of the Sprint 12 corpus against:
- Session-13 theory updates (KILLED-f4-info-theoretic-justification; CONV-cd-tower-in-zeta-moments; W-003 revision; CONJ-fu-from-hawking-time-reverse)
- Whatever theory state is current when BMA comes online
- The CTH inventory after PR7 reconciliation (v5.13 ↔ v5_3 → unified vNext)

Until then, manual reconciliation continues here, in order of importance per file:
1. **Sedenion.lean** (foundational 16D algebra; T1–T9 cited by Bi2Se3)
2. **Quaternion.lean** (foundational SU(2)/Kramers; Q1–Q11 cited by Bi2Se3, Graphene)
3. **Elements.lean** (T10–T18; shell capacity, Aufbau, Koide ratio)
4. **Graphene.lean** (Z₃ honeycomb + MATBG)
5. **Kitaev.lean** (Z₂ gauge structure)
6. **Bi2Se3.lean** (topological insulator chain — depends on Quaternion + Sedenion)
7. **Crystallisation.lean** (spectral action moment hierarchy)

---

## Provenance

- Files copied from `archive/lean-project/` (untracked in repo prior to this PR; sourced from QBP-web Session-13 transfer of 2026-05-08)
- Original authorship per file headers: James Paget Butler + Claude (Opus, Red Team), 2026-03 to 2026-04
- This integration: qbp-implementor (Claude Opus 4.7 [1M context]), Integration role per Beekeeper 2026-05-13
- Tracking issue: #81 (Sprint 3 Theory Refinement umbrella; PR8 of 8-PR roadmap per [#81/comment](https://github.com/JamesPagetButler/QBP/issues/81#issuecomment-4426862264))
