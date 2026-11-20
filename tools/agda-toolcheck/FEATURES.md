# Agda toolchain features — current pins (QBP#823 W1)

Pins, read from the repo on 2026-11-20 (never assumed):

| component | pin | source |
|---|---|---|
| Agda | **2.8.0** (official prebuilt static Linux bindist) | `.github/workflows/agda-cubical.yml`, `agda-substrate.yml` |
| agda/cubical | **`7b9019b2993535d6931991d87f5c762aee87a67a`** (2026-06-12, "General results about set quotients (#1312)"), library name `cubical-0.9` | `agda-cubical.yml`, `proofs/agda-cubical/qbp-cubical.agda-lib` |
| flags, library tree | `--cubical --safe --no-import-sorts --guardedness` (+ `--lossy-unification` in `SkyrmionCharge.agda`) | `qbp-cubical.agda-lib`, file pragmas |
| flags, builtins tree | `--cubical --safe` | `proofs/agda/*.agda` pragmas |
| local box | `~/agda-2.8.0/agda` (same bindist), `~/cubical` at the same sha, `~/.agda/libraries` → `~/cubical/cubical.agda-lib`, `~/.agda/defaults` = `cubical-0.9` | checked by `run.sh` (`pin_match`, `agda_match`) |

Status column = the baseline run recorded in `BASELINE.md` / `results/results-2.8.0-7b9019b.json`.

## 1. Feature table

### 1a. Core (builtins only) — `tool/`

| feature | used by (QBP) | test file | status |
|---|---|---|---|
| interval `I`, `i0`/`i1`, `~`/`∧`/`∨`, definitional De Morgan + absorption, connection squares, `Partial` | Diamond (orSquare/andSquare), CDJoinBR, HopfNoAssoc (`merid a (~ k ∧ ~ j)`), SubstrateCharge | `tool/Interval.agda` | PASS |
| `PathP`, `_≡_` as constant-family PathP, funExt/happly round-trip, `cong`, dependent `congP`, Σ-paths, `Square` | QBPSubstrate (funext/cong-path), Diamond, CDAssocReduction, CDAssocCubesStatus (PathP of PathP), QuaternionicHopf | `tool/PathP.agda` | PASS |
| `transp`: `transport`, `transportRefl` (φ = i1 identity), filler, `subst`/`substRefl`, J + JRefl | QBPS3HSpace (`subst HSpace (ua∙ e p)`), AssocTransport (J/substRefl), Diamond (J/JRefl), SubstrateCharge, SkyrmionCharge | `tool/Transp.agda` | PASS |
| `hcomp` with face systems, reduction at φ = i1, `hfill` via `Sub`/`inS`/`outS`, builtin `fill` | HopfNoAssoc (8 systems, `hfill … (inS …)`), Diamond/SubstrateCharge (via library `_∙_`) | `tool/HComp.agda` | PASS |
| `Glue`/`glue`/`unglue`, builtin `isEquiv` by copattern, `ua` from Glue, endpoint reduction, `uaβ` (transp over Glue computes), glue/unglue β | HopfNoAssoc (`ua (μ-eq a)`, `ua-gluePt`, `ua-unglue`, `ua→`, `EquivJ`), QuaternionicHopf, QBPS3HSpace (`ua∙`) | `tool/GlueUa.agda` | PASS |
| HIT with a path constructor: S¹, recursor + dependent eliminator by pattern matching on `loop i`, β-rules by refl, `reverse` | QBPSubstrate; CDLawsBool/CDAssocBool via `Cubical.HITs.S1` | `tool/CircleHIT.agda` | PASS |
| parameterised HITs: `Susp` (`merid a i`), `Join` (binary `push a b i`), recursors + β, S³ = Susp³ by refl, `SuspBool→S¹` (`merid false ↦ loop`) | QBPSpheres, QBPJoin; Diamond/CDJoinBR (`push`), CDLawsBool (`merid false i ↦ loop i`) | `tool/SuspJoinHIT.agda` | PASS |
| `opaque` / `unfolding` | not yet used (persona-recommended barrier for the transported S³ μ; today's barrier is module parameters in SubstrateCharge/HopfNoAssoc) | `tool/Opaque.agda` | PASS |
| `--guardedness` with `--safe`: coinductive record, copatterns, productivity, projections compute | flag carried by all 13 `proofs/agda-cubical` files (from the library pin); no QBP coinductive type | `tool/Guardedness.agda` | PASS |
| the library flag string `--cubical --safe --no-import-sorts --guardedness` + `-WnoUnsupportedIndexedMatch`; `Set` must be imported under `--no-import-sorts` | all 13 `proofs/agda-cubical` files; `agda-cubical.yml` | `tool/LibFlags.agda` | PASS |
| `--lossy-unification` with `--safe` | SkyrmionCharge (file pragma); the library's `Group.Base`, `PinSn` | `tool/LossyUnification.agda` | PASS |
| generalisable `variable`, `private`, anonymous/named parameterised modules, `where`, `renaming`, records + copatterns, mixfix + fixity, universe polymorphism, Σ, pattern lambdas, Unicode names | every file (Diamond `module _`, CDJoinBR `record CDLaws`, SubstrateCharge `module SubstrateLink (H : HSpace …)`, CDLawsBool `_⊗Bool_`) | `tool/CoreSyntax.agda` | PASS |

### 1b. Pinned agda/cubical modules — `lib/`

One file per module QBP imports; each ascribes the symbols QBP uses with their pinned types.

| library module(s) | symbols pinned | QBP files | test file | status |
|---|---|---|---|---|
| `Cubical.Foundations.Prelude` | transport, transportRefl, subst, substRefl, J, JRefl, funExt, cong (dependent forms), `_∙_`, compPath-filler, Square, isProp, isSet | all 13 | `lib/LibPrelude.agda` | PASS |
| `.Foundations.Pointed`, `.Pointed.Base` | Pointed, typ, pt, `_→∙_`, idfun∙, **ua∙** | CDJoinBR, QBPS3HSpace, S3FromCD, AssocTransport, HopfNoAssoc, SkyrmionCharge | `lib/LibPointed.agda` | PASS |
| `.Foundations.Equiv`, `.Isomorphism` | `_≃_`, isEquiv, idEquiv, isPropIsEquiv, equivToIso; Iso (fun/inv), isoToEquiv, invIso, compIso | QBPS3HSpace, S3FromCD, AssocTransport, HopfNoAssoc, QuaternionicHopf, CDAssocCubesStatus, SkyrmionCharge | `lib/LibEquivIso.agda` | PASS |
| `.Foundations.HLevels`, `.GroupoidLaws`, `.Path` | isProp→isOfHLevelSuc; rUnit, lCancel; PathP≡doubleCompPathˡ, compPath→Square | QuaternionicHopf, HopfNoAssoc, SubstrateCharge, CDLawsBool, CDAssocBool | `lib/LibHLevelsGroupoid.agda` | PASS |
| `.Foundations.Univalence`, `.Transport` | ua, uaβ, ua-gluePt, ua-unglue, ua→, EquivJ; transport⁻; **`transport (ua notEquiv) true ≡ false`** | HopfNoAssoc, QuaternionicHopf | `lib/LibUnivalence.agda` | PASS |
| `.Foundations.Function` | idfun, `_∘_` (dependent) | HopfNoAssoc | `lib/LibFunction.agda` | PASS |
| `Cubical.Data.Bool`, `.Nat` | Bool/true/false/not (A₀ = Bool, neg₀ = not); ℕ/zero/suc | CDLawsBool, CDAssocBool, S3FromCD, CDAssocCubesStatus, SkyrmionCharge | `lib/LibDataBoolNat.agda` | PASS |
| `Cubical.Data.Int`, `.Int.Properties` | ℤ, pos, negsuc, `-_`, `_+_`, +Comm, isSetℤ; `pos 1`, `negsuc 0` (the pinned charge values) | SkyrmionCharge, SubstrateCharge | `lib/LibDataInt.agda` | PASS |
| `Cubical.Data.Sigma` | Σ-syntax, Σ≡Prop | QuaternionicHopf, HopfNoAssoc | `lib/LibDataSigma.agda` | PASS |
| `Cubical.HITs.Join` | join, inl, inr, push, join∙, Iso→joinIso; a recursor by pattern matching | Diamond, CDJoinBR, CDLawsBool, QBPS3HSpace, S3FromCD, CDAssoc*, QuaternionicHopf, HopfNoAssoc | `lib/LibJoin.agda` | PASS |
| `Cubical.HITs.Susp` | Susp, north, south, merid, SuspBool, SuspBool→S¹ (+ inverse, round-trips), S¹IsoSuspBool, toSusp; `merid false ↦ loop` by refl | CDJoinBR, CDLawsBool, CDAssocBool, S3FromCD, CDAssoc*, QuaternionicHopf, SubstrateCharge, HopfNoAssoc | `lib/LibSusp.agda` | PASS |
| `Cubical.HITs.S1` | S¹, base, loop, `_·_`, invLooper, rotInv-1/2, isGroupoidS¹; `base · z ≡ z` by refl | CDLawsBool, CDAssocBool, S3FromCD | `lib/LibS1.agda` | PASS |
| `Cubical.HITs.Sn`, `.Sn.Properties` | S₊, S₊∙, ptSn; **`S₊ 3 ≡ Susp (Susp S¹)` and `ptSn 3 ≡ north` by refl** (the S₊∙ 3 presentation); sphereElim, sphereElim2, wedgeconFun, sphereConnected | QBPS3HSpace, S3FromCD, SkyrmionCharge, SubstrateCharge, QuaternionicHopf, CDAssocBool, CDAssocCubesStatus | `lib/LibSn.agda` | PASS |
| `Cubical.HITs.Sn.Multiplication` | IsoSphereJoin (`join S¹ S¹ ≅ S³`, `join S³ S³ ≅ S⁷`), IsoSphereJoinPres∙ | QBPS3HSpace, QuaternionicHopf, CDAssocCubesStatus | `lib/LibSnMultiplication.agda` | PASS |
| `Cubical.HITs.Sn.Degree` | degree, degreeIdfun (= pos 1), degreeConst (= pos 0), degreeHom, degree∥₂, degree∥₂Iso; `baryonNumber = degree 3` with its two pinned values | SkyrmionCharge, SubstrateCharge | `lib/LibSnDegree.agda` | PASS |
| `.HITs.PropositionalTruncation`, `.SetTruncation`, `.Truncation`, `.Pushout` | ∥_∥₁, ∣_∣₁, squash₁; ∥_∥₂, ∣_∣₂; propTruncTrunc1Iso; Pushout | QuaternionicHopf, HopfNoAssoc, CDAssocCubesStatus, SkyrmionCharge | `lib/LibTruncations.agda` | PASS |
| `Cubical.Homotopy.HSpace` | HSpace (μ, μₗ, μᵣ, μₗᵣ), AssocHSpace (μ-assoc), S1-HSpace, S1-AssocHSpace | all 13 except Diamond | `lib/LibHSpace.agda` | PASS |
| `Cubical.Homotopy.Hopf` | `module Hopf (e-ass) (conA)`: Hopf, `Hopf north ≡ typ A` (refl), TotalSpaceHopfPush, joinIso₁ — at a generic H-space | QuaternionicHopf | `lib/LibHopf.agda` | PASS |
| `Cubical.Homotopy.Loopspace` | Ω, Ω→ | SubstrateCharge | `lib/LibLoopspace.agda` | PASS |
| `Cubical.Homotopy.Group.Base` | π'Gr, ∙Π, -Π, 1Π, ∙Π-rCancel; `π'Gr 2 (S₊∙ 3)` as a type | SkyrmionCharge, SubstrateCharge | `lib/LibGroupBase.agda` | PASS |
| `Cubical.Homotopy.Group.PinSn` + `Algebra.Group.{Morphisms,Instances.Int,Properties,ZAction}` | πₙ'Sⁿ≅ℤ, πₙ'Sⁿ≅ℤ-idfun∙, πₙ'Sⁿ-gen-by-idfun (generic n only); GroupIso, ℤGroup, GroupTheory.invUniqueR, gen₁-by | SkyrmionCharge | `lib/LibPinSn.agda` (`--lossy-unification`) | PASS |
| `Cubical.Homotopy.Connected` | isConnected, isConnectedPath, isConnectedPathP, isConnectedRetractFromIso, isConnectedSubtr | CDAssocCubesStatus | `lib/LibConnected.agda` | PASS |

### 1c. Negative controls — `mustfail/`

| control | EXPECT substring | status on 2.8.0 |
|---|---|---|
| top-level `postulate` under `--safe` | `Cannot postulate` | REJECTED |
| `{-# TERMINATING #-}` under `--safe` | `TERMINATING` | REJECTED |
| `?` hole left in | `Unsolved interaction metas` | REJECTED |
| path between distinct points (`λ _ → true : true ≡ false`) | `UnequalTerms` | REJECTED |
| **`let postulate p : ⊥ in p` under `--safe`** (agda/agda#8341; AFFECTED 2.8.0, 2.8.0.1, 2.8.0.2; FIXED-IN 2.9.0 via PR 8340, merged 2026-01-27) | `postulate` | **KNOWN-HOLE — accepted by 2.8.0** (< FIXED-IN) |
| control: `forbidden_tokens.sh --require-safe` over the 17 gated files | 0 hits | PASS |
| control of the control: `control/PlantedForbidden.agda` (PLANTED: 9 — flag `--type-in-type`, pragmas TERMINATING / NO_POSITIVITY_CHECK / REWRITE, a let-bound axiom, an axiom block, `primTrustMe`, `primEraseEquality`, `{!!}`; decoys `postulated`, `rewriting-free`, `--safe`) | exactly 9 hits | PASS |
| control fixture B1 `control/B1StringFakeComment.agda` — `s = "{-"` opens a fake block comment before a let-bound axiom (PR #826 Red Team bypass) | exactly 1 hit | PASS |
| control fixture B2 `control/B2IdentifierDashDash.agda` — `a--b` read as a line comment before an axiom on the same line (PR #826 Red Team bypass) | exactly 1 hit | PASS |

The KNOWN-HOLE is real: on the current pin `--safe` does not reject a postulate hidden in a `let`. The grading is keyed to the pin (Red Team F2): `run.sh` reads `FIXED-IN: 2.9.0` from the file; on Agda < 2.9.0 acceptance is KNOWN-HOLE, on Agda ≥ 2.9.0 acceptance is ACCEPTED = suite failure (verified with the `TOOLCHECK_FAKE_AGDA_VERSION=2.9.0` grading test, which exits 1). `forbidden_tokens.sh` (Red Team F3) covers the gap meanwhile and scans **raw text** — no comment or pragma stripping, because a comment-aware scanner was bypassed twice in the PR #826 review (B1: a `"{-"` string literal opening a fake block comment; B2: an identifier `a--b` read as a line comment — each hid a `--safe`-green proof of ⊥ with 0 hits). The token list is the one in PR #826's `scripts/agda_forbidden_tokens.py` and the scan is delegated to that script whenever it is present in the repo, so suite and CI share one scanner. The price is the convention *never write a forbidden token in a gated Agda file, even in a comment*; all 17 gated files comply. The three fixtures keep the scan honest in both directions (sensitivity on B1/B2 and the nine planted constructs; specificity on the decoys).

## 1d. Behaviour notes on the current pin (recorded while writing the suite)

* **Generalised variables + explicit mention.** On 2.8.0, a signature that mentions both a generalisable `x y : A` and `A` (or `ℓ`) explicitly inside an *extended lambda* or an explicit level expression can produce `y.A !=< A` / `UnequalSorts (ℓ-max A.ℓ …)` — the generalised copy and the explicit mention are not identified. Workaround used in `tool/Interval.agda` (`boundary`), `tool/PathP.agda` (`ΣPathP`), `lib/LibTruncations.agda` (`Pushout`): explicit binders. QBP's own files avoid the pattern (they bind `{A : Type ℓ}` explicitly where it matters).
* **Error classes are printed** (`error: [UnequalTerms]`, `[UnsolvedConstraints]`, `[NotInScope]`): the must-fail EXPECT strings pin these where the free text is order-dependent.
* **Cost profile** (first measurement on this box, `boxrun --gpu`, 1 thread): builtins-only files 0.03–0.08 s / ≤ 48 MiB; library test files 0.17–7.6 s / 55–465 MiB (the cost is loading pinned interfaces from `~/cubical/_build`); project files ≤ 8 s warm / 10.2 s cold, ≤ 507 MiB warm / 644 MiB cold (`SubstrateCharge`). See `BASELINE.md`.

## 2. Candidate triage, next upgrade — DRAFT (no upgrade performed)

This section is the R5 template: every changelog item between the pinned and
the candidate version lands in one bucket — *relevant → test needed*,
*breaking → does it touch our usage?*, *not relevant → one-line reason*.
Sources were fetched read-only with `gh api` on 2026-11-20 and treated as
untrusted text.

### 2a. Agda 2.8.0 → 2.8.0.1 → 2.8.0.2 → 2.9.0

Sources: `repos/agda/agda/contents/doc/release-notes/{2.8.0.1,2.8.0.2,2.9.0}.md` (master), `repos/agda/agda/releases`.
Releases: 2.8.0.1 (2026-08-31), 2.8.0.2 (2026-09-13), **2.9.0 (2026-11-13)**; 2.9.0-rc1..rc3 are pre-releases and excluded by R2 (stable only).

* **2.8.0.1** (1 item): GHC 9.14.1 support — *not relevant* (bindist user).
* **2.8.0.2** (2 items): Windows `zlib1.dll`; version string without commit hash — *not relevant* to Linux, but note `run.sh` parses `agda --version` field 3, which is already the clean form on 2.8.0.
* **2.9.0** (578 items as parsed: narrative notes + 204 closed issues + merged PRs). Full table: [`triage/agda-2.8.0-to-2.9.0.md`](triage/agda-2.8.0-to-2.9.0.md).

| bucket | count |
|---|---|
| relevant → test needed | **199** |
| breaking → touches our usage? | **12** |
| not relevant | **370** |
| total | 581 |

Items that matter most for QBP, in order:

1. **`--safe` hole closed (agda/agda#8341 / PR 8340).** `let postulate … in …` passes 2.8.0's `--safe`; 2.9.0 rejects it. Test: `mustfail/LetPostulate.agda` must flip KNOWN-HOLE → FIXED. This alone is a reason to lean forward.
2. **Builtin fixities removed (BREAKING, Builtins section) × cubical pin.** 2.9.0 drops the fixity of `primINeg`/`primIMin`/`primIMax`. agda/cubical at `7b9019b` renames them `~_`/`_∧_`/`_∨_` *without* fixity (`Core/Primitives.agda`), so `i ∧ j ∨ k`-style interval expressions throughout the library would parse differently or fail. cubical commit **`c2d05f7` (2026-09-09, "#1325")** restores the fixities. ⇒ **Agda 2.9.0 requires cubical ≥ `c2d05f7`; the two pins move together** (R2's "Lean and Mathlib move together", for Agda). QBP's own `tool/` files rename the primitives too and must gain `renaming (primIMin to infixr 20 _∧_ …)` in the same PR.
3. **Cubical side conditions now checked in inference mode (#8683, consistency fix).** Can *reject* previously accepted `glue`/`unglue` applications. Usage to re-check: `HopfNoAssoc.agda` (`ua-gluePt`, `ua-unglue`, the `hfill` systems), `QuaternionicHopf.agda`; `tool/GlueUa.agda` exercises `prim^glue` with explicit side conditions.

Also relevant: ~60 consistency/internal-error fixes in the cubical core and HIT unifier (#6198 Glue/HCompU canonicity, #8370, #8695 HIT cycle rule, #7629/#8808 cubical internal errors) — none can break a sound proof, all strengthen what a green `--safe` certifies; the project layer re-run is the test. `UnusedImports` (new warning, non-fatal) will fire on QBP's explicit `using` lists — count and prune in the upgrade PR. `--parallel`/`-j` and the performance work are R6 items: compare `results/*.json` wall/RSS before adopting anything. `Eta-equality … no longer inferred` is bucketed *breaking* only pro forma: QBP's records (`HSpace`, `CDLaws`, `CDCommLaws`) are not recursive.

How this triage was produced (repeat for the next candidate):

```bash
D=<fresh empty dir>   # downloaded content is untrusted: keep it out of the repo
gh api 'repos/agda/agda/releases?per_page=20' --jq '.[] | [.tag_name,.published_at,.prerelease] | @tsv'
for v in 2.8.0.1 2.8.0.2 2.9.0; do
  gh api "repos/agda/agda/contents/doc/release-notes/$v.md?ref=master" -H 'Accept: application/vnd.github.raw' > "$D/agda-$v.md"; done
python3 -I tools/agda-toolcheck/triage_changelog.py --notes "$D/agda-2.8.0.1.md" --notes "$D/agda-2.8.0.2.md" \
  --notes "$D/agda-2.9.0.md" --overrides tools/agda-toolcheck/triage_overrides.json \
  --label "Agda 2.8.0 → 2.9.0" > tools/agda-toolcheck/triage/agda-2.8.0-to-2.9.0.md
```

`triage_overrides.json` holds the hand judgements (first match wins); the
built-in keyword rules catch the families (Emacs, backends, rewriting,
modalities, …); a PR titled only "Fix #N" inherits issue N's bucket; anything
left is printed as `UNCLASSIFIED` and must be resolved by hand before the
upgrade PR (0 remain for 2.9.0).

### 2b. agda/cubical `7b9019b` → v0.9 tag → master

**Finding: the tag `v0.9` (`b150186`, 2025-07-30, "Release for Agda 2.8.0") is 68 commits OLDER than the pin.** `gh api repos/agda/cubical/compare/7b9019b…b150186` → `ahead_by 0, behind_by 68`. The pin already sits on the post-0.9 line (library name `cubical-0.9` is the 0.9 *series*). "Move to v0.9" would be a downgrade; there is no newer tag. The candidate is therefore **master** (`8f0a71b`, 2026-11-19): 23 commits, 118 files.

| sha | commit | touches QBP's direct imports? | bucket | test / reason |
|---|---|---|---|---|
| 3686f9d | made some variables private (#1315) | no (`Algebra/BooleanRing`) | not relevant | module not in QBP's closure |
| 9216603 | BooleanAlgebraStr infers the set (#1297) | no | not relevant | BooleanRing |
| 970cb5f | OrderedCommRing properties (#1303) | no | not relevant | ordered rings; QBP uses none |
| f410736 | truncated logarithm over ℕ (#1311) | `Data/Nat/Order`, `Data/Nat/Mod` (transitive) | not relevant | QBP imports `Cubical.Data.Nat using (ℕ ; zero ; suc)` only; additions |
| 44374e6 | Determinant and Adjugate (#1165) | no | not relevant | linear algebra |
| 5a2e8e2 | generated-ideal decomposition (#1317) | no | not relevant | CommRing quotients |
| 439f2a0 | trivialQuotient→1∈I (#1316) | no | not relevant | CommRing quotients |
| b7b644e | perf: baseChange normal form (#1314) | no | not relevant | CommAlgebra |
| 2b0ab94 | union of iterative sets (#1318) | no (`Foundations/Smallness` is new) | not relevant | iterative sets |
| 6845892 | rename lemmas in `Nat.Order` (#1319) | `Data/Nat/Order` (transitive), `Cohomology/EilenbergMacLane/Groups/Sn` (transitive via `Sn.Degree`?) | **breaking → usage?** | renames only; QBP names none of the renamed lemmas (grep `Nat.Order` → 0). Test = `lib/LibDataBoolNat`, `lib/LibSnDegree`, `lib/LibPinSn` + project re-run |
| 34be04c | iterative sets ≃ cumulative hierarchy (#1320) | `Foundations/Equiv` **+18 lines** (`rCancelIsEquiv`, `lCancelIsEquiv`), `Functions/Embedding`, `Functions/Surjection` | relevant → test | additions to a directly imported module; `lib/LibEquivIso` must still pass (no clash with QBP names) |
| **6e6df4e** | **remove `UsingEq` (#1322)** | **`Foundations/Prelude` −17 lines**, `Data/Bool/{Base,Properties}` (`DecBool→Type` moved Base←Properties; Bool.Properties now imports only `PropositionalTruncation.Base`) | **breaking → usage?** | QBP never uses `_UsingEq` / `DecBool→Type` (grep → 0). `Cubical.Data.Bool` still exports Bool/true/false/not/notEquiv. Test = `lib/LibPrelude`, `lib/LibDataBoolNat`, `lib/LibUnivalence` |
| **c2d05f7** | **fixity for imported interval operations (#1325)** | **`Core/Primitives`** (every QBP file, transitively) | **relevant → test (REQUIRED for Agda 2.9.0)** | `infixr 20 _∧_ _∨_`, `infix 30 ~_` — today these fixities come from `Agda.Primitive.Cubical` itself, so parsing is unchanged on 2.8.0 and preserved on 2.9.0. Test = `tool/Interval` (De Morgan squares) + the whole project layer |
| af1f88a | explicit implicits for agda/agda#8749 (#1327) | `CW/HurewiczTheorem`, `Cohomology/EilenbergMacLane/{Groups/Sn}`, `Homotopy/EilenbergMacLane/CupProductTensor` | not relevant | not in QBP's closure (`Sn.Degree`/`PinSn` go through `ZCohomology.*`, not EilenbergMacLane); lib re-run confirms |
| f3c126c | unify Inductive and Recursive Order (#1323) | `Data/Nat/Order*` (removes `Order/Recursive.agda`), `Data/Bool/Properties`, `Data/Fin/*`, `CW/*` (transitive) | **breaking → usage?** | QBP imports no order lemma; a transitive module removal is caught by `lib/` (every direct import re-checked) |
| 3d828af | remove fixity for closed operators, for Agda 2.9.0 (#1329) | no (`HITs/CumulativeHierarchy`) | not relevant | prepares the library for `FixityDeclarationForNonOperator` |
| 87af036 | normalised ℚ (#1313) | `Data/Int/{Base,Properties}` (+`_≡ᵇ_`, `_<ᵇ_`, `IsZeroℤ`, `·≢0`), `Foundations/Function` (+`converse`), `Data/Nat/Properties` | relevant → test | additions to directly imported modules; `lib/LibDataInt`, `lib/LibFunction` must still pass; `Int.Base` now imports `Cubical.Data.Empty` — watch for a name clash with QBP's own `⊥` (none: QBP's `⊥` is in builtins-only files) |
| 0c9f423 | faster Rationals (#1324) | `HITs/SetQuotients/Properties` (big refactor, `DISPLAY` pragmas, named `where` modules) — transitive only | not relevant | QBP's ℤ is `data ℤ`, not a quotient; SetQuotients is not in the closure of the 34 direct imports (confirmed by lib re-run on the candidate) |
| c37782b | binary search / nth root (#1330) | `Data/Nat/{Order,Properties}` (transitive) | not relevant | additions |
| 0ad02ac, ec0098d, 2bc6a92, 8f0a71b | iterative sets: W-types, codes, quotients, universes (#1334–#1337) | no | not relevant | iterative sets |

Counts: relevant → test **3** · breaking → usage? **3** · not relevant **17** (of 23).

### 2c. Coupling and order of operations for the next upgrade PR

1. Move **both** pins in one branch: Agda 2.9.0 + cubical ≥ `c2d05f7` (master `8f0a71b` is the candidate; a new upstream tag, if one appears, is preferred by R2).
2. Add fixities to the `tool/` renamings (`primIMin to infixr 20 _∧_` …) — same change as cubical `c2d05f7`.
3. Run `run.sh`; expected diffs vs. this baseline: `LetPostulate` → FIXED; possibly `WRONG-ERROR` on must-fails whose text changed (re-pin the EXPECT); `UnusedImports` warnings in the logs (non-fatal); timing/RSS deltas per R6.
4. Thompson step (W4) on the bindist: release provenance + checksum of `Agda-v2.9.0-linux.tar.xz` from `repos/agda/agda/releases`.
