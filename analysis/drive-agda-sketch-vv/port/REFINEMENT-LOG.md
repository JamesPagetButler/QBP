# CD-join square — refinement loop log (CHT provenance trail)

Loop invariant: CDJoin.agda type-checks with N holes, postulate-free. Ratchet: commit only on progress.

| Iter | Hypothesis | Attempt | Agda result | N | Committed? |
|------|-----------|---------|-------------|---|-----------|
| 0 | (baseline) | minimal CDStr, all 1-cells filled | type-checks, 1 hole (twisted square) | 1 | yes (d712720) |
| 1 | square needs cancellation (Hopf template uses secEq/retEq of (a·_)) | +6 CDStr fields: ⊗-isEquivˡ, conj-conj, conj-⊗, neg-neg, neg-⊗ˡ | type-checks, still 1 hole (no regression) | 1 | yes |
| 2 | STATE: confirm exact square goal | isolate as PathP-of-PathP | Agda accepts the type (goal confirmed) | 1 | n/a |
| 3 | filler via hcomp, constant tube + diagonal base | hcomp, 4 faces, base push(a·c')(b·c c')(i∧~k) | FAIL: base circular — tube faces must be l-DEPENDENT morphs via secEq/retEq | 1 | no |

## Loop status (this session)
- **Phase A: DONE** (iter 1) — CDStr extended with the invertibility/compatibility structure the filler needs. Ratcheted + committed.
- **Phase C: IDENTIFIED** (iter 3) — the square closes via a nested hcomp whose tube faces morph the boundary using the equivalence laws secEq/retEq of (a⊗_), per the Hopf.agda §93-122 template. This is a genuine interactive nested-cubical construction (multi-session).
- **TERMINATE**: escalated per loop design (identified-but-not-yet-built nested construction). Structure, goal, template, and required laws are all now in place around the one hole.
| 4 | my inl·inr corner had a convention error (d·a); true CD gives a·d | fix 3 sites: inl·inr = inr(a·d) | PASS type-checks, 1 hole. Now μ'(inl a)=joinMap(a·_)(a·_) is an EQUIVALENCE; true CD product ⇒ filler EXISTS | 1 | yes |
| 5 | filler with corrected formula, nested hcomp | hcomp, morph inr-side via ∨/∧ tube | FAIL: same base/tube coherence — base must already carry the edges | 1 | no |
| 5b | REFORMULATE: express _*J_ via joinMap + join-commFun | μ'(inl a)=joinMap(a·_)(a·_); μ'(inr b)=commFun∘joinMap(b·conj_)(neg∘(b·conj_)) — verified reproduces all inr cases | insight (not yet coded) | 1 | — |

## Loop status after iters 4-5b
- **iter 4 (RATCHET, committed):** corrected the CD convention (inl·inr = a·d). Consequence: μ'(inl a) is now a genuine EQUIVALENCE (diagonal left-mult), and the true CD product means the twisted square's filler PROVABLY EXISTS (SU(2) is a group) — earlier attempts may have chased a non-existent filler.
- **iter 5b (insight):** the whole multiplication is `joinMap`/`join-commFun`-structured. The remaining hole = a homotopy `joinMap(a·_)(a·_) ⟹ join-commFun∘joinMap(b·conj_)(neg∘(b·conj_))` along push a b. This is the cleaner form of BR's core 2-cell; the recommended next iteration is to build it via join-functoriality lemmas rather than raw hcomp.
| 6 | implement joinMap reformulation as code | define joinMap; _*J_ via joinMap/join-commFun, z as variable | PASS type-checks, 1 hole. Corners+1-cells now UNIFORM (joinMap); hole collapsed to a single function-level homotopy | 1 | yes |
| 7 | isolate square in a pushMul helper (maximally clean) | pushMul with inl/inr filled, push,push = square; _*J_ = 3 lines | PASS type-checks, 1 hole (the pushMul push,push square) | 1 | yes |

## Session summary (iters 0-7): 5 committed ratchets, construction maximally clean
- Phase-A extension (iter1) · formula correction ⇒ filler EXISTS (iter4) · joinMap reformulation (iter6) · pushMul isolation (iter7).
- `_*J_` is now 3 clean lines; the ENTIRE remaining obligation = ONE twisted coherence square (pushMul push,push), corners inl(a·x)/inr(b·conj x)/inr(a·y)/inl(neg(b·conj y)).
- This square is BR's irreducible core 2-cell. It is now: (a) provably fillable (true CD product), (b) maximally isolated, (c) with the exact tools (⊗-isEquivˡ, rotInv-2/3/4) and template (Hopf.agda §93-122) in hand. Closing it = an interactive nested-cubical construction (multi-session), tracked in #578.
| 8 | build interactive scaffold for the square | SquareScaffold.agda: tools (Rᵉ/Rsec/Rret) + goal wired + named `seed` obligation + filler skeleton + obligation menu | PASS type-checks, ONE named typed hole (seed); interactive entry point for #578 | 1 | yes |

## Definitive finding on the seed square (2026-07-06, after ~7 distinct attempts)
Attempts: constant-tube hcomp · morphing-tube hcomp · nested hcomp · routing-through-inr(a·y).
EVERY attempt fails on the same geometric fact — Agda: `neg (b · conj y) != a · x`. The square's
two inl-corners (inl(a·x) at [0,0], inl(neg(b·conj y)) at [1,1]) are genuinely distinct points;
the filler must navigate all four distinct corners via the exact CD/equivalence structure. This
is BR's irreducible 2-cell. It is NOT closable by blind batch iteration — it needs either the
BR paper's explicit nested-hcomp transcribed, or a live interactive Agda session (goal-by-goal
in an editor). The scaffold (SquareScaffold.agda) is the correct handoff for either.

---

## Iteration 9 — THE SQUARE IS CLOSED (2026-07-06, "one more attempt, be creative, think through the fundamental goal")

**The creative move: stop constructing, start transcribing.** All ~7 prior attempts were blind
hcomp engineering. But BR's paper was FORMALIZED (Lean-2 HoTT, machine-checked, Apache 2.0) —
the explicit square construction exists as code. Fetched it: `leanprover/lean2`
`hott/homotopy/{imaginaroid,hopf,join,quaternionic_hopf}.hlean` (vendored in `br-lean2-source/`).

**Why every direct attempt failed — and BR's resolution.** The four corners ARE genuinely
distinct (iters 0-8's finding was correct); BR never fill that square directly. Instead
(imaginaroid.hlean:229-242):
1. **Lemmas 1-4** rewrite the corners as images of ONE point `w = ((c*·a*)·d)·b*` (and ±1)
   under two maps `f x = (a·c)·(−x)`, `g y = (c·y)·b` — pure equational algebra.
2. **`ap_diamond f g`** exhibits the goal as the join-functorial image of a UNIVERSAL
   one-variable diamond `(−1, w, 1, w)`.
3. **Suspension induction on `w`**: poles → degenerate diamonds; meridian → `twist_diamond`,
   a pure path-induction (J) lemma. **The carrier must be `Susp A₀`** — the deep reason the
   abstract-CDStr-on-arbitrary-A attempt could never close it. Negation on `Susp A₀` swaps
   poles (definable!), dissolving the S¹-negation obstruction of MulProbe.agda.

| Iter | Hypothesis | Attempt | Gate | Holes | Ratchet |
|---|---|---|---|---|---|
| 9a | port the diamond machinery (join.hlean) | `Diamond.agda`: or/and/deg/hdeg squares (J), diamond, v/hdiamond, symmDiamond, twistDiamond, apDiamond (one-liner — push is a binary constructor), pushCong | **PASS `--safe`, 0 holes** | 0 | yes |
| 9b | port the imaginaroid CD step (imaginaroid.hlean) | `CDJoinBR.agda`: negS/starS on Susp A₀, CDLaws record, lemmas 1-4, genDiamond, pushMulSquare, cd-mul, unit laws, **`CDJoin-HSpace : HSpace (join S S , inl oneS)`** | **PASS `--safe`, 0 holes** | **0** | yes |

**TERMINATE: N = 0.** The seed square is closed — not by filling SquareScaffold's hole
(my corner convention differed from BR's; theirs is ground truth) but by the BR-faithful
construction that supersedes CDJoin.agda/SquareScaffold.agda. Postulate-free, hole-free,
`--safe`, checked with local Agda 2.8.0 against cubical-0.9.

**Remaining for #578:** AC2 — instantiate `A₀ = Bool`, `neg₀ = not`: build CDLaws for
`Susp Bool` (transport the S¹ multiplication along S¹ ≃ Susp Bool; laws via rotInv-1..4,
per quaternionic_hopf.hlean, vendored) → `HSpace (join S¹ S¹)` → feed the already-verified
`S³-HSpace-from-join` (QBPS3HSpace.agda) → **`HSpace (S₊∙ 3)`**.

**Deviations from BR (honest):** normˡ taken as a field (BR derive it from star_mul/star_star);
⊗-unit-coh field added (cubical HSpace needs μₗᵣ; BR's h_space record doesn't). Both are
obligations pushed to the Bool/S¹ instantiation, where they are directly provable.

---

## Iteration 10 — AC2: THE BOOL INSTANTIATION (2026-07-06, "proceed")

Port of `quaternionic_hopf.hlean` (vendored). `A₀ = Bool`, `neg₀ = not`, mult = circle
multiplication conjugated along the library's `S¹IsoSuspBool`:
`x ⊗ y = S¹→SuspBool (SuspBool→S¹ x · SuspBool→S¹ y)`.

Every deferred obligation from iteration 9 discharges here, exactly as predicted:

| CDLaws field | Discharge | Notes |
|---|---|---|
| ⊗-unitˡ | `= sec'` (iso round-trip), verbatim | `to north ≐ base`, `base · z ≐ z` definitional |
| ⊗-unitʳ | `cong fr (rUnitS¹ (to x)) ∙ sec' x` | `rUnitS¹` is a 2-clause pattern refl (`rotLoop base = loop`) |
| **⊗-unit-coh** (the added field) | `= rUnit refl` | at north: LHS ≐ refl, RHS ≐ refl ∙ refl — one groupoid law |
| ⊗-negʳ | via `negS-id : negS ~ id` (BR circle_neg_id) | endpoints `sym (merid false)` / `merid true`; merid-true case = `degSquare` (Diamond.agda), merid-false case = `compPath→Square (lCancel ∙ sym lCancel)` |
| normʳ | `star-to` + `rotInv-1 base b` | `star-to` (starS ↦ invLooper across the iso): poles refl / sym loop, meridians are single connections `loop (~(i∧j))`, `loop (i∧~j)` |
| **normˡ** (the field BR derive) | `star-to` + `rotInv-2 base b` | directly provable, as predicted |
| ⊗-assoc | `ret'` conjugation + `μ-assoc S1-AssocHSpace` | library wedge-connectivity proof; `S₊ 1 ≐ S¹` definitional |

| Iter | Attempt | Gate | Holes | Ratchet |
|---|---|---|---|---|
| 10 | `CDLawsBool.agda`: negS-id, star-to, 8 CDLaws fields, `SuspBool-CDLaws : CDLaws not`, **`JoinSuspBool-HSpace : HSpace (join SuspBool SuspBool , inl north)`** | **PASS `--safe`, first try, 0 holes** | 0 | yes |

**AC2 COMPLETE.** The concrete quaternionic H-space exists, postulate-free.

**Remaining for #578:** AC3 — the join-equivalence wiring:
`join SuspBool SuspBool ≃ join S¹ S¹` (joinMap of S¹IsoSuspBool both sides; check
Cubical.HITs.Join.Properties for an existing lemma), then `HSpace≃` (QBPS3HSpace.agda) →
`HSpace (join∙ (S₊∙ 1) (S₊∙ 1))` → `S³-HSpace-from-join` → **`HSpace (S₊∙ 3)`**.
