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
