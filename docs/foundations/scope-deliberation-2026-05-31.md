# Foundations Rebuild — Scope Deliberation (Minutes)

**Date:** 2026-05-31 (extending into 2026-06-01 UTC)
**Status:** LIVE — open item routed to Theory teams; qbp-architecture to be looped in after team verdict
**Convened by:** Oppenheimer (Strategic Lead)
**Ratified by:** James Paget Butler (beekeeper / PI)
**Participants:** Oppenheimer (strategy), Gemini Theory team (Furey, Feynman), Claude Counter-Team (Wilson, Jaynes), Foundations Auditor (read-only audit), beekeeper (decisions)

> **Purpose of this document.** A durable record of *why* the foundations rebuild is scoped the way it is — including what we are deliberately **not** proving and the rationale, so a stuck future-us can recover the reasoning. This is the minutes; the queryable form lives in the CTH (see §6, Wisdom Ledger).

---

## 0. The deep goal (the test every decision is measured against)

A **truly solid, fully-proven foundation** for QBP — a Lean 4 stack, zero-`sorry`, where every rung is proven — solid enough to eventually answer fundamental questions (*Why is there gravity? Is there truly a "Universe 1" / parent black hole?*) and to **scale all the way up**: ℝ→ℂ→ℍ→𝕆→𝕊 → particles → atoms → materials-chemistry ("materia-chem") and beyond.

**Test for every foundational decision:** does this make the foundation *more* solid, self-justifying, and provable end-to-end — or does it import an external, unprovable convention?

**Why this rebuild exists (the original failure).** A prior phase eliminated enough of the Cayley-Dickson ladder and its utility that we *convinced ourselves we had fully uncovered it* — but we had only a **selection of operations**, no full proof of the ladder, and no proof for all available operations. A web-Claude review uncovered the gaps. The strategic call: go back and verify there really are no gaps, so future work builds from a robust foundation.

---

## 1. Triggering context — the octonion orientation ruling

The deliberation was triggered by a Tier-3 review finding that the inherited `archive/QBP_Octonion.lean::octonionMul` table is **non-alternative** (18/42 entries wrong vs Cayley-Dickson; survived only because its alternativity/CD-agreement theorems were `True := by trivial` stubs).

**Ruling (beekeeper-ratified): re-derive-native / F3-master.** The octonion Fano orientation is a *free internal choice*; the CD doubling formula (F3) is master; `octonionMul` is fixed to the CD-canonical valid orientation (NOT reverse-engineered to Furey 2018). Import-literal is withdrawn. Full provenance in the Gemini decision log (`gemini/state/decisions/qbp.md`) and bridge `pr407-conflict-resolution` seq 69.

This is the canonical example of the rebuild's purpose: a foundation-altering defect, hidden behind a proof stub, caught by review. It also established the principle carried into scope: **the foundation imports no external arbitrary convention.**

Three obligations attached to that ruling (now folded into scope below): (1) prove G₂-transitivity in Lean zero-sorry; (2) G₂-map to Furey as a tested boundary translation; (3) tag every numeric anchor FORCED vs SELECTED.

---

## 2. The phased plan: (1) → (3) → (2)

| Phase | What | Why this slot |
|---|---|---|
| **(1) Tower** | Prove ℝ→ℂ→ℍ→𝕆→𝕊 zero-sorry, **operations-complete** (§3), incl. the 3 obligations | **No-regret.** Load-bearing under every choice of upper boundary; can start now with zero risk of proving the wrong thing. |
| **(3) Dependency map** | Trace claim→lemma→proof-status for all Tier-1 physics claims, **as a view over the CTH** | **The scoping instrument.** Built on the solid tower, reveals exactly which lemmas the physics rests on. |
| **(2) Physics bridge** | Prove the load-bearing rungs the map identified | **Now bounded** — scope = what (3) surfaced, not a guess. |

**Rationale:** (1) is the no-regret bedrock; (3) is the blueprint; (2) builds exactly what the blueprint calls for. This converts "prove everything up to chemistry" (unbounded) into "prove the tower, then prove precisely what Tier-1 claims stand on" (bounded, evidence-defined). The materia-chem ambition becomes the *next* (3)→(2) iteration one layer up. Driving (2) from a dependency map — rather than a file-by-file sweep — is the direct antidote to the original failure (which was *assuming* coverage).

**Decisions:**
- **𝕊 (sedenions) complete now** — full sedenion tier in phase (1), not deferred. The 42 zero divisors are the *witness* for loss-of-division/alternativity/composition (see §3), so 𝕊 is foundational, not optional.
- **CTH is the dependency-map home** — phase (3) is a view over the CTH (provenance/status already per-anchor), not a parallel artifact.

---

## 3. "Operations-complete" — the property matrix (phase-1 exit spec)

**Principle (beekeeper):** the tower must include not only the *numbers* (elements per level) but **all the operations you can do on those numbers per level** — and the truth-value, *with proof*, of every law. An algebra is its elements **together with its operations and laws**; proving only "the 16-dim algebra exists" is the partial coverage that fooled us before.

This makes "complete" a **bounded property matrix**: rows = canonical operations/laws; columns = the five levels; **every cell is a proof obligation.** ✓ = theorem; ✗ = **witnessed counterexample** (not mere `¬∀`).

| Operation / law | ℝ | ℂ | ℍ | 𝕆 | 𝕊 |
|---|:--:|:--:|:--:|:--:|:--:|
| Addition, 0, −x, ℝ-scaling | ✓ | ✓ | ✓ | ✓ | ✓ |
| Multiplication, 1 | ✓ | ✓ | ✓ | ✓ | ✓ |
| Conjugation x\* (anti-automorphism) | ✓ | ✓ | ✓ | ✓ | ✓ |
| Norm N(x)=xx\*, Re/Im parts | ✓ | ✓ | ✓ | ✓ | ✓ |
| Cayley-Dickson doubling (constructor) | — | ✓ | ✓ | ✓ | ✓ |
| **Total order** | ✓ | ✗ | ✗ | ✗ | ✗ |
| **Commutativity** | ✓ | ✓ | ✗ | ✗ | ✗ |
| **Associativity** | ✓ | ✓ | ✓ | ✗ | ✗ |
| **Alternativity** | ✓ | ✓ | ✓ | ✓ | ✗ |
| Flexibility / power-associativity | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Multiplicative norm (composition)** | ✓ | ✓ | ✓ | ✓ | ✗ |
| **Division / inverse / no zero-divisors** | ✓ | ✓ | ✓ | ✓ | ✗ |

**Witnesses for the ✗ cells (the foundation's real content):**
- ℂ loses order; ℍ loses commutativity (`ij = −ji`); 𝕆 loses associativity (a specific non-associating triple); 𝕊 loses alternativity + composition + division → **the 42 zero divisors are the witness**.

**Diagnostic operations that close the surface (finite/canonical):** commutator `[x,y]=xy−yx` and associator `[x,y,z]=(xy)z−x(yz)`. Every standard law is expressible via these, so "all operations per level" is bounded and checkable.

**Decision (beekeeper): include Moufang/identities** — the named higher identities that survive at 𝕆: the three **Moufang identities**, **Artin's theorem** (2-generated subalgebra is associative), the **Hurwitz/composition theorem** statement, flexibility, diassociativity.

**Phase-1 exit artifact:** a **proof-coverage manifest** = this matrix, every cell proven (✓) or witnessed (✗), zero `sorry`. It is the checkable definition of "(1) done" and the pre-filled bottom rows of the phase-(3) CTH map.

---

## 4. "What are we missing?" — Oppenheimer's hard pass

Per beekeeper instruction to think hard about overlooked structure and higher-level fruit. Dispositions: **IN** (add to phase-1 matrix), **FRONTIER** (document as signpost), **OMIT** (defer w/ rationale).

### 🟢 IN phase 1 (cheap, foundational, at risk of silent omission)
| Addition | Why load-bearing |
|---|---|
| **Bilinear/inner-product form** (polarization of N: ⟨x,y⟩=Re(x ȳ)) | This **is** the metric — connects algebra to geometry. Part of the norm surface. |
| **exp / log** (well-defined via power-associativity) | The evolution axiom `ψ(t)=exp(−Ht)ψ₀` needs it. Assumed, never proven well-defined. |
| **Cross product on Im** (3D at ℍ, **7D at 𝕆**) | Antisymmetric part of × ; the 7D cross product's automorphism group **is G₂** — bridge to the gauge story. The only two cross products that exist. |
| **Zero-divisor *structure*** (graph/symmetry), not just count | QBP: "zero divisors are seams." Inter-cell topology rests on the *structure*, not the number 42. |
| **Idempotents & nilpotents at 𝕊** | Appear when division is lost; Furey's SM uses *primitive idempotents* — foundational, not phase-2. |

### 🟡 FRONTIER — higher-level fruit (document as signposts in the Wisdom Ledger)
| Structure | Potential fruit |
|---|---|
| **Triality at 𝕆** | Unique to dim 8; historically linked to *three generations* / three-ness. Independent source of "3" vs dim(Im ℍ). |
| **Unit spheres / Hopf fibrations** | S⁰,S¹,S³,S⁷ from the four division algebras; Hopf maps host instantons/monopoles/twistors. **S⁷ is a Moufang loop, not a group.** |
| **Tensor products ℂ⊗ℍ⊗𝕆 (Dixon algebra)** | ⚠️ SM-from-algebra programmes (Dixon/Furey) build on *tensor products of the tower*, not single levels. Proving levels in isolation but never defining `⊗` may miss the structure the physics uses. **Borderline-IN.** |
| **Exceptional Jordan algebra h₃(𝕆) → magic square → F₄/E₆/E₇/E₈** | Natural home for *octonionic gravity & grand unification*. The signpost for "when we reach for gravity / Universe 1, look here." |
| **𝔽₂ substrate of the Fano plane** (PG(2,𝔽₂)) | Finite-field combinatorial object under octonion ×; relevant to the FORCED-vs-SELECTED question. |

### ⚪ OMIT + document (Wisdom Ledger)
- **CD algebras beyond 𝕊** (32D+): identity-ladder stabilizes after 𝕊 (nothing new lost beyond alternativity+division), though ZD structure keeps enriching. *Trigger to revisit:* inter-cell topology needs >16D.
- **Peirce decomposition, Albert-algebra machinery:** phase-3+ tooling; pulls in when SM embedding needs it.
- **Base fields beyond ℝ:** except **ℚ** (needed now for exact Lean arithmetic) and **𝔽₂** (Fano).

---

## 5. RESOLVED — norm-form signature → complexification in scope (synthesis)

**The one omission that could gate "why gravity."** N(x)'s polarization is a metric; the *division* tower (ℝℂℍ𝕆) is **positive-definite → Euclidean**, but the **split** forms (split-ℂ (1,1), split-ℍ, **split-𝕆 (4,4)**) carry **indefinite/Lorentzian** signature, and much SM-from-octonions work uses *split*-octonions. **Gravity needs Lorentzian signature** — building only the compact tower may silently bake in Euclidean space and foreclose gravity at the foundation.

### Theory-team verdict — UNANIMOUS (B)
All four voices convened and converged on **(B) division tower now, defer split**:
- **Gemini/Furey:** 𝕆 and split-𝕆 are two *real forms of the same complexified algebra*; split forms carry native zero-divisors — baking them in trades Hurwitz rigidity for an ad-hoc choice. Lorentzian signature can emerge via complexification (ℂ⊗𝕆) or the 𝕆→ℍ crystallisation.
- **Gemini/Feynman:** "If you bake split algebras into the basement, you answer *why time?* with *because we put it there* — you ruin the explanatory power of emergence." Time is the order parameter of the ℍ-crystal; Euclidean bulk → Lorentzian boundary is standard holography.
- **Claude/Wilson:** signature is a **real-form / reality-condition choice**, not a forced UV ingredient; building split forms is *not* more neutral (it picks (4,4) just as division picks compact). Universality favors letting signature emerge. *Guardrail:* the basement must not call its norm "the spacetime metric."
- **Claude/Jaynes:** A pays zero present discriminating power for permanent foundational mass; insure cheaply via a **loud pre-committed revisit-trigger**, not by over-building. The Type-II error (rewrite) is *observable*, so it can be caught late and cheaply.

### Decision (beekeeper): SYNTHESIS — complexification in scope, over pure-B
Build the **complexified tower (𝕆_ℂ + lower-level complexifications)** in phase 1 so **both** the Euclidean division forms **and** the split/Lorentzian forms are **provable real forms** from one foundation. Lorentzian signature is **reachable-by-theorem, not hard-coded**.

**Decisive rationale (beekeeper):** holography is **independently, provably real** (lab optical holograms; holographic principle / AdS-CFT). Building the foundation so the holographic map is *provable* gives QBP an **external anchor** — confirming the math holds in *this* universe, raising the evidential weight of the whole stack. The holographic map *is* a Euclidean-bulk → Lorentzian-boundary correspondence (noted by Furey and Feynman), so expressing and proving it **requires both real forms reachable from one foundation** = complexification. This honors the teams' "don't hard-code the minus-sign" (signature still *emerges* via real-form choice) AND the beekeeper's "in scope now" insurance instinct (the structure making gravity/holography reachable is foundational and proven). Strictly stronger than pure-B.

**Three mandatory guardrails (conditions on the decision):**
1. **Non-identification clause** — the basement explicitly marks ⟨x,y⟩=Re(x·conj y) as the *algebraic norm form*, NOT the spacetime metric.
2. **Complexification-friendly proofs** — basement results expose the complexified algebra so selecting a real form later is additive, not a rewrite.
3. **Loud pre-committed revisit-trigger** — fires if the emergence route cannot produce Lorentzian signature above the algebra layer.

**Named target theorem:** the foundation must be able to express and prove the **Euclidean→Lorentzian holographic map**.

**qbp-architecture to be looped in** to reflect this in foundations architecture docs.

---

## 6. The Wisdom Ledger mechanism

Omissions become a **debugging resource for the theory.** Recorded as CTH anchors (new class, e.g. `WISDOM-*` / `OMITTED-*`), consistent with the existing `First-Wisdom` / `WISDOM-003` tradition. Each anchor carries four fields:

1. **what** — the structure/operation set aside
2. **why deferred** — the rationale
3. **trigger** — what would make us revisit it
4. **potential fruit** — what it might unlock

When phase-2 physics hits a wall: *query the omission ledger first* — "did we set aside something load-bearing?"

---

## 7. Decisions ledger (this session)

| # | Decision | By |
|---|---|---|
| D1 | Octonion orientation: re-derive-native / F3-master; import-literal withdrawn | beekeeper |
| D2 | Phased plan (1)→(3)→(2) | beekeeper |
| D3 | 𝕊 complete now (full sedenion tier in phase 1) | beekeeper |
| D4 | CTH is the dependency-map home (phase 3 = view over CTH) | beekeeper |
| D5 | Operations-complete property matrix is the phase-1 exit spec | beekeeper |
| D6 | Include Moufang/identities in the operation surface | beekeeper |
| D7 | Add the 🟢 items to the phase-1 matrix; **promote FRONTIER→IN** per team verdict: L_x/R_x (→Cl(6)/spinors), primitive idempotents at 𝕆 (not just 𝕊), ℂ⊗𝕆, h₃(𝕆) observables, 𝕆P² + G₂⊃SU(3) automorphism chains | Oppenheimer rec + team |
| D8 | Wisdom Ledger as CTH anchors (4-field) | beekeeper rec (pending confirm) |
| D9 | **Q2: derived structure ops in scope** (automorphism groups, subalgebra-embeddings, doubling/trace forms) | beekeeper |
| D10 | **Signature: complexification in scope (synthesis)** — 𝕆_ℂ so both real forms provable; 3 guardrails; holographic map as named target theorem | beekeeper (over unanimous team pure-B) |

### Resolved open items
- ~~O1: signature/split-form question~~ → **RESOLVED** as D10 (see §5).

---

## 8. Next actions

- [ ] Theory teams (Furey/Feynman + Wilson/Jaynes) rule on the signature question (§5) — **in progress**
- [ ] Completeness-critic pass: teams + Foundations Auditor adversarially attack the §4 list before it's frozen
- [ ] Loop in **qbp-architecture** after team verdict — reflect outcome in foundations docs (may change architecture)
- [ ] File issues: phase-1 matrix + 3 obligations + 🟢 additions + Wisdom-Ledger anchors (after architecture sign-off)
- [ ] Update this document with the team verdict and architecture response
