# Constants target — does QBP derive a dimensionless constant purely from the algebra?

**Status:** DELIVERABLE (option 1, #570 target 2) · **Date:** 2026-06-17
**Method:** apply the #570 gate (g1 derived-not-fitted · g2 orthogonal-to-fitted-inputs · g3 dimensionless) to QBP's **existing** constant-derivation work (the f0/spectral-action investigation `archive/QBP-f0-investigation-report-v1.0.md`; the Koide test `archive/QBP-TEST-K-*`) — *not* a fresh "derive α" hunt (which would be the f(0)/#535 numerology trap).
**Why this is the right move:** QBP already did serious, **unusually honest** constant work (the f0 report explicitly separates "structural prediction" from "coincidence of notation," and its own red team caught the overselling). The gate adjudicates which attempts are real.

---

## 1. Gate-check of QBP's existing constant attempts

**(corrected after the adversarial BLOCK — my first-draft "PASS" marks were too generous.)**

| Attempt | What it is | Gate verdict (corrected) |
|---|---|---|
| **sin²θ_W = 3/8** | Hessian eigenvalue ratio = the **SU(5)-GUT value** (Georgi–Glashow 1974) | ❌ **NOT a derivation** — a *tautology of the embedding*: once the SM/GUT group structure is hosted in the algebra, 3/8 follows automatically. Recovery of standard GUT kinematics; **not content-distinct**, not a QBP constant. |
| **δ₁ ≈ δ₃** | U(1)/SU(3) threshold corrections equal, from equal sedenion-Hessian multiplicity | ❌ **FAILS g1 (look-elsewhere)** — selected as **best of 12 models** (χ²=0.006): a model choice fitted post-hoc. Not zero-parameter; agreement only 9%. The multiplicities are algebra-fixed, but the *map* "δ ∝ multiplicity" was chosen after seeing the data. |
| **C=12, the 42 ZD-planes, uniform Hessian** | proven invariants (`QBP_HessianTheorem.lean`) | ✅ proven **algebraic invariants** — real mathematics, but *internal structural facts*, **not predictions of any physical constant** (value or content-distinct relation). |
| **Koide Q → 2/3** | charged-lepton ratio = 2/3 to 6×10⁻⁶ | ⚠️ a sharp empirical relation QBP **tests, does not derive** (the 2/3 democratic structure is not shown to follow from the algebra). Not a QBP derivation. |
| **f(0)=2/α_unif · absolute α,α_s · Higgs mass** | value attempts | ❌ **FAIL** — f(0) *chosen* to match α_em (circular); ε *from the RGE* (tautological); m_H needs a *free parameter*. No value derived. |

## 2. The verdict (hardened) — nothing content-distinct passes

My first draft said "relations pass, values fail." **The adversarial gate BLOCKED that as face-saving, correctly.** Corrected:

> **On the constants, QBP produces nothing content-distinct from standard physics.** The "relations" it gets — sin²θ_W=3/8, the multiplicity ratios — are **standard group-theory consequences of embedding the SM structure in the algebra** (any SU(5)/SO(10)-flavoured model gives the same); they are *tautologies of the embedding*, not QBP-novel. The one QBP-specific relation (δ₁=δ₃) **fails the gate** on the look-elsewhere effect. And **no continuous value** (α, masses, m_H) is derived — every attempt imports a fitted/measured magnitude.

So the honest position is **harder** than "structure passes": the structure that "passes" is **borrowed group theory, not QBP content**, and QBP adds **no content-distinct constant prediction** — neither a value nor a novel relation. On the constants, QBP is "**a kinematic classification scheme devoid of the dynamical machinery needed to generate a real universe**" (adversary). Its genuinely-proven invariants (C=12, the 42) are real mathematics but predict no physical constant.

## 3. What genuinely holds (very little)

- **No content-distinct constant** — no value, and no relation that isn't already a standard group-theory consequence of the embedding. The "successes" (3/8, the multiplicity ratios) are recovered standard kinematics; δ₁=δ₃ fails look-elsewhere; Koide is tested-not-derived.
- **Proven algebraic invariants** (C=12, the 42 ZD-planes) are solid mathematics but predict **no physical constant.**
- **All continuous values fail** — f(0)→α (circular), absolute couplings (RGE-tautological), m_H (free parameter). QBP's own honest f0 report already reached this ("predicts the PATTERN but the MAGNITUDE comes from the measurements").

## 4. The consolidated diagnosis (corrected, robust across the threads)

| Thread | Genuinely QBP-content & gate-passing? |
|---|---|
| **Footprint (#571)** | ✅ *one* genuine pass — n = CD-dimension (adversary-confirmed) — but **pyrrhic** (predicts null in every accessible venue) |
| **Constants (here)** | ❌ **nothing content-distinct** — recovered GUT kinematics (tautology) + δ₁=δ₃ (look-elsewhere) + no value |
| **v→constants #564 / triangle #566** | ❌ free coefficients / ∞−∞ until truncation |

> **Corrected verdict:** QBP's only genuine, content-distinct, gate-passing result is the **coarse CD-level footprint (#571), and it is pyrrhic.** On the **constants** it adds nothing standard group theory doesn't already give, and it derives **no value**. So QBP is **a kinematic classification scheme** — it organizes the SM's group-theoretic structure in division-algebra language (a real, if not novel, organizing achievement) but, with the current algebra, it **generates no content-distinct physical prediction** beyond the one pyrrhic footprint. The "structure passes" comfort of the first draft is withdrawn: most of that "structure" is borrowed GUT kinematics, not QBP content.

## 5. The honest resting point (option-1 result)

Option 1 (the purely-algebraic derivations) has now been pushed on its two sharpest targets — the footprint and the constants — and the result is decisive: **the gate is passable only by coarse, mostly-borrowed structure; no content-distinct value or novel relation survives it.** Unless the triangle loop-closure (#566) genuinely over-determines (open, hard, regularization-gated), the continuous values are **beyond the current algebra**. This is the honest resting point: **QBP is a sound division-algebra *organization* of known SM kinematics, not (yet) a *generator* of new physics** — and saying otherwise requires either the (unbuilt) loop-closure machine or a richer algebra.

## 6. Provenance
Option 1, #570 target 2, 2026-06-17. Gate-application to QBP's existing f0/Koide work, built on QBP's own (commendably honest) f0 investigation (`archive/QBP-f0-investigation-report-v1.0.md`). The first draft's "relations pass, values fail" framing was **adversarially BLOCKED** (Gemini Furey/Feynman) as face-saving — the "relations" are borrowed GUT kinematics, δ₁=δ₃ fails look-elsewhere, no value derived. Hardened to: QBP is a division-algebra *organization* of SM kinematics with no content-distinct constant prediction (only the pyrrhic #571 footprint survives). Recorded by @qbp-oppenheimer.
