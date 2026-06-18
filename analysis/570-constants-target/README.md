# Constants target — does QBP derive a dimensionless constant purely from the algebra?

**Status:** DELIVERABLE (option 1, #570 target 2) · **Date:** 2026-06-17
**Method:** apply the #570 gate (g1 derived-not-fitted · g2 orthogonal-to-fitted-inputs · g3 dimensionless) to QBP's **existing** constant-derivation work (the f0/spectral-action investigation `archive/QBP-f0-investigation-report-v1.0.md`; the Koide test `archive/QBP-TEST-K-*`) — *not* a fresh "derive α" hunt (which would be the f(0)/#535 numerology trap).
**Why this is the right move:** QBP already did serious, **unusually honest** constant work (the f0 report explicitly separates "structural prediction" from "coincidence of notation," and its own red team caught the overselling). The gate adjudicates which attempts are real.

---

## 1. Gate-check of QBP's existing constant attempts

| Attempt | What it is | g1 derived? | g3 value or relation? | Gate verdict |
|---|---|---|---|---|
| **sin²θ_W = 3/8** | Hessian eigenvalue ratio (the SU(5)-GUT value) | ✅ group-theoretic | a **rational relation** | ✅ **PASS** (structural; not unique to QBP) |
| **δ₁ ≈ δ₃** | U(1) & SU(3) threshold corrections equal, because sedenion-Hessian eigenspaces have equal multiplicity (mult(4)=mult(12)=4) | ✅ "nobody chose these; they follow from the algebra" | **zero-parameter relation**, verified to 9.4% | ✅ **PASS** (the strongest; a genuine zero-parameter algebraic prediction) |
| **C = 12, the 42 ZD-planes, uniform Hessian** | proven algebraic invariants (`QBP_HessianTheorem.lean`) | ✅ proven | exact integers | ✅ **PASS** (structural invariants) |
| **Koide Q → 2/3** | charged-lepton ratio = 2/3 to 6×10⁻⁶; runs *toward* 2/3 at high E | ⚠️ QBP *tests* it; does **not** derive the 2/3 democratic structure from the algebra | a relation | ⚠️ **PARTIAL** — the *relation* is sharp and real, but QBP notes it, doesn't derive it (the "3 generations" may be algebraic à la Furey; the specific 2/3 is not shown derived) |
| **f(0) = 2/α_unif** (→ α value) | the spectral cutoff matched to α | ❌ f(0) was **chosen** to match α_em (partial circularity); magnitude from measurement | a **value**, fitted | ❌ **FAIL** as a derivation of α's value (passes only as a relation among already-measured couplings) |
| **Higgs mass** (λ_H=g² → m_H) | spectral-action prediction | ❌ gives 170 GeV; 125 needs a **free parameter** (Chamseddine-Connes singlet) | a value | ❌ **FAIL** |
| **absolute α_em, α_s magnitudes** | the coupling values | ❌ "ε is determined by the RGE… almost tautological — the magnitude comes from the measurements" | values | ❌ **FAIL** |

## 2. The verdict — RELATIONS pass, VALUES fail (the same boundary as the footprint)

> **QBP's algebra gate-passingly derives STRUCTURE and RELATIONS among the constants — rational group-theoretic ratios (sin²θ_W = 3/8) and zero-parameter multiplicity relations (δ₁ = δ₃, the strongest, verified to ~9%) — but it does NOT gate-passingly derive the absolute continuous VALUES (α, masses, m_H).** Every value-attempt requires a fitted or measured magnitude: f(0) is *chosen* to match α_em (circular), the threshold magnitude ε *comes from the RGE/measurements* (tautological), the Higgs mass *needs a free parameter*.

This is **exactly the boundary the footprint hit (#571)**: the algebra gives gate-passing *structure* (CD-level n; multiplicities; rational relations) and *not* gate-passing *values* (within-level n; α; masses). Two independent threads, one boundary.

## 3. What this means (honest, and it gives QBP real credit)

- **The positive (real, but appropriately humbled):**
  - **sin²θ_W = 3/8 is the standard SU(5)-GUT value** (Georgi-Glashow, 1974) — QBP *reproduces* it from the Hessian eigenvalue ratios, it does **not** derive something new. Gate-passing but **not content-distinct from GUT/group theory.** Credit: consistency, not novelty.
  - **δ₁ = δ₃ is QBP-specific but must carry a look-elsewhere caveat:** the f0 report selected the multiplicity model as best of **12 models tested** (χ²=0.006), so "zero-parameter" applies to the *winning* model, not to the search — the look-elsewhere effect weakens it, and the agreement is only **9.4%**. It is *suggestive* (the sedenion eigenspace dims 4,8,4 were genuinely not chosen to fit, and δ₁=δ₃ follows), **not decisive.**
  - **C=12, the 42 ZD-planes, uniform Hessian** are proven algebraic invariants (`QBP_HessianTheorem.lean`) — solid, but structural, not constant *values*.
  So QBP's gate-passing constant content is **real but modest**: it reproduces the standard GUT relation (not novel) plus one suggestive-but-loose QBP-specific multiplicity relation (δ₁=δ₃, 9%, look-elsewhere-caveated). It is **not** a derivation of any constant *value*.
- **The limit (decisive for option 1):** the continuous **values** do not yield. The fine layer (α to its digits, the mass spectrum, m_H) needs a magnitude-generating mechanism (dynamics/RGE) that **imports measured inputs**, so it fails the gate — and #564 already showed the dynamical route has free coefficients. QBP's own f0 report reached this conclusion independently ("predicts the PATTERN but the MAGNITUDE comes from the measurements").

## 4. The consolidated diagnosis (now robust across three threads)

| Layer | Footprint (#571) | Constants (here) | Verdict |
|---|---|---|---|
| **Structure / relations** | n = CD-dimension (gate-pass) | sin²θ_W=3/8, δ₁=δ₃, C=12, the 42 (gate-pass) | ✅ QBP derives these purely-algebraically |
| **Continuous values** | within-level n (fails) | α, masses, m_H (fail) | ❌ need fitted/measured magnitude |

> **QBP is a sound theory of ALGEBRAIC STRUCTURE that gate-passingly predicts RELATIONS (multiplicities, rational group-theoretic ratios, level structure) — but, with the current algebra, it does not derive the continuous constant VALUES.** That is its honest predictive reach. The values are not merely underived; the gate analysis (across footprint + constants + the #564 no-shortcut + the #566 ∞−∞) indicates they are **beyond the finite algebra** without a magnitude-generating mechanism that imports physics.

## 5. Next under #570 / the honest resting point
- **Strengthen the real positives:** the δ₁=δ₃ prediction deserves a tighter test (current 9.4%) and a Lean-backed derivation of the multiplicity structure; sin²θ_W=3/8 and Koide deserve a *derivation* of the rational (does the octonion 3-generation structure force Koide's 2/3?). These are where QBP's gate-passing content can be **sharpened**.
- **The values are the wall.** Unless the triangle loop-closure (#566) genuinely over-determines (the open, hard, regularization-gated question), the continuous values do not come from the algebra. This is the coarse-algebraic resting point the footprint already suggested, now confirmed by the constants.

## 6. Provenance
Option 1, #570 target 2, 2026-06-17. The gate-application to QBP's existing f0/Koide work, and the relations-pass/values-fail verdict consolidating the footprint boundary, are this deliverable's synthesis — built on QBP's own (commendably honest) f0 investigation. `archive/QBP-f0-investigation-report-v1.0.md`. Recorded by @qbp-oppenheimer; adversarially tested before adoption (see PR thread).
