# Purely-algebraic footprint n — first derivation (option 1, #570 target 1)

**Status:** FIRST DELIVERABLE of the purely-algebraic-derivation program (#570) · **Date:** 2026-06-17
**Target:** derive the footprint n **purely from the algebra** (no appeal to mass/spin/complexity), apply the #570 gate, and resolve the QBP-APC line-181/193 inconsistency (#568).
**Discipline:** the #570 gate (AC-gate-1 derived-not-fitted · AC-gate-2 orthogonal-to-mass · AC-gate-3 dimensionless) applied to *this* derivation.

---

## 1. The derivation

QBP-APC already carries the answer implicitly: the encoding levels ℝ/ℂ/ℍ/𝕆 have "Real DOF" 1/2/4/8 = **the Cayley-Dickson dimension** 2^k. Read *purely*, the footprint is

$$\boxed{\,n = \dim_{\mathbb R}(\text{the CD algebra encoding the particle}) = 2^k,\quad k\in\{0,1,2,3\}\,}$$

This is a genuine algebraic quantity (the dimension of the CD level), not a fitted or borrowed one.

## 2. The gate adjudicates the APC line-181/193 inconsistency

QBP-APC stated the within-ℍ footprint two incompatible ways (#568). The #570 gate decides among the three readings:

| Reading of n | AC-gate-1 (derived?) | AC-gate-2 (mass-orthogonal?) | Verdict |
|---|---|---|---|
| line 193: n ∝ mass/complexity | ❌ borrows mass | ❌ *is* mass | **DEGENERATE w/ QM** |
| line 181: n = 4 + internal spin DOF | ❌ borrows spin DOF | ❌ spin drives the standard gate physics | **DEGENERATE by construction (#568)** |
| **PURE: n = CD-dimension (2^k)** | ✅ it *is* 2^k | ✅ quantized to {1,2,4,8}, mass-orthogonal | ✅ **GATE-PASSING** |

> **Result:** only the **CD-dimension reading survives the gate.** The "mass" and "internal-spin-DOF" readings both fail AC-gate-1/2 (they import standard-physics parameters). **QBP-APC should be corrected** to define n = CD-dimension and drop the line-181/193 formulations. This is the first QBP bridge-quantity to pass #570 — a genuine positive.

> **Sharp objection, answered (does the level smuggle mass back in?):** the ℂ↔ℍ level boundary *is* the massless↔massive boundary, so the level correlates with whether a particle has mass. But it correlates only with the **massless/massive binary**, not with the **mass magnitude**: n = 4 for *every* massive particle, identically, regardless of its mass value. The recoil/Lamb-Dicke degeneracy that killed the earlier readings depends on the mass *magnitude/ratio* (recoil ∝ k²/m); n is orthogonal to *that* — for any two ions n_A/n_B = 1. So AC-gate-2 holds in the sense that matters (n carries no mass-*magnitude* information), even though the level encodes the binary mass>0. This is exactly why it escapes #568's degeneracy.

## 3. What the gate-passing n predicts

With n = CD-dimension, the footprint asymmetry ΔF ∝ (n_A − n_B):
- **Same CD-level** (ion–ion, atom–atom: both ℍ, n=4): ΔF ∝ **0**. QBP predicts **zero algebraic species-asymmetry** — any asymmetry seen in mixed-species ion gates is **100% standard physics** (mass-ratio Lamb-Dicke, recoil, heating), **zero QBP content.** This is a *definite, falsifiable* statement (an irreducible within-level algebraic asymmetry would refute it), and it is **clean** — not the degenerate-by-construction failure of #568, but a genuine algebraic null.
- **Cross-level** (atom ℍ n=4 vs photon ℂ n=2): ΔF ∝ **(4−2)=2**, **mass-independent.** This is QBP's one accessible *distinct* footprint prediction.

## 4. Honest limitations (the gate is passed, but the quantity is coarse)

1. **Coarse.** n is quantized to {1,2,4,8} — it distinguishes algebra *levels*, not particles within a level. So it makes **no within-level prediction** beyond "zero."
2. **The finer (Furey) n doesn't help the experimental particles.** Furey's ℂ⊗𝕆 minimal-ideal dimensions give a finer, *also mass-orthogonal* footprint for **elementary fermions** (mass is not a Furey input). But entanglement experiments use **photons** (ℂ, n=2) and **composite atoms/ions** (no clean minimal ideal). A composite footprint summed over constituents tracks constituent count ~ mass → fails AC-gate-2. So for the *accessible* particles the CD-level n is the **finest gate-passing footprint** — there is no mass-orthogonal within-level refinement.
3. **Venue.** The one accessible distinct prediction (atom-photon cross-level) still carries the EXP-10 (1−1/γ) suppression → needs relativistic γ (#567 §4). So it is gate-passing and falsifiable-in-principle but not near-term.

## 5. Net (the first surviving result)

> **QBP's footprint, correctly defined, IS purely algebraic and mass-orthogonal: n = the Cayley-Dickson dimension.** It passes the #570 gate (the first bridge-quantity to do so), it **adjudicates the APC inconsistency** (only this reading survives — a concrete theory correction), and it makes definite predictions: **exactly zero algebraic asymmetry within a CD-level** (so trapped-ion Test C is predicted null, cleanly), and a **mass-independent ΔF ∝ (n_A−n_B) across levels** (atom-photon, the one accessible distinct test, relativistic-γ venue).
>
> This is not the degeneracy of #568 — it is a clean, gate-passing, falsifiable footprint. Its honest price is **coarseness**: it predicts null in every easy venue and a hard-to-access signal in the one venue where it's nonzero. QBP's footprint has *content distinct from standard physics*, but only at the cross-level boundary.

## 5b. Adversarial confirmation (Gemini Furey/Feynman) — confirmed gate-pass, but PYRRHIC

The adversarial gate **confirms the core claim** and sharpens the cost:
- **g1 (derived):** "not a mere relabeling… a pristine, non-fitted derivation. The first footprint that genuinely satisfies g1." ✅
- **g2 (mass-orthogonal):** "You legitimately pass g2" — n decouples from mass *magnitude* ("a Hydrogen atom and a Lead atom both sit flatly at n=4"); the global massless→ℂ / massive→ℍ correlation does not reintroduce the recoil degeneracy (which needs mass magnitude). ✅
- **APC adjudication:** "correct: you must purge the 'spin DOF' and 'n∝m' interpretations — n = CD-dimension is the unique gate-passing algebraic quantity." ✅
- **The concern — a PYRRHIC pass:** because n=4 for *all* matter, ΔF ∝ (n_A−n_B) = **exactly 0 for every matter-matter experiment** (ion-ion, isotope, atom-atom). QBP's gate-passing footprint thus predicts a **flat null across all near-term tabletop tests**; its only nonzero signal is cross-level (atom-photon) at relativistic γ — an "experimental desert." It is a *strictly falsifiable null prediction*, but it expects zero anomalous signal anywhere currently reachable.

**Verdict (Gemini): (b) passes but pyrrhic — genuine, correctly-scoped gate-pass; the price of algebraic purity is a flat null for accessible experiments.** This is recorded as-is: the first surviving result *is* a real positive (a gate-passing quantity + the APC adjudication), and it is honestly modest (no accessible distinct signal).

## 6. Next under #570
- Correct QBP-APC to n = CD-dimension; retire the line-181/193 readings (a clean-up PR against the APC doc).
- The remaining #570 targets (the #564 potential coefficients; the triangle loop-closure) are *not* resolved by this — they need their own purely-algebraic derivations.
- The atom-photon cross-level prediction is the empirical thread worth a dedicated EXP write-up (relativistic-γ venue), distinct from the (now-predicted-null) trapped-ion Test C.

## 7. Provenance
First deliverable of option 1 (#570), 2026-06-17. The CD-dimension footprint and the gate-adjudication of the APC line-181/193 inconsistency are this derivation's results; the Furey-ideal assessment bounds the within-level refinement. `gate_check.py`. Recorded by @qbp-oppenheimer; adversarially tested before adoption (see PR thread).
