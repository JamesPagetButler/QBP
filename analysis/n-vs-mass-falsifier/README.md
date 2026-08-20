# n vs mass — the decisive falsifier for QBP's footprint prediction

**Status:** COMPLETE (theory-side computation) · **For:** Test C falsifier (the #567 verdict's make-or-break), EXP-10 / QBP-APC · **Date:** 2026-06-16
**The test (from the Test C verdict, #567):** derive the algebraic footprint **n** from the QBP structure *without reference to mass*. If n_A/n_B = m_A/m_B → QBP's asymmetry is degenerate with standard QM (recoil ∝ k²/m) and the distinctive prediction is **dead**. If n_A/n_B diverges from the mass ratio → QBP has a genuine, testable signal.
**Method:** apply QBP-APC's own footprint rule (`archive/QBP-HYPOTHESIS-Algebraic-Particle-Classification.md`) to the species actually used in Test C experiments.

---

## 1. QBP-APC's footprint rule is internally inconsistent — and that inconsistency *is* the test

QBP-APC gives two non-equivalent statements of the within-ℍ footprint:
- **Reading A — line 193 (verbatim):** *"Fidelity asymmetry scales with mass ratio within the ℍ level… the difference comes from internal DOF count (which scales roughly with mass/complexity)."* → **n ∝ mass.**
- **Reading B — line 181 (verbatim):** footprint = *"4 real DOF per boundary step, plus any internal structure (spin states, colour charges, generation indices)."* → **n = 4 + internal structure** (which is *not* the same as mass).

All atomic ions are massive ⇒ all ℍ-encoded ⇒ the base 4 is common; the *difference* is the disputed internal term. Which reading holds decides whether QBP is degenerate with QM or testable.

## 2. The computation (applied to the Test C species)

The decisive probe is an **isotope pair**: near-equal mass, very different nuclear spin I (hence very different internal DOF).

| Pair | mass ratio | footprint ratio, Reading A (n∝mass) | footprint ratio, Reading B (n∝2I+1 internal) |
|---|---|---|---|
| ⁴⁰Ca⁺ (I=0) / ⁴³Ca⁺ (I=7/2) | 1.075 (≈1) | ≈ 0.94 (**tracks mass**) | ≈ 0.42 (**diverges from mass**) |
| ⁸⁸Sr⁺ (I=0) / ⁸⁷Sr⁺ (I=9/2) | 0.989 (≈1) | ≈ 1.01 (**tracks mass**) | ≈ 0.36 (**diverges from mass**) |

(`compute_n.py`; the integer n-values are schematic — the *structural* result is what matters: for an isotope pair the mass ratio ≈ 1 while the internal-structure footprint ratio is far from 1.)

**Result:**
- **Under Reading A, n does NOT decouple from mass** — for every species pair n_A/n_B ≈ m_A/m_B ⇒ **degenerate with standard QM/recoil ⇒ QBP's distinctive prediction is DEAD.** This is QBP-APC's *primary stated* prediction (line 193 literally says "scales with mass ratio").
- **Under Reading B, n decouples from mass** — an isotope pair has mass ratio ≈ 1 but a footprint ratio far from 1, set by nuclear spin / internal structure, *not* mass. This is the **only survival path.**

## 3. Verdict on "compute n vs mass" (hardened after the adversarial BLOCK)

The first draft proposed an isotope-pair "escape." **The adversarial gate (Gemini Furey/Feynman) BLOCKED it as a mirage, and it is right.** The honest verdict is harder:

> **QBP's footprint n is degenerate with standard physics BY CONSTRUCTION.** QBP-APC *defines* n as "4 + internal structure (spin states, …)" — i.e. **out of standard degrees of freedom**. Whether you read the within-ℍ term as ∝ mass (line 193 → recoil/Lamb-Dicke degeneracy) or as ∝ internal spin/hyperfine (line 181), in **both** cases n is built from the *same parameters standard atomic physics already uses*. There is **no decoupling**, because there is no QBP-specific quantity — n is a relabeling of standard DOF.

## 4. Why the isotope "escape" collapses (not a nuisance — a total collapse)

Switching ⁴⁰Ca⁺ (I=0) → ⁴³Ca⁺ (I=7/2) does **not** isolate n from mass; it **changes the atomic physics wholesale** — from an optical/Zeeman qubit to a hyperfine manifold, with different Raman transitions, couplings, detunings, and error channels. Any measured asymmetry there is *correctly* attributed to standard atomic physics. And the deeper point: because QBP *defines* its footprint **using** nuclear spin / internal states, the isotope difference QBP would key on **is** standard physics — the test is degenerate at the level of *definition*, not just measurement. There is no ion pair (and no within-ℍ pair generally) where this n separates from standard internal-structure physics.

## 5. The honest endpoint

> **As currently formulated, QBP has no testable distinctive entanglement-asymmetry prediction.** Its footprint n is defined out of standard DOF (mass/spin/complexity), so it is degenerate with standard physics by construction — there is no escape via isotopes, mixed species, or "internal structure." This is not a pass/fail *gate* (my earlier "first clean algebra-only gate" framing is **retracted** — there is no threshold to pass); it is a diagnosis that **the theory is incomplete at exactly this point.**

**The single requirement (the adversary's mandate, adopted):** derive n **purely from the algebra** — from the representation-theoretic / Cayley-Dickson *dimensional* structure (e.g. the dimension of the CD level required to host the particle's state) — with **no ad-hoc appeal to mass, nuclear spin, or "complexity."** Only an n that is *mathematically orthogonal* to the standard atomic parameters could be non-degenerate. QBP-APC does not do this; it defines n *via* those parameters. Until a purely-algebraic n exists, QBP's most distinctive prediction is **not just untestable in a venue (#567) — it is degenerate by construction.**

This is the deepest of the session's clean negatives: not "the experiment can't see it" (#567) but **"the prediction, as defined, carries no content distinct from standard physics."** The constructive residue is precise and small: a *purely-algebraic, parameter-free* definition of n (CD-dimension / rep-theory) is the one thing that could give QBP a real prediction — and it does not yet exist.

This is the first time QBP's distinctive prediction has a **clean pass/fail gate that needs only the algebra** (no dynamics, no experiment): *does the algebra give a precise, mass-independent n, or not?*

## 6. Provenance
The #567 Test C verdict's n-vs-mass falsifier, executed against QBP-APC's own footprint rule. Found the line-181/193 inconsistency. The first draft proposed an isotope-pair escape; the adversarial gate (Gemini Furey/Feynman) **BLOCKED** it — n is degenerate-by-construction (defined out of standard DOF), so the escape is a mirage and "clean gate" was an overclaim. Hardened to the honest endpoint: QBP needs a purely-algebraic (CD-dimension / rep-theory) n with no appeal to standard parameters, which does not yet exist. Recorded by @qbp-oppenheimer.
