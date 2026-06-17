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

## 3. Verdict on "compute n vs mass"

> **As QBP-APC primarily states it (Reading A, line 193), the footprint tracks mass — so n_A/n_B = m_A/m_B and QBP's asymmetry is degenerate with standard QM. By its own primary rule, QBP's distinctive trapped-ion prediction is dead.**
>
> **QBP's ONLY escape is to commit to Reading B** (the footprint is driven by mass-independent *internal structure* — nuclear spin / hyperfine / generation — not mass). This (a) requires **fixing the APC internal inconsistency** (lines 181 vs 193 contradict), and (b) yields a concrete, **mass-independent, near-term test: the isotope-pair footprint asymmetry** (⁴⁰Ca⁺/⁴³Ca⁺ or ⁸⁷Sr⁺/⁸⁸Sr⁺).

## 4. The residual confound (honest — Reading B is not yet clean)

Reading B is necessary but **not sufficient**. The internal structure QBP keys on (nuclear spin → hyperfine manifold) **also drives standard gate physics**: ⁴³Ca⁺ (hyperfine qubit) vs ⁴⁰Ca⁺ (Zeeman/optical qubit) use *different qubit transitions, laser couplings, and hyperfine-dependent error channels*. So a *standard* asymmetry exists at the isotope pair too — it is not the clean mass-cancellation it first appears. To separate a QBP footprint signal there, **QBP must specify n PRECISELY** — a definite algebraic formula (e.g. n = 4 + (2I+1)?) whose *functional dependence* on internal structure differs from the standard hyperfine error scaling. "n = 4 + internal structure" (qualitative) is not enough.

## 5. Net — the sharp, decidable task this leaves

| Outcome | Condition |
|---|---|
| **QBP distinctive prediction DEAD (degenerate w/ QM)** | if QBP holds Reading A (n ∝ mass) — its own primary statement |
| **Survives, testable** | iff QBP commits to Reading B *and* computes n as a precise mass-independent algebraic formula distinguishable from standard hyperfine physics |
| **Cleanest non-degenerate venue** | cross-level atom-photon (ℍ n=4 vs ℂ n=2 — algebra-set, mass-independent), but needs relativistic γ (#567 §4) |

**The decisive next theory task is now sharp and small:** (1) resolve the QBP-APC line-181-vs-193 inconsistency; (2) if Reading B, **derive n as an explicit algebraic function** (of spin/charge/generation, not mass) from the octonion/Clifford structure; (3) check it diverges from *both* the mass ratio *and* the standard hyperfine error scaling. Until (2), QBP's most distinctive prediction has **no mass-independent content** — and by its own primary text (Reading A) it is degenerate with QM.

This is the first time QBP's distinctive prediction has a **clean pass/fail gate that needs only the algebra** (no dynamics, no experiment): *does the algebra give a precise, mass-independent n, or not?*

## 6. Provenance
The #567 Test C verdict's n-vs-mass falsifier, executed against QBP-APC's own footprint rule. Found the line-181/193 inconsistency; identified the isotope-pair discriminator and its residual hyperfine confound. Recorded by @qbp-oppenheimer.
