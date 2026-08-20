# #564 — The v→constants keystone (first pass)

**Status:** WORKING — Sub-problem A built, Sub-problem C reduced, Sub-problem B is the open frontier · **Issue:** #564 (child of #559 + #539) · **Date:** 2026-06-14
**Discipline:** build the rigorous object → adversarially test → predict a dimensionless number or it dies.

---

## The keystone
Derive **α(v), μ(v), Λ_QCD(v)** — how the SM dimensionless residues depend on the crystallisation order-parameter magnitude v = |(2,2) VEV|. The falsifiable target is **R_αμ = (d ln α/dv)/(d ln μ/dv)**, the parameter-free number that is QBP's only genuine drift fingerprint (Gemini "derive or die", #539).

## A. The crystallisation potential & VEV — the algebra supplies a Mexican hat (`potential_construction.py`)

Built from the #559-verified ingredients: V(y) = a|y|² + b·Re⟨X(y e₄),(y e₄)X⟩ + c(|y|²)², where the middle term is the **non-commutative cross-coupling** (the algebra's sign-indefinite source) for a retained-sector background X.

**Two concrete findings:**
1. **The cross-coupling matrix is isotropic with sign (|X_real|² − |X_imag|²):** M(X) = (|X_re|² − |X_im|²)·I. So the **negative** mass term — the SSB trigger — appears precisely when the background is **dominantly imaginary**. In QBP's own formalism Im(ℍ)={i,j,k} are the *spatial* directions, so a **spatial/imaginary background drives the crystallisation**. (Structural fact; not over-read.)
2. **V(y) is a genuine Mexican hat** when b·|X_im|² > a (the negative cross-coupling beats the positive norm mass): mass² = a − b|X_im|² < 0, minimum at v = √((b|X_im|² − a)/2c). Concretely realised (v = 2.24, 2.50 for sample coefficients). **#559's "ingredients available" is now an explicit symmetry-breaking potential**, with the negative mass² *supplied by the octonion non-commutativity* rather than put in by hand (unlike the SM, where the negative Higgs mass² is an unexplained input).

**Open (AC-A2, the crux):** the absolute scale v depends on the coefficients (a, b, c, |X|). Whether a canonical action principle fixes them — giving a parameter-free v — is unresolved. *But Sub-problem C shows the falsifiable prediction may not need it.*

## B. v → constants — the genuine open frontier
How does each dimensionless residue depend on v? This is **QBP-specific and not the SM**: in the SM, α is *not* a function of the Higgs VEV (it's a gauge coupling). QBP must supply its own mechanism by which α (the U(1)/EM sector), μ = m_p/m_e, and Λ_QCD/m_q arise from / couple to the crystallisation (2,2). **This is the hard, unsolved part** (AC-B1/B2). No claim made here.

## C. The "scale-independent R" shortcut — ❌ BLOCKED (illusory)

The attempted shortcut: if each constant couples to the VEV as a **power law** f(v)=f₀·v^p, then R_αμ = p_α/p_μ — a ratio of exponents, independent of the absolute scale and the potential coefficients. **The adversarial gate (Gemini Furey/Feynman) BLOCKED this, correctly:**

1. **The power-law premise is broken for α.** α is a **gauge coupling** — in QFT it runs **logarithmically** (α⁻¹ ~ ln(v/Λ)), *not* as a power law. Substituting a log dependence makes R_αμ **scale-dependent** after all. Scale-independence holds only if *both* couplings are power-law; α almost certainly isn't. The "win" is dead on arrival for the gauge channel.
2. **Relocation, not progress.** The unknown functional dependence was merely bundled into "constants" p_α, p_μ. Computing them *is* the full crystallisation→constants mechanism (Sub-problem B) — all the intractable complexity, just renamed.
3. **The math is trivial** (power law ⇒ constant log-derivative); celebrating it as a structural win is a distraction from the broken premise.

**Verdict: the C-reduction is illusory.** It does NOT drop the hardest piece. (The earlier "tractability win" framing is retracted.)

## A (revisited) — demoted: SSB is *possible*, the potential is *not* parameter-free
The adversary also fairly hit Sub-problem A: choosing exactly the cross-coupling term that yields the convenient isotropic (|X_re|²−|X_im|²) mass matrix, and invoking an "imaginary background" to force the negative mass², is **model-building, not a parameter-free consequence** of the algebra. Honest demotion: §A demonstrates that the octonion non-commutativity **can** source a Mexican hat (existence — SSB is not forbidden, strengthening #559), but it is **not** "the canonical crystallisation potential." The specific term + background are inputs.

## Net (honest) — the keystone is opened and its real difficulty mapped; no shortcut exists
- **A:** SSB is *possible* (the algebra contains a negative cross-coupling) — existence only; the specific potential is model-building, scale open.
- **C:** the scale-independent-R shortcut is **BLOCKED** (α runs logarithmically; R is not generically scale-free).
- **B:** the full crystallisation→constants mechanism is the **irreducible frontier** — no shortcut bypasses it.

> **The sharpened crux (the adversary's mandate):** the real prior question is *does QBP's crystallisation give α a power-law or a logarithmic dependence on the VEV?* — i.e. does QBP **reproduce standard QFT gauge-coupling running, or replace it?** Until that is answered, neither R nor the spectrum is derivable. This is the genuine, deep next question — and it is bigger than #564 alone.

## AC status (#564)
| AC | Status |
|----|--------|
| A1 (build V, show Mexican hat) | 🟡 existence shown (SSB *possible*); demoted — specific potential is model-building, not parameter-free |
| A2 (canonical coefficients / parameter-free v) | ⏳ open (the absolute-scale crux) |
| B1/B2 (α, μ, Λ_QCD coupling to the VEV) | ⏳ **irreducible frontier** — no shortcut |
| C1 (is R scale-independent?) | ❌ **NO** — fails for log-running gauge couplings (α). Shortcut blocked |
| C2 (derive R) | ⏳ requires the full B mechanism; gated on the power-law-vs-log question |

## Provenance
Continuation of #559 (the SSB ingredients) + #539 (the drift observable), per the #563 `CONJ-vconstants-keystone`. This pass: built the explicit Mexican-hat potential (existence of algebra-sourced SSB), attempted the scale-independent-R shortcut, and the adversarial gate (Gemini Furey/Feynman) **BLOCKED the shortcut** as illusory (α runs logarithmically, not power-law). The honest residue: the keystone has no shortcut; the real prior question is power-law-vs-log running of α under crystallisation. Recorded by @qbp-oppenheimer.
