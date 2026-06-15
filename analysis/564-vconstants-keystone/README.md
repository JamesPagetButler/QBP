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

## C. R_αμ reduces to a RATIO OF EXPONENTS (scale-independent) — the tractability win
R_αμ is a ratio of logarithmic derivatives. If each constant couples to the VEV as a **power law** f(v) = f₀·v^p, then d ln f/d ln v = p (constant — independent of v and of all potential coefficients), so

$$R_{\alpha\mu} = \frac{d\ln\alpha/d\ln v}{d\ln\mu/d\ln v} = \frac{p_\alpha}{p_\mu}\quad(\text{a pure ratio of exponents, scale-free}).$$

**Consequence:** the falsifiable number is **independent of the absolute VEV scale AND of the (undetermined) potential coefficients** — it reduces to the **coupling exponents** (p_α, p_μ, p_QCD). So "derive R" no longer requires solving the hard absolute-scale problem (A's crux); it requires only Sub-problem B's *exponents*. This drops the hardest piece — *provided* the couplings are power laws (flagged assumption — logarithmic/running couplings would make R scale-dependent).

## Net (honest)
- **A:** the algebra gives a concrete SSB Mexican hat (negative mass² from non-commutativity, triggered by an imaginary background). ✅ mechanism shown; absolute scale open.
- **C:** R_αμ = p_α/p_μ, scale- and coefficient-independent under power-law coupling. ✅ the falsifiable number is reduced to exponents.
- **B:** deriving the exponents p_α, p_μ, p_QCD (QBP's mechanism for how the constants couple to the (2,2)) is the **genuine remaining frontier** — untouched, hard, QBP-specific.

> **The keystone is now sharply localised:** not "solve the dynamics + the scale + the map" but **"derive the three coupling exponents."** That is the single thing standing between QBP and a parameter-free, falsifiable drift-ratio testable on the Th-229 clock network (#539).

## AC status (#564)
| AC | Status |
|----|--------|
| A1 (build V, show Mexican hat) | ✅ done — explicit, algebra-sourced negative mass² |
| A2 (canonical coefficients / parameter-free v) | ⏳ open (the absolute-scale crux) |
| B1/B2 (α, μ, Λ_QCD coupling to the VEV) | ⏳ **open frontier** — the real remaining work |
| C1 (is R scale-independent?) | ✅ **yes, under power-law coupling** — R = ratio of exponents |
| C2 (derive R) | ⏳ reduces to B (the exponents) |

## Provenance
Continuation of #559 (the SSB ingredients) + #539 (the drift observable), per the #563 `CONJ-vconstants-keystone`. The imaginary-background SSB trigger and the R=ratio-of-exponents reduction are this pass's results. Recorded by @qbp-oppenheimer; the C-reduction adversarially tested before adoption (see PR thread).
