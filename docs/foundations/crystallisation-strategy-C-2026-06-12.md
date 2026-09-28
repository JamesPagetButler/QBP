# Crystallisation Strategy C — first cycle (2026-06-12)

> ## ⚠️ PROVISIONAL CHECKPOINT — updated 2026-09-28 after #473's first pass (substrate first draft v0.1, PR #685)
> **Status of the gate:** #473 has a first-pass document on master. On the one question this checkpoint asked of it — which spatial or geometric primitive the substrate yields for C's `∫d³x` — the first-pass answer is **negative** (§5). The checkpoint is therefore a record of the fork, not a green light for a fundamental C. Whether it merges as a record or waits for a positive in-flight account is the beekeeper's call.
> This document records Strategy C's **first** generate→attack→synthesize cycle. The
> counter-team surfaced that the model **smuggles spacetime** (the `∫d³x` it integrates
> over is the very geometry crystallisation should *produce*) → a *fundamental* C needs
> the **condensed/locale substrate (#473)** as the spacetime origin. We are deliberately
> **tick-tocking**: this is captured as a checkpoint, and it **must be revisited and
> updated once #473 has a first-pass resolution.** The merge is gated on that. The
> physics below is the right *shape*, but three couplings are undelivered and the
> geometric foundation is owed by #473.

**For:** #539 · **Status:** CHECKPOINT, blocked-on-#473 · **Inputs:** B (#548), the ln-7 ruling (#539)

---

## 1. The proposal (Gemini, Furey/Feynman) — a strong first draft
A φ⁴ Landau–Ginzburg model of the **G₂ → SO(4) spontaneous symmetry breaking** (𝕆-vacuum → ℍ-vacuum):
- **Order parameter** φ = gauge-invariant magnitude of an adjoint-**14** G₂ field (φ=0 fully non-associative, φ=φ₀ crystallised ℍ).
- **Potential** V(φ) = (λ/4)(φ²−φ₀²)² — 𝕆-symmetric state unstable, ℍ-broken minima.
- **EOM** (Model A relaxational, in Γ) → logistic φ(Γ). **Emergent time:** `dt = (φ/φ₀)² dΓ` (at φ=0, time doesn't exist).
- **α-drift** via coset-DOF vacuum polarization; we sit in the asymptotic tail → drift exponentially suppressed (≈ matches ~zero observed).
- **Goldstones:** postulates G₂ *local gauge* → 8 coset Goldstones become massive non-associative vectors; α-drift = their masses asymptoting.
- **Cross-channel:** V(φ) descent **is** dark energy → **α̇/α ∝ (w+1)** ("expansion = exhaust heat of crystallisation").
- **Falsification:** isotropic monotonic α(z); **dies if the Webb α-dipole is confirmed** (a global Γ-relaxation can't make a spatial dipole).

## 2. Counter-team (Wilson / Jaynes)
**Wilson — smuggled structure:**
- **W1 (deepest):** `∫d³x[(∇φ)²+V]` **smuggles spacetime** — presupposes the geometry crystallisation should produce. → C is **EFT *on* spacetime, not a derivation *from* the algebra.**
- **W2:** the α–φ coupling ε is **asserted, not derived** (the f(0) risk — a knob dressed as a prediction).
- **W3:** "G₂ local gauge so Goldstones are eaten" is a **rescue invoking an unobserved exceptional gauge sector.**

**Jaynes — honest accounting:**
- **J1:** `dt = (φ/φ₀)²` — the exponent **2 is postulated to make "near-frozen" work** (prior chosen to get the posterior).
- **J2:** **α̇/α ∝ (w+1)'s teeth are in the proportionality CONSTANT — undelivered.** "Both depend on φ → correlate" is weak; "by *this* number" is strong.
- **J3:** currently **unfalsifiable-in-practice** (sub-detection drift); the one sharp kill rides a *contested* measurement.

## 3. Synthesis (Oppenheimer) — APPROVE as the starting framework; 3 derivations owed + 1 structural fork
- **Keep the φ⁴ SSB skeleton** — right shape, correctly puts the physics in the gauge-invariant breaking (honours B + the ln-7 ruling).
- **Three free parameters must be DERIVED from B's G₂/SO(4) geometry** (or each is an honest fork the theory doesn't fix): **(i)** ε (the α-coupling), **(ii)** the `dt` exponent, **(iii)** the α̇/α∝(w+1) constant. Undelivered → f(0)-with-knobs.
- **The structural fork (the headline):** C, attacked, **reveals the substrate dependency.** The `∫d³x` spacetime C needs is exactly what **#473** is meant to provide. *A fundamental C needs #473; an effective C can proceed treating spacetime as given.* **Decision (beekeeper 2026-06-12): route through #473 first — finalize C after #473's first pass.**
- **Sharpest near-term empirical target (Strategy A):** **α̇/α ∝ (w+1)** — sign + existence testable now (DESI `w` × clocks/high-z `α̇`); the ESPRESSO isotropy kill is a real near-term falsification.

## 4. What this checkpoint owes (the update after #473) — status 2026-09-28
- [ ] Re-derive C on the substrate's spacetime origin (remove the `∫d³x` circularity) once #473 has a first-pass. — **BLOCKED in a new way (§5.1):** v0.1 yields no spatial primitive; this item now waits on a positive account of the in-flight region, which has no owning issue yet.
- [ ] Derive (or fork-flag) ε, the `dt` exponent, the α̇/α∝(w+1) constant from the coset geometry. — unchanged; owned by #539 AC-C1/AC-C2.
- [x] Pin the SO(4) stabilizer / coset dimension (#551) feeding the derivations. — **on record (§5.2):** stabiliser SO(4) = (SU(2)×SU(2))/ℤ₂, coset G₂/SO(4) of dimension 14 − 6 = 8 (ledger `INSIGHT-octonion-quaternion-branching`; the 8-dimensional moduli T(G₂/SO(4)) of ℍ ↪ 𝕆 also recorded in `PROOF-level-set-invariants-rule-blind`'s description). A ledger record, not a Lean theorem; #551's own AC to cite Baez/Harvey/Conway–Smith stays open.
- [ ] Resolve the Goldstone fate (W3) without inventing an unobserved gauge sector. — unchanged; §5.3 adds what v0.1 says about the 8 coset directions.

## 5. Update after #473's first pass (2026-09-28)

Source: `docs/foundations/substrate-first-draft-v0.1.md` (PR #685, master a014688; ledger 6.10.0 → 6.11.0 after PR #687). Every claim below carries the draft's own tag.

### 5.1 The spatial primitive — the first-pass answer is negative

| What C's `∫d³x` needs | What v0.1 supplies | Tag |
|---|---|---|
| a space with points to integrate over | per universe, one crystal algebra ℍ_s ⊂ 𝕊 and one number b₀² (the ℓ-coefficient); no space | PROVED (hosting definition), OPEN (any geometry) |
| a metric on that space | the only metric on record is N on the 16-dimensional carrier, not on any emergent 3-space | record statement |
| the in-flight region as a space with configurations (hosting clause (c)'s "pointless" half) | **no positive account on record; no issue owns one** (v0.1 §4, §8) — only negatives: V's first-order data constrains at most one of 14 tangent directions; level-set invariants are rule-blind | PROVED (negatives), OPEN (positive account) |

**Consequence for the fork of §3.** The substrate as drafted does not supply the primitive; the `∫d³x` circularity (W1) is not removed, it is relocated. The fork is therefore sharpened, not resolved:
- **Effective C:** proceed on a hosted spacetime whose origin is *not* the substrate — an EFT on space taken as given, with §3's three derivations still owed. Honest, and testable through Strategy A.
- **Fundamental C:** waits on a positive definition of the in-flight region. v0.1 §8 names it as the first thing a v0.2 needs and says it has no issue.

Nothing in v0.1 rules either branch out. What it rules out is the reading of the 2026-06-12 checkpoint on which "route through #473" would *deliver* the spacetime origin: at first pass it does not.

### 5.2 The coset — delivered as a record
G₂ → SO(4) with SO(4) = (SU(2)_a × SU(2)_b)/ℤ₂ the stabiliser of ℍ, and the 7 imaginary octonions branching 7 = (3,1) ⊕ (2,2) (`INSIGHT-octonion-quaternion-branching`). Coset dimension dim G₂ − dim SO(4) = 14 − 6 = **8**; the same 8 appear as the moduli T(G₂/SO(4)) of the embedding ℍ ↪ 𝕆 in v0.1 §4. This pins §1's "adjoint-14 … 8 coset Goldstones" arithmetic and answers #551's first AC as a citation of the ledger; #551's literature citation and its discrete-vs-continuous question remain open. A caution from the same ledger: `INSIGHT-octonion-higgs-killed` records that the (2,2) carries spatial-rotation charge under γ(a,b), so any reading of the coset as an internal Higgs sector was already killed (#559).

### 5.3 The Goldstone fate (W3) — one input, not a resolution
v0.1's transition-state theorems say the 8 coset directions are *kinematic* moduli of where ℍ sits in 𝕆 (`PROOF-level-set-invariants-rule-blind`, NOT-claimed clause: "nonzero and kinematic"), and that the potential V is blind to 13 of 14 tangent directions off the ridge. So the substrate supplies no potential that would lift the coset — neither a mass term nor a gauge sector. W3 stands: the Goldstone fate is not decided by the substrate, and §1's "G₂ local gauge" remains an import the theory does not supply.

### 5.4 The kill test, restated in positive-measure form
The 2026-09-25 lesson (v0.6 addendum §2; AXIOM-1's rewritten kill, PR #687): a kill posed as a single reachability hit can fire on a null set and discriminate nothing. §1's kill — "dies if the Webb α-dipole is confirmed" — should be carried as: *C's global-Γ relaxation predicts an isotropic, monotonic α(z); it is killed if a spatial α-dipole is established at a stated significance by an independent instrument (ESPRESSO-class), because no global relaxation produces one.* The contested status of the Webb measurement (J3) is unchanged; the restatement fixes the form, not the evidence.

### 5.5 What this update does NOT do
No derivation of ε, the `dt` exponent or the α̇/α∝(w+1) constant (§3 (i)–(iii) still owed to #539); no choice between the effective and fundamental branches (a physics question, decided by evidence, not by ruling — cf. #635 and the horn audit on #473); no change to any ledger record; no claim that AC1–AC3 of #473 are met.

## 6. Provenance
Strategy-C first cycle: Gemini (generate) + counter-team Wilson/Jaynes (attack) + @qbp-oppenheimer (synthesis), 2026-06-12. Tick-tock checkpoint per beekeeper direction; revisit after #473. **Revisited 2026-09-28** (qbp-oppenheimer) against the substrate first draft v0.1 (PR #685) and the AXIOM-1 kill rewrite (PR #687), at the beekeeper's direction ("draft the update on #553").
