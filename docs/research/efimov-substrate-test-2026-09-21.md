# Efimov states as a test of the substrate — research note (v0.1, 2026-09-21)

**Status:** side project directed by the beekeeper (2026-09-21; tracking issue #669): "research what experiments have been done and add them to the CTH; understand what is happening; think through whether we can run a test of our substrate, and whether this is appropriate." Written by qbp-oppenheimer. **Nothing here is ruled, anchored or encoded**; §1's anchor candidates enter the ledger only through a Tier-3 PR via the confined writer. Every physics statement carries its source; every QBP-side statement carries its ledger or Lean cite or is marked open.

## 1. Experiments (verified table)

*Filled from the literature sweep — see `efimov-experiments-2026-09-21.md` alongside; only entries whose values were read from the paper or abstract are carried. Anchor candidates are listed in §7.*

## 2. What the Efimov effect is (Efimov 1970; Braaten & Hammer 2006; Naidon & Endo 2017)

| Ingredient | Statement | Source |
|---|---|---|
| Setting | three particles in **3D** with a **short-range** two-body interaction tuned to **resonance** in the **s-wave** (scattering length a → ∞, two-body bound state at threshold) | Efimov 1970; Braaten–Hammer §1 |
| Effect | an infinite ladder of three-body bound states (trimers) even when no two-body bound state exists (Borromean); binding energies E_n = E_0 λ^{−2n}, resonance positions a_n = a_0 λ^n | Braaten–Hammer §3 |
| Mechanism | in hyperspherical coordinates the three-body problem at unitarity reduces to a hyperradial Schrödinger equation with an attractive **−(s₀² + ¼)/R²** potential; the 1/R² potential is scale-invariant and its continuous scale symmetry is broken to a **discrete** one (log-periodic solutions) | Braaten–Hammer §3; Naidon–Endo §2 |
| s₀ | for three identical bosons, s₀ is the positive root of s cosh(πs/2) = (8/√3) sinh(πs/6), **s₀ = 1.00624**, hence **λ = e^{π/s₀} = 22.694** | Braaten–Hammer eq. (standard); Wikipedia quotes 1.0062378 and 22.69438 |
| Renormalisation | the 1/R² attraction is too singular (Thomas collapse); a **three-body parameter** fixes the ladder's absolute position; the system is a **renormalisation-group limit cycle** | Braaten–Hammer §3–4 |
| Universality of the parameter | for van der Waals atoms the three-body parameter is universal: a₋ ≈ −9.7 r_vdW across species and resonances | Berninger et al. 2011; Wang, D'Incao, Esry, Greene 2012; Naidon–Endo abstract ("scales with the range of atomic interactions") |
| Statistics / mass ratio | two identical fermions + one particle: no effect below mass ratio ≈ 13.6 (Petrov 2003; Braaten–Hammer §6); heavy-heavy-light bosonic mixtures have a **smaller** scaling factor (Cs–Cs–Li: λ ≈ 4.9) | Braaten–Hammer; Pires 2014; Tung 2014 |
| Dimension | absent for zero-range interactions in 2D and 1D — the effect is a 3D phenomenon | Naidon–Endo (standard) |
| Beyond atoms | proposed origin: the triton and the Hoyle state of ¹²C; halo nuclei; helium trimer imaged directly (Kunitski 2015) | Naidon–Endo abstract |

What the effect **does not** depend on: the detailed two-body potential (only a and the range), the species, or the coupling strength — hence "universality". What it **does** depend on: 3D kinematics, quantum statistics, mass ratios, and the composition rule for three-body states (the Faddeev decomposition, which assumes the standard tensor-product Hilbert space of composite systems).

## 3. Where QBP could touch this — and where it cannot

**3.1 The substrate does not reach it.** The substrate (state sphere, potential, the rule) describes how a universe crystallises; a crystal hosts an associative algebra ℍ_s and the physics of matter lives *inside* it (POST-hosting; PROOF-substrate-hosting-definition). Efimov trimers are cold-atom three-body states inside a universe. No observable of the flow (b₀², the relaxation rate, the seam) enters a trimer's spectrum. **So Efimov physics cannot test the rule, the flow, or the seam.** "Can the substrate enable these states?" reduces to "does the hosted layer reproduce 3D quantum mechanics with a composite-system rule?" — which is link 4 of the matter question (#635 records).

**3.2 The hosted quantum layer: the Moretti–Oppio reduction.** Moretti & Oppio (Rev. Math. Phys. 2019; arXiv:1709.09246) prove: for a quaternionic Hilbert-space quantum theory carrying a locally faithful irreducible strongly continuous unitary representation of the Poincaré group with non-negative squared mass, there is a unique (up to sign) Poincaré-invariant complex structure commuting with the observables, and the theory is **physically equivalent to a complex Hilbert-space theory** in which "all self-adjoint operators are observables, Noether's theorem holds and composite systems may be given in terms of tensor product". QBP's own theory doc (`docs/theory/quaternionic_si_definitions.md` §8.2) already records quaternionic tensor products as non-trivial with this citation, and states the double-slit work covers **single-particle** interference only.

Consequence, sorted:

| If the hosted layer is … | then Efimov physics in QBP is … | Bucket |
|---|---|---|
| a quaternionic Hilbert-space theory with Poincaré symmetry (3+1 from DERIV-3plus1; Lorentz symmetry itself is not a theorem on record) | **identical to standard QM** — s₀ = 1.00624, λ = 22.7, tensor-product composites. Efimov data test **fidelity**, and cannot discriminate QBP from standard QM | 2 forced, conditional on the two premises |
| a theory with quaternionic *amplitudes* combined in a shared frame (the double-slit "Model A", choice open per #387) | **undefined for three bodies** until a composite-system rule is written. The observed trimers then **force** that rule: any candidate that fails to reproduce the ladder and λ is killed | 3 open, with a sharp kill |
| octonionic anywhere in the hosted physics | operator composition ambiguous (theory doc §8.3); three-body states are exactly where (AB)ψ ≠ A(Bψ) bites | excluded at a crystal (ℍ_s associative; PROOF-associative-composition-iff) — the reason the next test exists |

**3.3 The associativity null test (the QBP-native use).** `PROOF-associative-composition-iff` (`lMul_comp_eq_iff_assoc_forall`): compositions of left-multiplications equal multiplication exactly on associative sets. Three-body composition is the associator's home. At a crystal the hosted algebra is associative, so QBP predicts **zero deviation** from standard three-body QM. That is a prediction with a falsifier: any residual non-associativity in the hosted layer (an in-flight admixture; a seam effect) would show first in three-body observables, and the Efimov scaling factor is the cleanest three-body observable in physics. Measured: Huang et al. 2014 give λ = 21.0 ± 1.3 against 22.69 (a 7 % bound at 1σ on any correction to s₀; s₀ enters as π/ln λ so δs₀/s₀ ≈ 7 % too); the heteronuclear Li–Cs consecutive-resonance ratios add a second, mass-ratio-dependent check. **Turning this into a quantitative bound needs a model of how an associator term enters the three-body kernel** — open (§5). Without that model the null test is qualitative: "no three-body anomaly has been seen where one would first appear."

**3.4 The resonance-space analogy.** Efimov physics is discrete scale invariance: a log-periodic spectrum with period π/s₀ = 3.12 in ln a, a renormalisation-group limit cycle. The ledger's INSIGHT-echo-harmony-z2 (a log-periodic self-similar tower, period ln 3 = 1.10; a ℤ₂ grading selecting odd harmonics) and INSIGHT-resonance-vs-amplification-scale-invariance describe the same *kind* of structure by construction. The Efimov ladder has **no** parity grading and its period is fixed by s₀, not by a Cantor construction; so the connection is a shared mathematical form (limit cycle), not a shared mechanism. Recorded as analogy; a claim would need a derivation of s₀ from anything in QBP, which nothing suggests.

## 4. Tests that can be run

| Test | What it would show | Cost | Status |
|---|---|---|---|
| **T-A fidelity**: solve the Skorniakov–Ter-Martirosian / Faddeev equation numerically at unitarity in the hosted layer's composite-system rule and recover s₀ = 1.00624 | that the hosted QM hosts Efimov physics at all | trivial in complex QM; **blocked** in QBP until the composite-system rule is written (the finding) | open — the block *is* the result |
| **T-B associativity bound**: model a non-associative perturbation of the three-body kernel by an associator of relative size ε; compute δλ(ε); bound ε from λ = 21.0 ± 1.3 and the Li–Cs ratios | a quantitative upper bound on hosted non-associativity | M (a model choice — which is itself a theory decision, so it enters as an OPEN root with a kill, not a ruling) | open |
| **T-C anchors**: the experiments as REF-/MEAS- records with values and citations | the data on the ledger, so any future hosted-QM model is tested against them by the gate | S | §7 |
| Lean | the 1/R² scale invariance and the discrete-symmetry breaking are classical mathematics; nothing QBP-specific is reachable | — | not proposed |

## 5. Buckets

| Claim | Bucket | Test / kill |
|---|---|---|
| Efimov physics cannot test the substrate's dynamics (rule, flow, seam) | 2 forced | no flow observable enters a trimer spectrum (POST-hosting / hosting definition: matter lives in the crystal) |
| Under quaternionic-Hilbert + Poincaré premises, QBP's Efimov physics = standard | 2 forced (Moretti–Oppio), conditional | kill: a demonstration that the hosted layer is NOT a Hilbert-space theory or lacks Poincaré symmetry |
| The hosted layer has no composite-system rule on record | 1 (documentary) | theory doc §8.2/8.4; double-slit Model A single-particle |
| Efimov data force the composite-system rule | 3 open, sharp kill | any rule failing λ = 22.7 (7 % today) is dead |
| Zero three-body anomaly = associativity null test | 3 open | needs the ε-model (T-B) to be quantitative |
| Discrete scale invariance ↔ resonance records | analogy only | a derivation of s₀ from QBP would upgrade it; none exists |

## 6. Appropriateness verdict

**Appropriate, for one thing and not another.** Efimov states are an excellent test of the **hosted quantum layer**: they force it to commit to a composite-system rule (which it has not) and, once it has, they test that rule against the sharpest universal three-body number in physics, with the associativity theorem supplying QBP's only genuine prediction (null). They are **not** a test of the **substrate's dynamics**: nothing about the rule, the flow, the transient or the seam reaches a cold-atom trimer, and under the Moretti–Oppio premises QBP's answer is standard QM by theorem. The utility, then, is exactly what the beekeeper suspected in a different place: not "does the substrate enable them" but "does our matter layer know how to hold three things at once" — the same gap (link 4) the black-hole question ran into.

## 7. Anchor candidates (for a Tier-3 PR; not encoded here)

*Filled from §1 once the sweep's verified table is in: one REF- per landmark experiment (Kraemer 2006; Zaccanti 2009; Pollack 2009; Berninger 2011; Huang 2014; Pires/Tung 2014; Kunitski 2015; Ferlaino 2009 tetramers) with `measured_value`, `predicted_value` (the universal number), `measured_source`, provenance E, `provenance_kind: experiment`; one REF- for Moretti–Oppio 2019 (theory-external); one FLAG- "hosted composite-system rule undefined" pointing at theory doc §8.2–8.4 and this note.*
