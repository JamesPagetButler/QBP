# Efimov states as a test of the substrate — research note (v0.3, 2026-09-21; v0.3 = PR #670 round-1 fixes)

**Status:** side project directed by the beekeeper (2026-09-21; tracking issue #669): "research what experiments have been done and add them to the CTH; understand what is happening; think through whether we can run a test of our substrate, and whether this is appropriate." Written by qbp-oppenheimer. **Nothing here is ruled, anchored or encoded**; §1's anchor candidates enter the ledger only through a Tier-3 PR via the confined writer. Every physics statement carries its source; every QBP-side statement carries its ledger or Lean cite or is marked open.

## 1. Experiments (verified table)

Full sweep with per-entry verification status: `efimov-experiments-2026-09-21.md` (same directory). Three tiers — **verified** (value and error read from the paper's own text or abstract), **partial** (citation solid; number corroborated only through secondary sources), **unverified** (no numeric value recovered — the fetch tools could not read several journal PDFs). Only verified entries are anchor candidates; the rest need a primary-source pass first.

| Experiment | System | Observable | Measured | Universal prediction | Tier |
|---|---|---|---|---|---|
| Kraemer et al., Nature 440, 315 (2006) — Innsbruck | Cs-133, identical bosons | three-body recombination resonance a₋; atom–dimer resonance a₊ | a₋ = −850(20) a₀; a₊ = 1060(70) a₀; ratio 1.25(9) | ratio 0.96(3) (zero-range theory) | verified |
| Gross et al., PRL 103, 163202 (2009) | Li-7 | a₊, a₋ | a₊ = 243(35) a₀; a₋ = −264(11) a₀; ratio 0.92(14) | 0.96(3) | verified |
| Pollack, Dries, Hulet, Science 326, 1683 (2009) | Li-7 | two consecutive trimer pairs across a Feshbach resonance | ratios 22.5(22)(11) and 21.1(11)(24) | 22.7 | verified |
| Huang, Sidorenkov, Grimm, Hutson, PRL 112, 190401 (2014) | Cs-133 | second (excited) triatomic resonance; scaling to the first | λ = 21.0(1.3) | 22.7 | verified (the brief mis-cited this as PRL 113, 240402 — that is Tung et al.; corrected) |
| Huckans et al., PRL 102, 165302 (2009); Williams et al., PRL 103, 130404 (2009) | Li-6, three spin components (distinguishable fermions) | trimer resonances in three-body loss | loss features near 130 G and 500 G (ground trimers), excited trimer at 895 G; a_t → −2140 a₀ | positions from three-component theory | verified (from abstracts) |
| Ulmanis et al., PRL 117, 153201 (2016) — Heidelberg | Li-6/Cs-133 heteronuclear (heavy-heavy-light) | consecutive Cs–Cs–Li Efimov resonances | scaling 4.0(3) | 4.9 (mass-ratio universal) | verified |
| Berninger et al., PRL 107, 120401 (2011) | Cs-133 across several Feshbach resonances | universality of the three-body parameter | a₋ ≈ −9.5 to −9.7 r_vdW (spread unresolved in the sweep) | universal ≈ −9.7 r_vdW (Wang et al. 2012; Chin 2011) | partial |
| Pires et al., PRL 112, 250404 (2014); Tung et al., PRL 113, 240402 (2014) | Li–Cs | first heteronuclear Efimov resonances; geometric scaling | scaling ≈ 4.9 reported | 4.9 | partial |
| Kunitski et al., Science 348, 551 (2015) | He-4 trimer, Coulomb-explosion imaging | direct observation of the excited Efimov trimer and its size | size ≈ 100 Å scale (number not re-read) | Efimov-state structure | partial |
| Ferlaino et al., PRL 102, 140401 (2009); von Stecher, D'Incao, Greene, Nat. Phys. 5, 417 (2009) | Cs; theory | tetramers tied to each trimer | binding ratios B₄⁽⁰⁾ ≈ 4.57 B₃, B₄⁽¹⁾ ≈ 1.01 B₃ (theory); the '0.43 / 0.9' ratios in the brief could NOT be located | four-body universality | partial |
| Zaccanti et al., Nat. Phys. 5, 586 (2009) K-39; Lompe et al., Science 330, 940 (2010) RF association; Nakajima et al., PRL 106, 143201 (2011); Roy et al., PRL 111, 053202 (2013); Wild et al., PRL 108, 145305 (2012) Rb-85 | various | consecutive features / RF-associated trimers / cross-resonance universality | numeric values not recovered | — | unverified |

**Negative findings of the sweep:** no confirmed *experimental* Efimov observation in nuclear physics (triton, halo nuclei — theory only, the Phillips line); none yet in the dipolar mixtures (Er–Li, Dy–Li: mixtures realised, predictions published, no resonance observed); none in photonic or synthetic-lattice analogues.

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
| a quaternionic Hilbert-space theory carrying a locally faithful, irreducible, strongly continuous unitary Poincaré representation with non-negative squared mass (3+1 from DERIV-3plus1; Lorentz symmetry itself is not a theorem on record; cold atoms are Galilean, so the application assumes the non-relativistic effective theory inherits the reduction) | **identical to standard QM** — s₀ = 1.00624, λ = 22.7, tensor-product composites. Efimov data test **fidelity**, and cannot discriminate QBP from standard QM | 2 forced, conditional on the two premises |
| a theory with quaternionic *amplitudes* combined in a shared frame (the double-slit "Model A", choice open per #387) | **undefined for three bodies** until a composite-system rule is written. The observed trimers then **force** that rule: any candidate that fails to reproduce the ladder and λ is killed | 3 open, with a sharp kill |
| octonionic anywhere in the hosted physics | operator composition ambiguous (theory doc §8.3); three-body states are exactly where (AB)ψ ≠ A(Bψ) bites | excluded at a crystal (ℍ_s associative; PROOF-associative-composition-iff) — the reason the next test exists |

**3.3 Associativity and three bodies — an open question, not a prediction (v0.3).** v0.2 claimed an "associativity null test": that `PROOF-associative-composition-iff` (`lMul_comp_eq_iff_assoc_forall`) makes QBP predict zero deviation from standard three-body QM. Both round-1 reviewers rejected it and they are right: that theorem says compositions of **left-multiplication operators** equal multiplication exactly on associative sets — a statement about the algebra, not about composing **multi-particle states** (tensor products; the Faddeev decomposition). The word "composition" was doing two jobs. And no prediction can follow from a composite-system rule that does not exist (§3.2, row 2). **Withdrawn.** What survives is a question for T-B (§4): *if* a composite rule for the hosted layer were written with an associator-dependent term of relative size ε, what δλ(ε) would follow, and what would Huang et al. 2014 then bound? The numbers that bound it: λ = 21.0 ± 1.3 against 22.69 — the 1σ width is 6.2 % of λ and the central offset 7.5 %; since s₀ = π/ln λ, δs₀/s₀ = δλ/(λ ln λ) ≈ **2.0 %** at 1σ (v0.2 wrote 7 %, an arithmetic error); the heteronuclear Li–Cs ratios add a mass-ratio-dependent check. Consistent with §3.1: nothing about the seam or the flow enters this — the ε-term, if any, would be a property of the hosted layer's composite rule.

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
| Efimov data force the composite-system rule | 3 open, sharp kill | any rule failing λ = 22.7 (6 % at 1σ today) is dead |
| "Zero three-body anomaly" as a QBP prediction | **withdrawn** (v0.3) | the associativity theorem is about operator composition, not state composition; T-B remains an open question with no prediction attached |
| Discrete scale invariance ↔ resonance records | analogy only | a derivation of s₀ from QBP would upgrade it; none exists |

## 6. Appropriateness verdict

**Appropriate, for one thing and not another.** Efimov states are an excellent test of the **hosted quantum layer**: they force it to commit to a composite-system rule (which it has not) and, once it has, they test that rule against the sharpest universal three-body number in physics. QBP makes **no** Efimov prediction today (the v0.2 "null test" is withdrawn, §3.3). They are **not** a test of the **substrate's dynamics**: nothing about the rule, the flow, the transient or the seam reaches a cold-atom trimer, and under the Moretti–Oppio premises (locally faithful, irreducible, strongly continuous unitary Poincaré representation, non-negative squared mass; inherited by the Galilean effective theory) QBP's answer is standard QM by theorem. The utility, then, is exactly what the beekeeper suspected in a different place: not "does the substrate enable them" but "does our matter layer know how to hold three things at once" — the same gap (link 4) the black-hole question ran into.

## 7. Anchor candidates (for a Tier-3 PR; not encoded here)

Only the **verified** tier qualifies today: REF-efimov-kraemer-2006 (a₋ = −850(20) a₀, ratio 1.25(9) vs 0.96(3)); REF-efimov-gross-2009 (ratio 0.92(14)); REF-efimov-pollack-2009 (22.5(22)(11), 21.1(11)(24) vs 22.7); REF-efimov-huang-2014 (λ = 21.0(1.3) vs 22.7 — the number any composite rule must reproduce); REF-efimov-li6-three-component-2009; REF-efimov-ulmanis-2016 (4.0(3) vs 4.9). Each: provenance E, `provenance_kind: experiment`, `measured_value`/`measured_error`/`predicted_value`/`predicted_unit` (the universal number stays in `predicted_value` per the cth convention answer on #670), `measured_source` with DOI. Plus REF-moretti-oppio-2019 (theory-external; the reduction theorem) and FLAG-hosted-composite-rule-open (the hosted layer has no composite-system rule; points at theory doc §8.2–8.4 and this note; kill = a rule that reproduces the verified table). The partial and unverified rows enter only after a primary-source pass with PDF-capable tooling.
