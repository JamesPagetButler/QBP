# M1 test: Hessian zero modes of φ² at associative frames vs generic ψ (MDCU R4 FORM mechanism)

**Status:** research note, napkin grade, pre-registered. No physics adopted; no CTH anchor minted.
**Seat:** qbp-oppenheimer (theory axis). **Tracks:** QBP#776 (rung 2, E6 design input).
**Script:** `analysis/mdcu_m1_hessian.py` (numpy only, deterministic seeds, prints every table below; run as `run-bounded 2G 120 python3 analysis/mdcu_m1_hessian.py`, ~12 s).

## 0. Pre-registered expectation (written by oppenheimer before any computation; verbatim)

> Let φ be the standard G₂ 3-form on Im 𝕆 ≅ ℝ⁷ (use the repo's existing octonion convention — find the Fano/structure-constant convention in `docs/conventions/cd-doubling.md`, `docs/conventions/fano-orientation.md` and any existing Python octonion multiplication in `src/` or `analysis/`; do not invent a new table; cite the file you used). Define f(u,v,w) = φ(u,v,w)² on the Stiefel manifold V₃(ℝ⁷) of orthonormal triples (dimension 3·7 − 6 = 15). The maximisers (f = 1) are orthonormal frames of associative 3-planes: the associative Grassmannian G₂/SO(4) (dim 8) times the frame rotations SO(3) (dim 3). **Expectation A:** at an associative frame (e.g. a Fano line's basis triple) the Riemannian Hessian of f restricted to the tangent space of V₃ has **11 zero eigenvalues and 4 strictly negative ones** (tolerance: |λ| < 1e-6 counts as zero). **Expectation B:** for a generic stable definite 3-form ψ = g·φ with g = exp(sS), S symmetric traceless Gaussian, s = 0.1 (as in the MDCU S2 sampler), at ψ's Euclidean-unit maximiser (found by multistart ascent on V₃) the Hessian of ψ² has **3 zero eigenvalues (frame SO(3) only) and 12 strictly negative ones**: the maximiser is isolated up to frame. **Expectation C (control):** for the random (non-stable or arbitrary) 3-form the same isolation holds; for the split-G₂ form (signature (3,4) under Hitchin's B_ψ) report whatever comes out without expectation.

## 1. Context — what M1 is

MDCU round 4 (qbp-compute-unit `doc/spikes/mdcu-round4-results.md`, record PR qbp-compute-unit#88 @ `2c14c30`) read **Q4b = FORM**: at matched comass, the deformed form ψ locks the ring where φ does not (K-phi@κ 0.0% vs K-psi@1 100.0%); the COUPLING-ONLY kill fired, FORM did not. The frozen planning table (inter#194 [issuecomment-6431920143](https://github.com/JamesPagetButler/inter/issues/194#issuecomment-6431920143), row "COUPLING-ONLY killed") names the candidate mechanism — **flat landscape for φ vs funnelled landscape for ψ** — as a napkin design input to QBP#776 rung 2 (E6), to be stated by oppenheimer, not as an anchor. Call that mechanism **M1**.

M1 rests on a static-landscape claim: *the maximiser set of φ² on orthonormal triples is a continuum (11-dimensional), while a generic ψ's Euclidean maximiser is isolated up to the exact frame symmetry.* If that claim were false — e.g. if the associative set were not the full critical set, or if generic ψ kept extra flat directions — M1 would be dead before any ring dynamics is considered. This note tests exactly that claim and nothing else.

## 2. Method

**Octonion convention (not invented here).** φ_abc := (e_a e_b)_c, a,b,c ∈ 1..7, with the product from the repo's numerical Cayley–Dickson code `analysis/473-dirac-probe/cdalg.py::cd_mul` — the ratified F3 formula `(a,b)(c,d) = (ac − d̄b, da + b c̄)` of `docs/conventions/cd-doubling.md`. The script **asserts** that the result is totally antisymmetric, has exactly 42 non-zero entries, and equals +1 on each of the seven oriented triples of `docs/conventions/fano-orientation.md` (F4): e₁e₂=e₃, e₁e₄=e₅, e₁e₇=e₆, e₂e₄=e₆, e₂e₅=e₇, e₃e₄=e₇, e₃e₆=e₅. Hitchin's B_φ (B_ψ(u,v) e^{1…7} = ι_uψ ∧ ι_vψ ∧ ψ) is computed and is **definite (0,7)** — φ is of G₂ type.

**Manifold and tangent space.** V₃(ℝ⁷) = {F ∈ ℝ^{7×3} : FᵀF = I}, dim 15. T_F V₃ = {X : FᵀX + XᵀF = 0} = {FA + F⊥B : A ∈ so(3), B ∈ ℝ^{4×3}}; the script builds the orthonormal (Frobenius) basis {F(E_ij − E_ji)/√2}_{i<j} ∪ {F⊥ e_k e_lᵀ} (3 + 12 = 15) and asserts orthonormality and tangency.

**Hessian, two independent ways.**
1. *Analytic.* With f̄(F) = ψ(u,v,w)² the ambient function and T = ψ(u,v,w), D²f̄[X,Y] = 2·DT[X]·DT[Y] + 2T·D²T[X,Y] written out from trilinearity (DT[X] = ψ(x₁,v,w)+ψ(u,x₂,w)+ψ(u,v,x₃); D²T[X,Y] = the six mixed terms). The embedded-Stiefel Riemannian Hessian is Hess f[X,Y] = D²f̄[X,Y] − tr(XᵀY·S), S = sym(Fᵀ∇f̄(F)) (Absil–Mahony–Sepulchre 2008 §5.3; Edelman–Arias–Smith 1998).
2. *Finite differences* along the QR retraction qf(F + tX) (sign-fixed so diag R > 0). FD2: central second differences, h = 1e-4 (the pre-registered step). FD4: 5-point fourth-order stencil for Q(X) = d²/dt² f(qf(F+tX))|₀ with h = 1e-2, polarised H_ab = ½(Q(X_a+X_b) − Q(X_a) − Q(X_b)). At a critical point the Hessian of f∘R is the same for every first-order retraction (Absil et al. Prop. 5.5.5), so FD and analytic must agree there; |grad_R f| is reported at every point (≤ 2e-14).

**Points tested.** A: five associative frames F = g·F_Fano·R with F_Fano the basis triple of a Fano line, R ∈ SO(3) random, g ∈ G₂ random (g = exp(Σ cᵢ Dᵢ) over a 14-dimensional basis of Der(𝕆)|_{Im 𝕆} built from `cdalg.D`; the script asserts dim 14, g ∈ SO(7) and g·φ = φ to 1e-9), plus the bare (123) frame. B: five seeds of the MDCU S2 sampler (qbp-compute-unit `emulator/mdcu/r3forms.go::SampleS2`: ψ = g·φ := φ(g·,g·,g·), g = exp(sS), S = sym(Gaussian 7×7) made traceless, s = 0.1, Frobenius-matched to |φ|), each maximised by 20-start projected gradient ascent with Armijo backtracking + Newton polish on the tangent space. C: three random Gaussian 3-forms (antisymmetrised, Frobenius-matched), same search. Split-G₂: φ̃_abc = η_c (e_a ⋆ e_b)_c with ⋆ the split doubling `(a,b)(c,d) = (ac + d̄b, da + b c̄)` of ℍ and η = diag(1,1,1,−1,−1,−1,−1); checked totally antisymmetric and B of signature (4,3).

**Classification.** Eigenvalues of the symmetrised 15×15 matrix; |λ| < 1e-6 → zero (pre-registered tolerance). Counts are reported as #zero/#negative/#positive.

## 3. Results (verbatim script output)

### Expectation A — phi at associative frames (expect 11 zero / 4 negative / 0 positive)
| form / point | f = psi^2 | \|grad_R f\| | analytic #0/#neg/#pos | FD2 h=1e-4 #0/#neg/#pos | FD4 h=1e-2 #0/#neg/#pos | min \|nonzero\| (an.) | max \|zero-class\| (an.) | max \|H_fd2 - H_an\| | max \|H_fd4 - H_an\| | notes |
|---|---|---|---|---|---|---|---|---|---|---|
| phi, assoc. frame #1 (g.Fano(123).R) | 1.000000 | 5.1e-15 | 11/4/0 | 11/4/0 | 11/4/0 | 6.000e+00 | 3.2e-15 | 5.3e-07 | 3.9e-07 | T=+1.000000 |
| phi, assoc. frame #2 (g.Fano(145).R) | 1.000000 | 6.5e-15 | 11/4/0 | 11/4/0 | 11/4/0 | 6.000e+00 | 4.5e-15 | 2.7e-07 | 3.9e-07 | T=+1.000000 |
| phi, assoc. frame #3 (g.Fano(176).R) | 1.000000 | 6.3e-15 | 11/4/0 | 11/4/0 | 11/4/0 | 6.000e+00 | 3.3e-15 | 4.9e-07 | 3.7e-07 | T=+1.000000 |
| phi, assoc. frame #4 (g.Fano(246).R) | 1.000000 | 6.0e-15 | 11/4/0 | 11/4/0 | 11/4/0 | 6.000e+00 | 3.9e-15 | 4.8e-07 | 3.5e-07 | T=+1.000000 |
| phi, assoc. frame #5 (g.Fano(257).R) | 1.000000 | 9.0e-15 | 11/4/0 | 11/4/0 | 11/4/0 | 6.000e+00 | 4.4e-15 | 2.8e-07 | 3.8e-07 | T=+1.000000 |
| phi, bare Fano(123) frame | 1.000000 | 0.0e+00 | 11/4/0 | 11/4/0 | 11/4/0 | 6.000e+00 | 1.2e-15 | 8.9e-08 | 4.0e-07 | T=+1.000000 |

### Expectation B — generic definite psi = g.phi at its Euclidean maximiser (expect 3 / 12 / 0)
| form / point | f = psi^2 | \|grad_R f\| | analytic #0/#neg/#pos | FD2 h=1e-4 #0/#neg/#pos | FD4 h=1e-2 #0/#neg/#pos | min \|nonzero\| (an.) | max \|zero-class\| (an.) | max \|H_fd2 - H_an\| | max \|H_fd4 - H_an\| | notes |
|---|---|---|---|---|---|---|---|---|---|---|
| psi_S2 seed 1000, Euclid.-max. | 1.883325 | 1.6e-14 | 3/12/0 | 3/12/0 | 3/12/0 | 2.412e-01 | 4.3e-15 | 7.0e-07 | 5.5e-07 | B_psi definite (0,7); cond(gg^T)=3.37; d=0.245; 20/20 starts at max |
| psi_S2 seed 1001, Euclid.-max. | 1.706368 | 2.1e-14 | 3/12/0 | 0/15/0 | 3/12/0 | 2.128e-01 | 3.6e-15 | 1.6e-06 | 5.1e-07 | B_psi definite (0,7); cond(gg^T)=2.29; d=0.193; 20/20 starts at max |
| psi_S2 seed 1002, Euclid.-max. | 2.612892 | 2.7e-15 | 3/12/0 | 2/13/0 | 3/12/0 | 1.232e+00 | 4.3e-15 | 1.2e-06 | 6.3e-07 | B_psi definite (0,7); cond(gg^T)=3.99; d=0.334; 20/20 starts at max |
| psi_S2 seed 1003, Euclid.-max. | 2.045217 | 3.7e-15 | 3/12/0 | 2/13/0 | 3/12/0 | 7.300e-01 | 4.4e-15 | 1.1e-06 | 5.3e-07 | B_psi definite (0,7); cond(gg^T)=2.91; d=0.255; 20/20 starts at max |
| psi_S2 seed 1004, Euclid.-max. | 2.071429 | 3.3e-15 | 3/12/0 | 2/13/0 | 3/12/0 | 8.528e-01 | 6.7e-15 | 1.8e-06 | 5.4e-07 | B_psi definite (0,7); cond(gg^T)=3.24; d=0.247; 20/20 starts at max |

### Expectation C — random 3-form controls (expect 3 / 12 / 0)
| form / point | f = psi^2 | \|grad_R f\| | analytic #0/#neg/#pos | FD2 h=1e-4 #0/#neg/#pos | FD4 h=1e-2 #0/#neg/#pos | min \|nonzero\| (an.) | max \|zero-class\| (an.) | max \|H_fd2 - H_an\| | max \|H_fd4 - H_an\| | notes |
|---|---|---|---|---|---|---|---|---|---|---|
| random 3-form seed 2000, Euclid.-max. | 3.422473 | 8.6e-15 | 3/12/0 | 3/12/0 | 3/12/0 | 8.092e-01 | 4.3e-15 | 7.1e-07 | 8.2e-07 | B_psi split (3,4); 20/20 starts at max |
| random 3-form seed 2001, Euclid.-max. | 3.760262 | 4.9e-15 | 3/12/0 | 1/14/0 | 3/12/0 | 2.334e+00 | 4.7e-15 | 2.2e-06 | 9.0e-07 | B_psi split (3,4); 20/20 starts at max |
| random 3-form seed 2002, Euclid.-max. | 3.023325 | 5.0e-15 | 3/12/0 | 2/13/0 | 3/12/0 | 1.699e+00 | 5.4e-15 | 1.3e-06 | 7.2e-07 | B_psi split (4,3); 15/20 starts at max |

### Split-G2 form (no expectation; report only)
| form / point | f = psi^2 | \|grad_R f\| | analytic #0/#neg/#pos | FD2 h=1e-4 #0/#neg/#pos | FD4 h=1e-2 #0/#neg/#pos | min \|nonzero\| (an.) | max \|zero-class\| (an.) | max \|H_fd2 - H_an\| | max \|H_fd4 - H_an\| | notes |
|---|---|---|---|---|---|---|---|---|---|---|
| split-G2 form, Euclid.-max. (multistart) | 2.000000 | 2.1e-15 | 6/9/0 | 6/9/0 | 5/9/1 | 4.000e+00 | 2.6e-15 | 8.0e-07 | 5.0e-07 | B split (4,3); 20/20 starts at max |
| split-G2 form, bare (123) frame | 1.000000 | 0.0e+00 | 3/8/4 | 3/8/4 | 3/8/4 | 2.000e+00 | 0.0e+00 | 8.9e-08 | 4.0e-07 | B split (4,3); T=+1.000000 |

### Verdicts
Expectation A: analytic PASS; FD2 (h=1e-4, pre-reg) PASS; FD4 (h=1e-2) PASS  (expected 11/4/0)
Expectation B: analytic PASS; FD2 (h=1e-4, pre-reg) FAIL; FD4 (h=1e-2) PASS  (expected 3/12/0)
Expectation C (random control): analytic PASS; FD2 (h=1e-4, pre-reg) FAIL; FD4 (h=1e-2) PASS  (expected 3/12/0)
FD2 vs analytic: worst max|H_fd2 - H_an| over all points = 2.18e-06
FD4 vs analytic: worst max|H_fd4 - H_an| over all points = 9.02e-07

### Spectra (analytic Hessian, sorted)
phi, bare Fano(123) frame: [-6. -6. -6. -6. -0. -0. -0.  0.  0.  0.  0.  0.  0.  0.  0.]
phi, assoc. frame #1 (g.Fano(123).R): [-6. -6. -6. -6. -0. -0. -0. -0. -0.  0.  0.  0.  0.  0.  0.]
psi_S2 seed 1000, Euclid.-max.: [-9.4024 -8.8473 -8.5527 -8.1957 -2.1851 -1.8913 -1.8003 -1.5378 -1.2847 -0.9328 -0.3285 -0.2412  0.      0.      0.    ]
random 3-form seed 2000, Euclid.-max.: [-12.7954 -12.4466  -8.9175  -7.9944  -7.4876  -6.9834  -6.7045  -6.2655  -5.7157  -4.794   -1.2257  -0.8092  -0.      -0.       0.    ]
split-G2 form, Euclid.-max. (multistart): [-8. -8. -8. -4. -4. -4. -4. -4. -4. -0. -0. -0. -0.  0.  0.]
split-G2 form, bare (123) frame: [-4. -4. -4. -4. -4. -4. -4. -4.  0.  0.  0.  2.  2.  2.  2.]

runtime 11.3 s

(Hitchin B for every form is in the `notes` column: φ and all five S2 forms are definite; the three random Gaussian 3-forms came out split (3,4)/(4,3) — a random 3-form on ℝ⁷ lands in one of the two open GL(7)-orbits, and these three landed in the split one; the split-G₂ control is (4,3).)

## 4. Verdict against the pre-registration

| Expectation | Pre-registered | Found (analytic Hessian, primary) | FD2 h=1e-4 (pre-reg) | FD4 h=1e-2 | Verdict |
|---|---|---|---|---|---|
| **A** φ at 6 associative frames | 11 zero / 4 negative | 11/4/0 at all 6; the 4 negative eigenvalues are all −6 | 11/4/0 at all 6 | 11/4/0 at all 6 | **PASS** |
| **B** ψ = g·φ (S2, s = 0.1), 5 seeds, Euclidean maximiser | 3 zero / 12 negative | 3/12/0 at all 5; smallest soft mode 0.21–1.23 ≫ 1e-6 | 3/12/0 for 1 seed; 0/15/0 or 2/13/0 for 4 seeds — **precision artefact, see below** | 3/12/0 at all 5 | **PASS** (analytic + FD4); FD2 count fails at TOL for the stated numerical reason |
| **C** random 3-forms (3 seeds), Euclidean maximiser | 3 zero / 12 negative | 3/12/0 at all 3 (all three landed in the split orbit; no definite non-S2 form was tested) | 3/12/0 for 1; 1/14/0, 2/13/0 for 2 — same artefact | 3/12/0 at all 3 | **PASS** (analytic + FD4) |
| Split-G₂ (report only) | none | Euclidean maximiser f = 2: 6 zero / 9 negative (spectrum −8³, −4⁶, 0⁶); the bare (123) frame is a saddle, f = 1, 3/8/4 | 6/9/0 and 3/8/4 | 5/9/1 and 3/8/4 (one zero-class eigenvalue sits at ≈ +1e-6, at the tolerance edge) | reported, no reading |

**FD-vs-analytic agreement.** max|H_FD2 − H_an| ≤ 2.2e-6 over all 16 points (≤ 5.3e-7 on the f = 1 points); max|H_FD4 − H_an| ≤ 9.0e-7. The FD2 count failures on B/C are exactly what the roundoff floor predicts: with f ≈ 2–4 and h = 1e-4, 4εf/h² ≈ 1e-6 = TOL, so eigenvalues the analytic Hessian puts at 10⁻¹⁵ are reported by FD2 at ~10⁻⁶ and straddle the zero class. FD4 (h = 1e-2, truncation ~h⁴, roundoff ~10⁻¹¹) removes the floor and reproduces every analytic count. The agreement check is therefore **PASS at the 1e-6 level for both stencils**; the *count* at the pre-registered h is not a usable zero-classifier for f > 1 at TOL = 1e-6, which is recorded as a method lesson (pre-registered h and TOL were chosen together without checking 4εf/h² against TOL).

**Why 11 = 8 + 3, and what the spectrum says.** The cleanest count is an orbit count: the maximiser set {φ² = 1} is the G₂-orbit of one associative frame (G₂ acts transitively on associative planes and SO(4) ⊂ G₂ acts on a plane's frames through SO(3)); the stabiliser of a frame (u,v,w) in G₂ is the Sp(1) fixing the plane pointwise, dim 3, so the orbit has dim 14 − 3 = 11 and its tangent space is automatically in the kernel of the Hessian. The 8 + 3 split is the fibration G₂/Sp(1) → G₂/SO(4) with fibre SO(4)/Sp(1) = SO(3). The 3 modes along F·so(3) are moreover *exact for any 3-form* (ψ(FR) = det R · ψ(F) for R ∈ O(3), so ψ² is O(3)-frame-invariant) — forced, not evidence. **The content of A is that there are no zero modes beyond the orbit tangent**: the normal Hessian is non-degenerate. In Grassmannian terms the 8 non-forced zero modes are the tangent directions of the associative Grassmannian G₂/SO(4) ⊂ Gr₃(ℝ⁷) (dim 12): the four normal directions carry the only non-zero curvature, all with eigenvalue −6. The equality of the four is forced by symmetry: the normal space of G₂/SO(4) in Gr₃(ℝ⁷) is the 4-dimensional piece V₊⊗V₋ of T_ξGr₃ = ℝ³⊗ℝ⁴ = (V₊³⊕V₊)⊗V₋ under SO(4) = Sp(1)₊·Sp(1)₋, and the subgroup fixing the frame u,v,w pointwise (Sp(1)₋) acts on it as the quaternionic representation ℍ, whose only invariant symmetric bilinear forms are scalars; the value −6 itself is just read off, not derived here. Under the S2 deformation the 8 flat directions acquire eigenvalues of order s (0.21–2.2 here; the four hard modes move to ≈ −8…−9.4) — the critical continuum is lifted to an isolated maximum, which is the content of B. Random forms do the same (C). The split-G₂ Euclidean maximiser keeps 3 extra zero modes beyond the frame: the maximal compact SO(4) ⊂ G₂^split moves the maximising plane along a 3-dimensional orbit (6 − 3 stabiliser), consistent with 6 = 3 + 3; this is a description of the numbers, not a reading.

## 5. What this does and does not show

This computation tests the **static-landscape degeneracy claim behind M1**: on orthonormal triples the maximiser set of φ² is a non-degenerate (Morse–Bott) 11-dimensional continuum — the G₂-orbit of one associative frame — with exactly 4 stiff normal directions (non-degeneracy at one frame is non-degeneracy everywhere on the orbit by homogeneity, so the six frames tested are replications, not a sample size); **all five sampled** S2 forms at the single scale s = 0.1, and **all three sampled** random forms (which happened to land in the split orbit), have an isolated maximum up to the forced frame symmetry, with 12 stiff directions. Genericity in the strict sense was not established — no sweep in s, no failure count — only 8/8 sampled forms. That is the geometric premise of "flat for φ, funnelled for ψ", *if* the ring's landscape is this one. It does **not** test the ring dynamics of mdcu-r4 (the K-phi / K-psi update rule, step budget, comass matching, locking criterion); in particular it has **not** been shown that the R4 ring energy is ψ² on orthonormal triples, or that the ring's state space and energy factor through V₃(ℝ⁷)/O(3) at all — the correspondence between f here and K-phi / K-psi is unverified, so PASS on A/B/C is evidence about the landscape of ψ², not about R4. It does not show that this degeneracy *causes* the R4 locking gap, and says nothing about whether φ's flatness is a feature or a defect for the compute-unit design — those remain the open question M1 was named for, and S-A (spontaneity) / S-D (the d ladder) remain the instruments. No G₂-specific physics reading is taken from "ψ locks more"; the R4 record line stands unchanged. Napkin grade; no anchor minted; the FD2-at-TOL lesson is the only process finding.

## 6. Cross-links

- MDCU round-4 results: qbp-compute-unit `doc/spikes/mdcu-round4-results.md` (record PR qbp-compute-unit#88, head `2c14c30`); R3 results `doc/spikes/mdcu-round3-results.md` (S2 sampler statistics §Secondaries).
- R4 planning-consequence table (pre-data): inter#194 [issuecomment-6431920143](https://github.com/JamesPagetButler/inter/issues/194#issuecomment-6431920143), row "COUPLING-ONLY killed → direct design input to QBP#776 rung 2 (E6)".
- QBP#776 E6 (rung 2, discrimination): the "selecting substrate should reproduce φ's flat, Haar-uniform signature and the controls' clustering" criterion — this note supplies the static-landscape half of that signature (11 flat vs 3 flat directions) as a candidate pre-stated measure, for oppenheimer/architecture to accept or reject when E6 is pre-registered.
- Conventions used: `docs/conventions/cd-doubling.md` (F3), `docs/conventions/fano-orientation.md` (F4), `analysis/473-dirac-probe/cdalg.py` (`cd_mul`, `D`).
- References: Harvey & Lawson 1982 (associative 3-planes, φ|_ξ = vol_ξ); Hitchin 2000 (stable 3-forms, B_ψ); Absil, Mahony & Sepulchre 2008 (Stiefel Hessian, retraction-independence at critical points); Edelman, Arias & Smith 1998.
