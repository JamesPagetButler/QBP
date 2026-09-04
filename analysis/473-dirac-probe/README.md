# #473 lit-path step 1 — algebraic Dirac operator + δ-landscape over 𝕊→𝕆→ℍ: flashlight results (2026-09-03/04)

**Status:** numerical probe (numpy, Schafer CD convention = `CDAlg.lean`), NOT a proof. Red Team (qbp-oppenheimer) vs Gemini Furey/Feynman, 2 rounds. Scripts in this directory (`dirac_probe.py`, `envelope.py`, `delta_formula.py`, `minpoly.py`, `landscape.py`, `pairhess.py`, `ledgerhess.py`, `flow.py`, `flow_big.py`); run from this directory. Issue comment: https://github.com/JamesPagetButler/QBP/issues/473#issuecomment-5535630651

## 1. Gemini's recommended D = i·Σₐ L_{eₐ} — KILLED

Σₐ L_{eₐ} = L_s, s = Σ eₐ (left-mult linear in the left slot). So D = i·L_s and D² = −L_s².

| Level | D² | "alternativity defect" Δ = Σ_{a<b}{Lₐ,L_b} | Tr f(D/Λ) |
|---|---|---|---|
| ℍ | 3·I | 0 | 4·f(√3/Λ) |
| 𝕆 | 7·I | 0 | 8·f(√7/Λ) |
| **𝕊** | **15·I** | **0** | **16·f(√15/Λ)** |

Δ ≡ 0 even in 𝕊: any two basis units generate a quaternion subalgebra, so the linearized left-alternative law a(bx)+b(ax)=(ab+ba)x holds on basis pairs. Zero spectral information at every level. Gemini's readout table ("3 nonzero eigenvalues = 3 generations", Weinberg angle) had no spectrum to read. **Gemini conceded (round 2).**

Lean-able kill statement (cheap `decide` over the sign table): `∀ x : CDAlg ℝ 4, s * (s * x) = -15 • x` for `s = Σ_{a=1}^{15} eₐ`.

## 2. The only non-trivial structure: the δ(s) landscape

For a generic imaginary unit s ∈ Im𝕊: spec(−L_s²) = {1−δ (×4), 1 (×8), 1+δ (×4)}, δ(s) ∈ [0,1].

| s | δ | meaning |
|---|---|---|
| s in any octonion subalgebra 𝕆⊂𝕊 | 0 | alternative direction; L_s² = −1 |
| generic s (2000 random) | 0.19 – 0.998 | continuous |
| s = (e₁+e₁₀)/√2 (zero-divisor direction) | 1 | spec {0×4, 1×8, 2×4}; 4-dim annihilator |

δ(s) = "distance of s from alternativity" — a genuine 𝕊→𝕆 cooling fingerprint (cooling = δ→0), and the 4/8/4 multiplicities match the ledger Hessian's {4,8,4}. **But s is a free direction on S¹⁴ (input), so δ is a parameter, not a forced number.**

## 3. Structural obstructions (why no finite background-free D can force a number)

| Fact | ℍ | 𝕆 | 𝕊 |
|---|---|---|---|
| associative envelope ⟨Lₐ⟩ | ℍ (dim 4) | M₈(ℝ) = Cl(6) (64) | **M₁₆(ℝ)** (256, full) |
| Im under G₂ | — | irreducible **7** | **1 ⊕ 7 ⊕ 7** (1 = ℓ = e₈) |

- Connes triple needs an associative *-algebra on H. The non-associative levels enter only via their envelope = full matrix algebra ⇒ trivial commutant ⇒ **no gauge content** without choosing a stabilizer direction (input).
- Schur: any G₂-covariant finite D on one copy of 𝕆 or 𝕊 is a few block scalars ⇒ cannot encode sin²θ_W (needs a chosen U(1)⊂G₂) or a generation multiplicity (H is one copy).
- Enlarging H covariantly (⋀²Im𝕊 = 1 ⊕ 5·7 ⊕ 3·14 ⊕ 27 under G₂) gives ~36 free block parameters, no forced ratios (Gemini's count; plausible, unverified).
- The Lean-verified "42" is a count of **basis** planes {eₐ,e_b} (a∈1..7, b∈9..15, b≠a+8) — a coordinate-choice set, not Aut(𝕊)-invariant. Σ projectors = diag(6 on the 14 non-ℓ imaginaries, 0 on ℓ) — the incidence count 7−1, not physics. (Gemini's "28/5·I by Schur" was wrong — Im𝕊 is reducible under G₂×S₃ — but its conclusion holds.)

## 4. Verdict for #473 AC2 (first pass)

**KILL, for the finite background-free spectral action over one CD copy:** it cannot force generation count, Weinberg angle, or any ℝ-non-trivial number. The minimal input is a direction s ∈ S¹⁴ ⊂ Im𝕊 (14 real parameters — smaller than Connes' A=ℂ⊕ℍ⊕M₃(ℂ), H=ℂ⁹⁶ + mass matrix, but an input). Gemini's revised prior for "3 generations forced": <1%.

**Reframe (the honest positive):** QBP's distinctive claim — the dynamical cascade 𝕊→𝕆→ℍ — reduces to a *dynamics* question on the δ(s) landscape: which direction does cooling select, and why? δ(s) is an *intrinsic, background-free order parameter* (no ∫d³x). That is the object #553's Strategy-C needs where it currently smuggles spacetime: the order parameter is algebraic; the integration measure is still owed and cannot come from a finite triple.

## 5. Dead-end register additions (do not re-fund)
- D = i·L_{Σeₐ} (scalar D² at all levels).
- "3 non-zero eigenvalues ↔ 3 generations" (eigenspaces ≠ rep multiplicities).
- Aut(𝕊)-covariant operators from the 42 basis planes (coordinate artifact; incidence count only).
- Weinberg angle from a G₂-covariant finite D (Schur).

## 6. δ closed form, minimal polynomial, Haar mean (2026-09-04, `delta_formula.py`, `minpoly.py`)

Write an imaginary sedenion as s = a + bℓ, a ∈ Im𝕆 (coords 1..7), b ∈ 𝕆 (coords 8..15, b₀ = coord 8 = ℓ-component), and the left-alternator T_s x := (ss)x − s(sx). Then −L_s² = |s|²·I − T_s and (numerically, exact to 1e-12, 20+ random samples each):

| Identity | Scope |
|---|---|
| spec(T_s) = {+δ ×4, 0 ×8, −δ ×4}, rank 8 generically | unit imaginary s |
| **δ(s) = ‖[a,b]‖ = ‖ab − ba‖ = 2‖a × Im b‖** | unit imaginary s |
| **T_s³ = ‖[a,b]‖²·T_s** (polynomial identity, no unit normalisation) | every imaginary s |
| T_s = 0 ⟺ ab = ba ⟺ s in an octonion subalgebra | |
| Haar mean over S¹⁴: ⟨δ²⟩ = 4·E‖a × c‖² = 4·(49−7)/255 = **56/85** (numerical 0.6585 vs 0.6588) | the "42" appears here as 49−7 = 42 incidence terms — again a count, not physics |

## 7. Landscape Hessians and the ledger cross-link (`landscape.py`, `ledgerhess.py`)

V(s) = ‖[a,b]‖² on S¹⁴ is Aut(𝕊) = G₂×S₃ invariant, has no couplings, and does **not depend on b₀** (V is a function of (a, Im b) only). Critical-point Hessians are profile-independent (∇V = 0 ⇒ Hess f(V) = f′(0)·Hess V).

| Critical set | spec(Hess V) on T S¹⁴ | Reading |
|---|---|---|
| vacua {[a,b]=0} (8-dim), generic point | {0 ×10, **8(1−b₀²)** ×6} | 6 massive modes (3⊕3̄ of residual SU(3)); the mass² is a modulus |
| vacuum s = e₁ or (e₁+e₉)/√2 | {0 ×10, 8 ×6} | b₀ = 0 |
| vacuum s = (e₁+e₈)/√2 | {0 ×10, 4 ×6} | b₀² = ½ |
| vacuum s = ℓ = e₈ | {0 ×16} | fully flat point |
| ZD ridge {δ = 1}, e.g. (e₁+e₁₀)/√2 and generic | {**−8 ×2, −4 ×2**, 0 ×12} | two unstable doublets (residual SU(2)); curvature ratio exactly 2:1 |

**Ledger cross-link (verified exactly):** the Sprint-12 ledger Hessian (`proofs/Sprint12-Inherited/Sedenion.lean:hessianEntry`, Hessian of |xy|² at the zero-divisor pair x = e₁+e₁₀, y = e₄−e₁₅, spectrum {0,4,8,12}×{16,4,8,4}, Tr = 128, Tr H² = 1152) is H = 2JᵀJ with J = [R_y | L_x], and its diagonal 16×16 blocks are **exactly −2R_y² and −2L_x²**, each with spectrum {0 ×4, 4 ×8, 8 ×4} = 2·(δ=1 alternator spectrum {0,1,2}×{4,8,4}). The ledger's 4/8/4 multiplicities *are* the alternator spectrum at a zero-divisor direction. Structural, not new physics.

## 8. Gradient-flow dynamics on S¹⁴ (`flow.py`, `flow_big.py`)

Law: ṡ = −∇_{S¹⁴}V (canonical choice — an **input**). Since V is independent of b₀ and homogeneous of degree 4, the sphere projection gives **ḃ₀ = 4V·b₀**: the vacuum modulus is driven monotonically away from 0 while V > 0 and freezes when the vacuum manifold is reached (every generic trajectory converges, V → 1e-30; endpoint has a ∥ Im b exactly). The ZD ridge is measure-zero unstable.

Endpoint statistics from Haar initial data on S¹⁴ (Haar: ⟨b₀²⟩ = ⟨|a|²⟩/7 = 1/15 each coordinate, i.e. b₀² : |a|² : |Im b|² = 1 : 7 : 7):

| Quantity | Haar start | Flow endpoint (N=24 000, dt=0.02, 5000 steps) |
|---|---|---|
| ⟨b₀²⟩ | 1/15 = 0.0667 | **0.1462 ± 0.0011** (1/7 = 0.1429 excluded at 3σ — the "1:3:3" guess from the 3000-sample run is dead) |
| ⟨\|a\|²⟩, ⟨\|Im b\|²⟩ | 7/15 each | 0.4315, 0.4223 (difference 0.009 ± 0.004 — consistent with the exact a↔Im b symmetry) |
| ⟨8(1−b₀²)⟩ (mean 6-mode mass²) | — | 6.83 |
| b₀² quantiles 10/25/50/75/90 % | — | 0.003 / 0.018 / 0.078 / 0.216 / 0.397 |
| b₀ growth ratio | — | median 1.44, max 15.7 |
| endpoint alignment | — | a ∥ Im b to machine precision on all samples |

No closed form found for 0.146; not pursued further (see firewall reading).

Firewall reading: these numbers are forced by (ℝ + doubling) + (gradient-flow law) + (Haar initial measure). The last two are inputs — and the initial measure on S¹⁴ is precisely what the substrate is supposed to supply. So the flow gives Strategy C a coupling-free order parameter and a dynamics-to-vacuum map, but does not by itself produce an AC2-grade forced number.
