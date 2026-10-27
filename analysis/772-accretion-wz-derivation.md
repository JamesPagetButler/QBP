# #772 AC2 — the accretion model's w(z), written down explicitly

**Status: v0.1 — seat-reviewed 2026-10-27 (qbp-oppenheimer); records' explicit form, not adopted physics.** Prepared 2026-10-26 by a delegated agent for the QBP seat (theory axis); the closed form in §4 step 7 was re-derived by hand by the seat before review. Every step is tagged **DERIVED** (follows algebraically from the previous step or a quoted ledger record) or **ASSUMED** (a modelling choice the records do not fix; the alternative is named). Source dossier: `analysis/772-wz-ledger-dossier.md`. Script: `analysis/772_wz_symbolic.py` (sympy 1.13.1; `run-bounded 2G 60 python3 analysis/772_wz_symbolic.py`, exit 0; the script `assert`s every DERIVED claim it prints, so exit 0 is the check). Script output is reproduced in §9.

Ledger: `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` v6.19.0. Records: `PRED-H-equals-Mdot-over-M` (T3 untested), `PROOF-M-proportional-to-a` (T1 coherent), `PRED-lambda-as-cross-term` (T1 marginal), `PRED-w-not-minus-1` (T1 marginal), `COMP-cmb-power-spectrum-accretion` (T1 coherent, I).

## 0. Result in one table

| Quantity | Value | Tag |
|---|---|---|
| Boundary Hubble rate | H_B(z) = A(1+z) + B/(1+z), A = Ṁ₀/M₀, B = βM₀ | DERIVED from Ṁ = Ṁ₀ + βM² (ASSUMED accretion law, step 3) + M ∝ a |
| H_B² | A²(1+z)² + 2AB + B²(1+z)⁻² | DERIVED (the record's "cross-term" identity) |
| ρ_DE identification | ρ_DE/ρ_c0 = H_B²/H₀² (reading I) | **ASSUMED** — the records do not say this, but it is the only reading that reproduces the record's numbers A≈0.21, B≈0.62 |
| **w_eff(z)** | **w_eff(z) = −1 − (2/3) · [(1+z)² − (1+z_t)²] / [(1+z)² + (1+z_t)²]**, with (1+z_t)² = B/A | DERIVED under reading I |
| equivalently | w_eff(z) = −1 − (2/3) tanh[ ln((1+z)/(1+z_t)) ] ; w_eff(0) = −(r+5)/(3(r+1)), w_eff(∞) = −5/3, r = B/A | DERIVED |
| one free parameter | z_t only; the overall scale A+B = √Ω_Λ ≈ 0.83 drops out of w(z) | DERIVED |
| z_t = 0.7 ⇒ | r = 2.89, A = 0.213, B = 0.615, 2AB = 0.262 (record: 0.21, 0.62, 0.26) | DERIVED reconstruction of the record's numbers |
| sign of w+1 | **> 0 for z < z_t (quintessence-like), = 0 at z = z_t, < 0 for z > z_t (phantom-like)** | DERIVED |
| matches `PRED-w-not-minus-1`? | **Yes** — same crossing, same sign on both sides | — |
| matches COMP's −1.25 + 0.70 z/(1+z)? | **No** — opposite sign on both sides (COMP is phantom at z<0.56, quintessence above); magnitudes also differ (w₀: −0.68 vs −1.25) | — |
| CPL tangent of the derived curve | (w₀, w_a) = (−0.676, −0.509) at z_t = 0.7 | DERIVED |

## 1. Starting identities

**Step 1 (DERIVED, quoted).** `PRED-H-equals-Mdot-over-M`: "the Hubble parameter H = Ṁ/M (fractional mass accretion rate)". `PROOF-M-proportional-to-a`: "From H = Ṁ/M and H = ȧ/a, it follows that dM/da = M/a → M ∝ a = 1/(1+z)." Writing M(z) = M₀/(1+z) with M₀ = M(z=0). This step is model-independent (the record says so) and I take it as given. Note for later: it uses H = ȧ/a and H = Ṁ/M as **the same, total** H — a point that constrains the ASSUMED step 5.

**Step 2 (DERIVED).** For any accretion law Ṁ = f(M), the Hubble rate as a function of z is H(z) = f(M₀/(1+z)) · (1+z)/M₀. (Substitution of step 1 into H = Ṁ/M.)

## 2. The two-mode accretion law and the cross-term

**Step 3 (ASSUMED — stated by the record, but a modelling choice).** `PRED-lambda-as-cross-term`: "With Ṁ = Ṁ₀ + βM² (constant + Bondi)". The chosen law is the two-term sum of a constant feed Ṁ₀ and a Bondi term βM². *Alternatives the repo itself names:* Eddington Ṁ ∝ M (`reviews/matter_era_a0_findings.md:40-43` table: α = 0, 1, 2); a Hawking loss term −γ/M² (`archive/SESSION-13-WORKING-NOTES.md:130`: "Including Hawking, the full H² expansion picks up additional terms whose sign depends on …"); time-varying β (the paper's "cyclical modulation of the Bondi accretion rate B", `paper/quaternion_physics.md:187`). Each alternative changes the functional form below; none is in the ledger as a w(z) statement.

**Step 4 (DERIVED).** Substituting step 3 into step 2 (script STEP A):

H_B(z) = Ṁ/M = Ṁ₀/M + βM = (Ṁ₀/M₀)(1+z) + βM₀/(1+z) ≡ **A(1+z) + B/(1+z)**, A := Ṁ₀/M₀, B := βM₀.

Squaring: **H_B² = A²(1+z)² + 2AB + B²(1+z)⁻²**. This is exactly the record's text: "H_B² = A²(1+z)² + 2AB + B²(1+z)⁻². The constant term 2AB behaves as an effective cosmological constant. … It's a cross-term in an accretion rate expansion." The cross-term is the product term of the binomial square — "interference term between two accretion modes" is the record's language for the same thing. (Lean: `lambda_cross_term` in `proofs/QBP/Cosmo/AlgebraicIdentities.lean:140-150`, main checkout only, not ledger-linked.)

Decomposition of H_B² by (1+z) power: a **(1+z)² "stiff" term A²** (behaves like a fluid with w = −1/3), a **constant 2AB** (w = −1), and a **(1+z)⁻² "phantom" term B²** (w = −5/3). The matter term Ω_m(1+z)³ does **not** appear in H_B² — where it lives is the ASSUMED step 5.

## 3. Identifying ρ_DE — the step the records underdetermine

**Step 5 (ASSUMED — the central fork).** The records never say how H_B relates to the Friedmann equation H² = (8πG/3)(ρ_m + ρ_DE). Two readings:

- **Reading (I) — additive DE sector:** H²/H₀² = Ω_m(1+z)³ + H_B²/H₀², i.e. ρ_DE/ρ_c0 ≡ H_B²/H₀² = A²(1+z)² + 2AB + B²(1+z)⁻² (A, B now in units of H₀). Normalisation: H_B(0)² = (A+B)² = Ω_Λ = 1 − Ω_m. **Evidence this is the reading Session 12 used:** `archive/HANDOFF-simulation-workloads.md:76` "Accretion H(a) = A/a + Ba with A+B = √Ω_DE ≈ 0.83", and the record's own numbers A ≈ 0.21, B ≈ 0.62 give (A+B)² = 0.689 ≈ Ω_Λ (script STEP C). *Cost:* H_B ≠ ȧ/a, so "H = Ṁ/M" in step 1 is then only the DE part of H, which contradicts the literal premise of `PROOF-M-proportional-to-a` (same total H on both sides). Also the "z_t = deceleration→acceleration transition" gloss in `PRED-H-equals-Mdot-over-M` must then be re-read as mode-equality (step 7).
- **Reading (II) — H_B is the total H:** H = ȧ/a = Ṁ/M = H_B literally, matter inside; ρ_DE/ρ_c0 = H_B²/H₀² − Ω_m(1+z)³, normalisation A+B = 1. *Cost:* H_B² grows only as (1+z)² while matter grows as (1+z)³, so ρ_DE < 0 for z ≳ 0.5 (script STEP F: ρ_DE/ρ_c0 = +0.128 at z=0.3, −0.78 at z=0.7, −7.5 at z=2) and w_eff is undefined/violent there (w_eff(0) = −0.07, w_eff(0.3) = +5.5). Moreover, under (II) H(a) = A/a + Ba **is** the whole expansion history by definition — whatever matter is "inside" it — so ä = (aH) d(aH)/da = 2Ba(A + Ba²) > 0 for all a (script STEP D, sympy `is_positive: True`): the model **never decelerates**, and so cannot produce the "deceleration→acceleration transition" the records attach to z_t. This is a statement about reading (II) itself, not about a matter-free limit. Reading (II) is therefore not viable as a late-time DE model without further physics (the repo's own `reviews/matter_era_a0_findings.md:45-50` reaches the matching conclusion for the matter era: "There must be additional saturation physics").

**I proceed under reading (I)** because it is the only one that reproduces the record's numbers and is the one the Session-12 handoff wrote down; I flag that the records as worded are ambiguous between (I) and (II), and that (I) is in tension with the literal "same H" premise of step 1. The minimal extra assumption needed to make (I) consistent: *"H = Ṁ/M describes the boundary/DE sector only; interior matter adds separately in H²"* — this sentence appears nowhere in the ledger or repo and would need to be ratified as a record edit.

## 4. The equation of state

**Step 6 (DERIVED, definition).** For the non-matter remainder treated as a single fluid with continuity ρ̇_DE = −3H(1+w)ρ_DE, w_eff(z) = −1 − (1/3) d ln ρ_DE / d ln(1+z). (Standard; no QBP content.)

**Step 7 (DERIVED, script STEP B).** With ρ_DE ∝ A²(1+z)² + 2AB + B²(1+z)⁻², (1+z) dρ/dz = 2A²(1+z)² − 2B²(1+z)⁻², so

w_eff(z) = −1 − (2/3) · [A²(1+z)² − B²(1+z)⁻²] / [A²(1+z)² + 2AB + B²(1+z)⁻²].

Let u = (1+z)², r = B/A. Numerator ∝ (u² − r²), denominator ∝ (u + r)², so (u−r)(u+r)/(u+r)² = (u−r)/(u+r):

**w_eff(z) = −1 − (2/3) · [(1+z)² − r] / [(1+z)² + r] = −1 − (2/3) tanh[ ln((1+z)/√r) ].**

Properties (all DERIVED, sympy-checked): w_eff depends on **r = B/A only** (the normalisation A+B drops out). w_eff = −1 exactly where (1+z)² = r, i.e. where the two accretion modes are equal, A(1+z) = B/(1+z). w_eff(0) = −(r+5)/(3(r+1)); w_eff → −5/3 as z → ∞; w_eff → −1/3 as z → −1 (far future). The curve is monotone decreasing in z: quintessence-like at late times, phantom-like at early times. The "curvature" that `PRED-w-not-minus-1` attributes to the "third term B²(1+z)⁻²" is the tanh shape — a CPL fit cannot capture the −5/3 plateau.

**Step 8 (ASSUMED — what fixes z_t).** The records call z_t ≈ 0.7 "the observed deceleration-acceleration transition" and "an INPUT". Under reading (I) with Ω_m = 0.315, (A+B)² = 0.685, the actual q = 0 redshift is **≤ 0.55 for every value of B/A** (script STEP E: scan over r ∈ [0.1, 10⁵]; maximum 0.550 at r ≈ 5.6; for r ≲ 0.1 the model does not accelerate today at all, q(0) ≥ 0; z_{q=0} rises monotonically with r up to the maximum and then falls to the r → ∞ closed form (4Ω_Λ/Ω_m)^{1/5} − 1 = 0.541, which the scan tail reproduces; ΛCDM gives 0.632). So q(0.7) = 0 is **unattainable**: if z_t = 0.7 is literally the deceleration→acceleration redshift, the two-mode model cannot be calibrated to it. What the record's numbers actually encode is **mode-equality**, (1+z_t)² = B/A: with z_t = 0.7, r = 2.89, and with (A+B)² = 0.685 this gives A = 0.213, B = 0.615, 2AB = 0.262 — matching the record's "A ≈ 0.21, B ≈ 0.62, 2AB ≈ 0.26" to the quoted precision (script STEP C). I therefore read z_t as the mode-equality redshift (which coincides with the w = −1 crossing). *Alternative:* define z_t by q = 0 — then no (A, B) exist for z_t = 0.7, and the closest model (r ≈ 5.6, q=0 at z=0.55) has its w=−1 crossing at z = √5.6 − 1 = 1.37, not 0.7.

Side-finding for the record text (not a step): `PRED-lambda-as-cross-term` says "2AB ≈ 0.26 ≈ Ω_Λ". With Ω_Λ = 0.685, 2AB = 0.26 is 38 % of Ω_Λ; it is (A+B)² = 0.69 that matches Ω_Λ. The cross-term is the constant *part* of the DE density, not the whole of it. The record's numbers are self-consistent; the "≈ Ω_Λ" gloss is not. Oppenheimer to decide whether that is a record edit.

**Step 9 (not used).** The "8 % fluctuation" (`PRED-H-equals-Mdot-over-M` item 3, `MEAS-hubble-tension`) is a statement about ΔH₀/H₀ between epochs, not a parameter of w(z); it does not enter the functional form. `reviews/walking_the_chain_2026-04-30.md:251` records that the late-time model gives ~0.9 %, not 8.3 %.

## 5. Numbers

Script STEP F (reading I, z_t = 0.7 ⇔ r = 2.89; reading II with A+B = 1, Ω_m = 0.315; the two CPL curves for comparison):

| z | **(I) derived w_eff** | (II) total-H w_eff | ρ_DE(II)/ρ_c0 | COMP CPL −1.25 + 0.70 z/(1+z) | DESI Y1 CPL −0.55 − 1.3 z/(1+z) |
|---|---|---|---|---|---|
| 0 | **−0.676** | −0.067 | +0.685 | −1.250 | −0.550 |
| 0.3 | **−0.825** | +5.516 | +0.128 | −1.088 | −0.850 |
| 0.7 | **−1.000** | undefined (ρ_DE<0) | −0.784 | −0.962 | −1.085 |
| 1 | **−1.107** | undefined (ρ_DE<0) | −1.736 | −0.900 | −1.200 |
| 2 | **−1.343** | undefined (ρ_DE<0) | −7.467 | −0.783 | −1.417 |

w = −1 crossings: derived (I) z = 0.700 (by construction); COMP CPL z = 0.556; DESI Y1 CPL z = 0.529.
H(z)/H_ΛCDM(z) under (I), z_t = 0.7: 1.000 (z=0), 0.954 (0.3), 0.955 (0.5), 0.963 (0.7), 0.977 (1.0) — i.e. 2.3–4.6 % *below* ΛCDM at z = 0.3–1, consistent in magnitude with `PRED-w-not-minus-1` notes "differ from ΛCDM by 3-5% at z = 0.3-0.7".

## 6. Sign of (w_eff + 1) and the two ledger curves

| | z < z_t | z = z_t | z > z_t |
|---|---|---|---|
| **Derived (I)** | w + 1 > 0 (quintessence-like) | 0 | w + 1 < 0 (phantom-like) |
| `PRED-w-not-minus-1` (qualitative) | "w > −1 at z < z_t (quintessence-like)" | "w ≈ −1 at z_t ≈ 0.7" | "w < −1 at z > z_t (phantom-like)" |
| `COMP` curve −1.25 + 0.70 z/(1+z) | w + 1 < 0 (phantom; −1.25 at z=0) | crosses at z = 0.556 | w + 1 > 0 (quintessence; → −0.55) |
| DESI Y1 CPL (−0.55, −1.3), quoted in the record | w + 1 > 0 | crosses at z = 0.53 | w + 1 < 0 |

**Plain statement.** Under the one ASSUMED identification that reproduces the record's own numbers (reading I), the derivation **reproduces `PRED-w-not-minus-1` exactly in sign and crossing** and gives it the explicit form w_eff(z) = −1 − (2/3)[(1+z)² − (1+z_t)²]/[(1+z)² + (1+z_t)²]. It **does not reproduce the COMP curve**: −1.25 + 0.70 z/(1+z) has the opposite sign of (w+1) on both sides of its crossing and a different w₀ (−1.25 vs −0.68). The CPL tangent of the derived curve is (w₀, w_a) = (−0.68, −0.51) — same quadrant as DESI Y1's (−0.55, −1.3), opposite quadrant to COMP's (−1.25, +0.70). No reading of the records I can construct yields (−1.25, +0.70): reading (II) is undefined for z ≳ 0.5; swapping the roles of A and B does not help (w(z) depends only on r = B/A, and r → 1/r just moves the crossing). The COMP curve's provenance is "Session 12 narrative text, no artefact on disk" (dossier §2a), so whether it was a sign/convention slip in the CAMB input (e.g. w(a) = w₀ + w_a(1−a) entered with the wrong sign on w_a, or the curve's quadrant transposed) cannot be checked. I note without inference that COMP's z → ∞ limit (−1.25 + 0.70 = −0.55) equals DESI Y1's w₀.

**Does the ledger underdetermine w(z)?** For the *functional form*: yes, at step 5 (reading I vs II) and step 3 (accretion law). For the *sign pattern*: no — every viable reading of the two-mode law gives quintessence-below / phantom-above, agreeing with `PRED-w-not-minus-1` and disagreeing with COMP. Minimal extra assumptions to get each curve: for `PRED-w-not-minus-1`, assumptions (I) + mode-equality z_t (both already implicit in the record's numbers); for the COMP CPL curve, none available within the records — it would need a different accretion law or a different DE identification not written down anywhere in the repo.

## 7. ASSUMED steps (summary for the reviewer)

| # | Assumption | Alternatives | Which the records back |
|---|---|---|---|
| 3 | Accretion law Ṁ = Ṁ₀ + βM² | Eddington term; Hawking loss; time-varying β | Record states the two-mode law explicitly |
| 5 | Reading (I): ρ_DE/ρ_c0 = H_B²/H₀², matter added separately | Reading (II): H_B is total H | Numbers in `PRED-lambda-as-cross-term` + HANDOFF:76 use (I); the *words* of `PROOF-M-proportional-to-a` imply (II); (II) fails for z ≳ 0.5 |
| 5' | Normalisation (A+B)² = Ω_Λ = 0.685 (Planck, from the record's measured_value) | any other Ω_Λ | HANDOFF:76 "A+B = √Ω_DE ≈ 0.83"; w(z) is independent of it anyway |
| 8 | z_t is the mode-equality redshift (1+z_t)² = B/A | z_t is the q=0 redshift | Record's numbers encode mode-equality; q=0 at 0.7 is unattainable under (I) |
| 6 | Single-fluid w_eff definition | none standard | convention |

## 8. Seat decisions (qbp-oppenheimer, 2026-10-27) — proposals to the ledger lanes, no physics adopted here

1. **Reading (I) is taken as the explicit form the records' own numbers imply.** It is the only reading reproducing A ≈ 0.21, B ≈ 0.62, z_t ≈ 0.7 (step 8, script STEP C); reading (II) is excluded on a DERIVED fact: under (II) H(a) = A/a + Ba is the whole expansion history, and ä = 2Ba(A + Ba²) > 0 for all a (script STEP D) — the model never decelerates, whatever is inside H. Status: this is the model's w(z) as written down, ASSUMED where tagged; adopting it as physics is not done here. *Proposed record note (steward lane — cth-implementor shape, qbp-implementor edit; a note documenting the ambiguity, NOT a new postulate written into the record):* add to `PRED-H-equals-Mdot-over-M` and `PROOF-M-proportional-to-a` a `review_flag`/note of the form "The records are ambiguous about what H_B = Ṁ/M is the rate of. Their own numbers (A ≈ 0.21, B ≈ 0.62, (A+B)² ≈ Ω_Λ) require H_B to be the dark-energy sector only, with matter added separately in the Friedmann sum (reading I, `analysis/772-accretion-wz-derivation.md` step 5); the words 'H = ȧ/a = Ṁ/M' read as total H (reading II). Reading II never decelerates (DERIVED: ä = 2Ba(A + Ba²) > 0) and yields ρ_DE < 0 for z ≳ 0.5, so the numbers, not the words, are what the model as computed used. Whether reading I is adopted as physics is open." (Gemini review @ 7914fa5 BLOCKING: the earlier draft of this proposal wrote reading I into the record as a statement; this wording records the fork instead.)
2. *Proposed `review_flag` on `PRED-lambda-as-cross-term`:* "arithmetic: 2AB = 0.26 is 38 % of Ω_Λ = 0.685; it is (A+B)² = 0.69 that matches Ω_Λ; 2AB is the constant part of H_B²." (Step 8 side-finding.)
3. *Proposed notes edit on `PRED-lambda-as-cross-term` / `PRED-w-not-minus-1`:* z_t ≈ 0.7 is the mode-equality redshift A(1+z_t) = B/(1+z_t), i.e. the w = −1 crossing; under reading (I) with Ω_m = 0.315 the deceleration→acceleration redshift (q = 0) is z ≈ 0.54, not 0.7 (script STEP E: 0.543).
4. **`COMP-cmb-power-spectrum-accretion`:** #772 AC1 (`review_flag` + `status: contested`) is confirmed on two independent grounds: (a) wrong sign pattern relative to the model it approximates (§6 — opposite sign of w+1 on both sides of its crossing); (b) no reproduce-path in the repo (`docs/conventions/anchor-prefix-policy.md:40` requires one; dossier §2a: "Session 12 narrative text, no artefact on disk"). The CAMB raw outputs are ANCHOR-PENDING per `paper/quaternion_physics.md`.
5. **The explicit form is the curve `qbp-desi-fit` pre-registers** (architect-directed spike, inter#224): w_eff(z) = −1 − (2/3)[(1+z)² − (1+z_t)²]/[(1+z)² + (1+z_t)²], with z_t the single shape parameter and (A+B)² = Ω_DE fixing the normalisation. It is proposed as the functional form in `PRED-w-not-minus-1`'s notes (#772 AC4). The CPL tangent (w₀, w_a) ≈ (−0.68, −0.51) is reported for comparison only — it is not the pre-registered curve (it misses the −5/3 plateau, step 7).

**Not claimed.** Nothing here says the accretion model fits data; it says what the model's own curve is. Whether that curve survives DESI DR2 + Pantheon+ (AC5 / `qbp-desi-fit`) and the CAMB re-run (AC3) is not addressed in this document.

## 9. Script output (verbatim, `run-bounded 2G 60 python3 analysis/772_wz_symbolic.py`)

```
==============================================================================
STEP A  Mdot = Mdot0 + beta M^2, M = M0/(1+z)  =>  H_B = Mdot/M
  H_B = M0*beta*z/(z**2 + 2*z + 1) + M0*beta/(z**2 + 2*z + 1) + Mdot0*z/M0 + Mdot0/M0    (A := Mdot0/M0, B := beta*M0)
  check H_B == A(1+z) + B/(1+z): True
  H_B^2 expanded: A**2*z**2 + 2*A**2*z + A**2 + 2*A*B + B**2/(z**2 + 2*z + 1)
==============================================================================
STEP B  Reading (I): rho_DE/rho_c0 = H_B^2/H0^2 (boundary rate is the DE sector only)
  w_eff(z) = -(5*A*z**2 + 10*A*z + 5*A + B)/(3*(A*z**2 + 2*A*z + A + B))
  with r = B/A:  w_eff(z) = -(r + 5*z**2 + 10*z + 5)/(3*(r + z**2 + 2*z + 1))
  closed form -1 - (2/3)((1+z)^2 - r)/((1+z)^2 + r)  matches: True
  w_eff(z) + 1 = 0  solved for u=(1+z)^2: [r]   => (1+z)^2 = r = B/A  (mode-equality redshift)
  limits: z=0 -> (-r - 5)/(3*(r + 1))  ; z->inf -> -5/3
  in terms of z_t ((1+z_t)^2 = B/A):  w_eff = (-5*(z + 1)**2 - (z_t + 1)**2)/(3*((z + 1)**2 + (z_t + 1)**2))
  CPL tangent at z=0 (s = z/(1+z)): w0 = (-r - 5)/(3*(r + 1))   wa = dw/ds|0 = -8*r/(3*(r + 1)**2)
==============================================================================
STEP C  Reconstruct the record's numbers: A~0.21, B~0.62, z_t~0.7, Omega_Lambda=0.685
  B/A = 2.952  ->  z_t = sqrt(B/A) - 1 = 0.718   (record says z_t ~ 0.7)
  (A+B)^2 = 0.689  (= Omega_Lambda 0.685: matches HANDOFF 'A+B = sqrt(Omega_DE) ~ 0.83')
  2AB = 0.260  (record text says '2AB ~ 0.26 ~ Omega_Lambda' — 0.26 != 0.685; it is 38% of it)
  From (A+B)^2=0.685 and (1+z_t)^2=B/A with z_t=0.7:  A=0.213, B=0.615, 2AB=0.262
==============================================================================
STEP D  Reading (II): H_B is the TOTAL Hubble rate (H = adot/a = Mdot/M literally), matter inside
  rho_DE/rho_c0 = H_B^2/H0^2 - Omega_m (1+z)^3 ;  normalisation A+B = 1
  w_eff(z) = (-(B**2 + (z**2 + 2*z + 1)*(A**2*z**2 + 2*A**2*z + A**2 + 2*A*B - Omega_m*(z + 1)**3))*(z**2 + 2*z + 1) + (z + 1)*(B**2*(2*z + 2) + (z**2 + 2*z + 1)**2*(-2*A**2*z - 2*A**2 + 3*Omega_m*(z + 1)**2))/3)/((B**2 + (z**2 + 2*z + 1)*(A**2*z**2 + 2*A**2*z + A**2 + 2*A*B - Omega_m*(z + 1)**3))*(z**2 + 2*z + 1))
  under (II) H(a) = A/a + B a IS the whole expansion history: adot = A + B*a**2  addot = 2*B*a*(A + B*a**2)  is_positive: True  (never decelerates, whatever is inside H)
==============================================================================
STEP E  deceleration parameter q(z) under reading (I) + matter, Omega_m = 0.315, (A+B)^2 = 0.685
  with z_t(mode-equality)=0.7 -> A=0.213, B=0.615: q=0 at z = 0.543
  LCDM reference (Omega_m=0.315): q=0 at z = 0.632
  scan of q=0 redshift vs r=B/A under (I), r in [0.1, 1e5] (nan = q(0)>=0, no acceleration today): r=0.1:z=nan, r=0.562:z=0.375, r=3.16:z=0.545, r=17.8:z=0.546, r=100:z=0.542, r=562:z=0.542, r=3.16e+03:z=0.541, r=1.78e+04:z=0.541, r=1e+05:z=0.541
  r->inf analytic limit (4 Omega_L/Omega_m)^(1/5) - 1 = 0.541; scan tail r=1e5: z=0.541
  maximum attainable q=0 redshift under (I) with Omega_m=0.315: z = 0.550 at r = 5.6  -> q(z=0.7)=0 is NOT attainable for any A/B; z_t=0.7 can only be the mode-equality redshift
  H(z)/H_LCDM(z) under (I) with z_t=0.7: z=0: 1.000, z=0.3: 0.954, z=0.5: 0.955, z=0.7: 0.963, z=1.0: 0.977
==============================================================================
STEP F  numeric table w_eff(z)
| z | (I) r=(1+z_t)^2, z_t=0.7 | (II) total-H, Om=0.315 | rho_DE(II)/rho_c0 | COMP CPL -1.25+0.70 z/(1+z) | DESI Y1 CPL -0.55-1.3 z/(1+z) |
|---|---|---|---|---|---|
| 0 | -0.676 | -0.067 | +0.685 | -1.250 | -0.550 |
| 0.3 | -0.825 | +5.516 | +0.128 | -1.088 | -0.850 |
| 0.7 | -1.000 | undefined (rho_DE<0) | -0.784 | -0.962 | -1.085 |
| 1 | -1.107 | undefined (rho_DE<0) | -1.736 | -0.900 | -1.200 |
| 2 | -1.343 | undefined (rho_DE<0) | -7.467 | -0.783 | -1.417 |

w = -1 crossings:  (I) z = 0.7 ; COMP CPL z = 0.556 ; DESI CPL z = 0.529
sign of (w+1), computed at z = crossing/2 and 2*crossing+1:
  (I) derived:  below: quintessence-like (w+1>0), above: phantom-like (w+1<0)
  DESI Y1 CPL:  below: quintessence-like (w+1>0), above: phantom-like (w+1<0)
  COMP CPL:     below: phantom-like (w+1<0), above: quintessence-like (w+1>0)  — OPPOSITE to (I)
CPL tangent of (I) at z_t=0.7: w0 = -0.676  wa = -0.509
```
