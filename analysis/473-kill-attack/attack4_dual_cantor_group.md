# Attack 4 — the dual Cantor group of the Cayley–Dickson index tower (vs Prop 10′ / 13(a) / 15)

**Target.** `docs/foundations/473-ac1-first-link-2026-09-04.md` §1 rows 10′, 13, 15 and §6 "do not re-fund": *the only algebra-native finite cover of the vacuum S² is the S₃-orbifold S²(2,2,3) and it pushes down no measure; the algebra supplies no profinite / measure-carrying object beyond that cover.*

**Unexamined object.** The CD construction is indexed by a group: at level n the basis is e_m, m ∈ G_n = (ℤ/2)ⁿ, with e_m e_k = σ(m,k) e_{m⊕k} (`CDAlg.mulCoeff`, XOR-on-`Fin`). The tower's index group is the direct limit G_∞ = ⊕_ℕ ℤ/2; its Pontryagin dual Ĝ = ∏_ℕ ℤ/2 is a profinite group — the Cantor group — with a canonical probability Haar measure (fair coin). It is algebra-native (the dual of the construction's own indexing), not built from ℝ. Question: does it force anything on the state sphere S¹⁴, the vacuum S², or a number?

## 0. Driver's sealed position (written before any computation)

> The dual Cantor group's Haar measure induces only uniform measure over index-labelled combinatorial objects — basis vectors, the 84 basis-sum ZDs / 42 planes — and nothing on the continuum S¹⁴ or the vacuum S²; no ℝ-non-trivial number.

Sealed 2026-09-24 before running any script in this directory. Everything below is tested against it; §D says where it held and where it needed amendment.

## 1. Verdict and key numbers (read this first)

| Question | Answer | Evidence |
|---|---|---|
| Is there an algebra-native profinite object beyond the S₃-orbifold cover? | **Yes** — Ĝ = ∏_ℕ ℤ/2, the Pontryagin dual of the tower's index group ⊕_ℕ ℤ/2. It acts on the whole CD tower by **automorphisms** (e_m ↦ χ(m)e_m), and the tower ℝ ⊂ ℂ ⊂ ℍ ⊂ 𝕆 ⊂ 𝕊 ⊂ … is exactly its Galois correspondence: Fix(ker(Ĝ → Ĝ_k)) = CD_k. So Prop 10′'s sentence "the one cover the algebra supplies" has a WORDING GAP, not a defect: Prop 10′ is about profinite COVERS transporting measure, and Ĝ is a group that produces no cover (§C); but the algebra does supply a canonical profinite object, its Galois group, which the sentence did not mention. | §A, [C1] |
| Does it force anything on the continuum (S¹⁴, the vacuum S², ℝ)? | **No.** Its action on any finite level factors through the finite quotient Ĝ_n (order 2ⁿ; 16 for 𝕊). This is a theorem, not a computation: a continuous homomorphism from a profinite group into a Lie group (Aut 𝕊 = G₂ × S₃) has finite image (no small subgroups). The profinite structure is inert on every finite-dimensional algebra. | [C2] |
| What does Haar on Ĝ push to? | Averaging over Ĝ is the projection 𝕊 → ℝ·1 (the Reynolds operator onto the fixed subalgebra = the ground field). Fourier dual of Haar = δ₀ on the index group: **the real unit, off the state sphere**. On S¹⁴ the Haar average of every orbit is 0. | [B0] |
| Ĝ₄ inside Aut(𝕊) = G₂ × S₃ | Ĝ₄ = (ℤ/2)⁴ = **exactly** the diagonal (sign-flip) automorphisms — all 16 characters are automorphisms, no other sign function is (exhaustive at n=3: 8 of 128; 1000-sample null at n=4: 0). Ĝ₄ = Ĝ₃ × ⟨χ₈⟩ with Ĝ₃ = (ℤ/2)³ ⊂ G₂ (the classical diagonal subgroup) and χ₈ = the S₃ reflection r₀: (a, b₀, c) ↦ (a, −b₀, −c). Ĝ₄ ∩ S₃ = {1, r₀}. | [A2], [A2′], [A3] |
| Ĝ₄ and the 84 ZDs / 42 planes | The 42 planes **are** the Ĝ₄-orbits of the 84 basis-sum ZDs (orbits of size 2 mod ±). Haar on Ĝ₄ is precisely the "84 → 42" identification — combinatorial, as sealed. | [A4] |
| Where do the 84 ZDs / 42 planes sit in the orbit space? | **One point**: (|a|, |Im b|, b₀, ⟨a,Im b⟩) = (1/√2, 1/√2, 0, 0), V = 1 — the ZD ridge, the *maximum* of V, not on the vacuum S² at all. Uniform measure over the 42 pushes to a **delta**, not a non-uniform measure on S². ⟨b₀²⟩ = 0. | [B2] |
| Where do the 15 imaginary basis vectors sit? | 7 at (θ = 0°, b₀ = 0), 7 at (θ = 90°, b₀ = 0), 1 at the pole — i.e. **exactly the three cone points of S²(2,2,3)** (Prop 15's branch locus: order-2 points {0,60,120}°, {30,90,150}°, order-3 point ±ℓ) with weights **(7, 7, 1)/15** = the G₂-isotypic dimensions of Im𝕊 = 7 ⊕ 7 ⊕ 1. | [B1] |
| ⟨b₀²⟩ under the index-counting measure | **1/15 = 0.0667** — a fourth number, but it equals the N-measure's own initial (β = 0, no-rule) value 0.067 in Prop 9's table, because *any* measure symmetric under permuting the 15 indices has isotropic second moments. Not a rule endpoint (0.146, 1/3, 1). | [B1], [B3] |
| Other index-native discrete measures | 126 basis-sum vacua → ⟨b₀²⟩ = **1/9**; all 210 basis sums → 1/15; all 2¹⁵−1 index subsets → 1/15. Different combinatorial levels, different numbers; nothing selects a level. The 1/9 arises only because the 42 deleted ZD pairs never contain index 8. | [B3] |
| Rule-invariance (the one genuine wrinkle) | The basis-atom measure is supported inside the vacuum manifold (V = 0, rule field F = 0 on all 15 atoms), so it is a **fixed point of the quench and of every member of the Gibbs family e^{−βV}** — quench and anneal *agree* on it (1/15 = 1/15), while the ℓ-axis map still sends it to 1. The quench/anneal ambiguity of Props 9/12 is a property of the N-measure, not of every algebra-associated initial measure. | [B1] |
| Sealed position | **Held on every clause**; amended on one point of framing (§D): the index side pushes a (7,7,1)/15 atomic measure onto the vacuum S² — algebra-associated, chart-free, sitting on the orbifold's branch locus — but it comes from the *finite* level-4 counting measure (Haar on the finite group G₄), not from the Cantor group's Haar, it is basis-dependent on S¹⁴, and its number is the isotropic 1/15. | §D |

**Bottom line for #473:** Prop 10′ should be *re-worded*, not reversed: the algebra supplies a profinite object (the tower's dual Cantor group, its Galois group), but every profinite group acting continuously on a finite-dimensional algebra acts through a finite quotient, so no profinite structure can ever reach the continuum — a stronger and cleaner obstruction than "the only cover pushes down no measure". Prop 13(a) is **not** met: the only measure the indexing pushes onto the vacuum S² is the dimension-weighted counting measure on Prop 15's cone points, and its ⟨b₀²⟩ = 1/15 is the trivial isotropic moment. No ℝ-non-trivial number is forced.

## A. The object, made precise

**A1. Sign cocycle.** σ(m,k) := `mulCoeff n m k` (transcribed literally from `proofs/QBP/Foundations/CDAlg.lean` §3; recursion `(a,b)(c,d) = (ac − d̄b, da + bc̄)`). Verified against `flowlib.mul` on all 64 (n = 3) and all 256 (n = 4) basis pairs: max |e_m e_k − σ(m,k) e_{m⊕k}| = **0.0** (exact). Properties: σ(m,0) = σ(0,m) = 1; σ(m,m) = −1 (m ≠ 0); σ(m,k) = −σ(k,m) for distinct imaginary m, k. Table at n = 4 in `sigma_n4.txt`. (σ is *not* a group 2-cocycle — that is the failure of associativity — which is why the CD algebra is a twisted group algebra of (ℤ/2)ⁿ only in the loose "graded" sense; the grading itself is what matters below.)

**A2. Characters are exactly the sign-flip automorphisms.** e_m ↦ ε(m)e_m is an automorphism iff ε(m)ε(k)σ(m,k) = σ(m,k)ε(m⊕k) for all m, k, i.e. iff ε is a homomorphism G_n → {±1} — a character. σ cancels identically, so *every* character of the index group is an automorphism at every level and no other sign function is. Checked: n = 3, all 8 characters pass (product residual 0), exhaustive over the 128 sign functions with ε(0) = 1 gives exactly 8; n = 4, all 16 pass, 1000 random non-characters all fail. Hence Ĝ_n ↪ Aut(CD_n) and the profinite Ĝ = lim← Ĝ_n = ∏ ℤ/2 acts by automorphisms on the direct-limit algebra 𝔸_∞ = ⋃_n CD_n, faithfully there.

**A3. Ĝ₄ inside G₂ × S₃.** Characters with χ(8) = +1 (v ∈ {0,…,7}) fix ℓ = e₈, hence lie in G₂ (within the DIAGONAL / grading-preserving automorphisms, those fixing ℓ restrict to the sign-flip subgroup of Aut(𝕆); this is NOT true of all ℓ-fixing automorphisms — `CrystalHosting.rotAut3` fixes ℓ and moves 𝕆, per the P2 audit — but Ĝ₃ ⊂ G₂ holds): this is Ĝ₃ = (ℤ/2)³, the classical elementary-abelian diagonal subgroup of G₂ (normaliser 2³:GL(3,2), order 1344 — the monomial Fano automorphisms). χ₈ (v = 8) acts as (a, b₀, c) ↦ (a, −b₀, −c): in the (M, s) parametrisation of `aut_s3.py` this is M = diag(1, −1), s = −1 — one of Prop 14's three reflections (axis θ ∈ {0°, 90°}). No other χ_v has S₃-shape (M ⊗ I₇). So **Ĝ₄ = Ĝ₃ × ⟨r₀⟩, Ĝ₄ ∩ G₂ = Ĝ₃, Ĝ₄ ∩ S₃ = {1, r₀}**. Ĝ₄ is not normal-anything in Aut(𝕊); its Aut-conjugates are the sign-flip groups of the other CD bases.

**A4. The 84 and the 42.** Enumerating rank(L_x) over the 210 normalised basis sums (e_i ± e_j)/√2, i < j imaginary: **84 ZDs** (kernel dimension 4 each), on **42 planes** {i, j} = the 7 × 6 grid i ∈ 1..7, j ∈ 9..15, j ≠ i + 8 (PROOF-42zd / Moreno, reproduced). Ĝ₄ acts on the 84 by χ·(e_i + s e_j) = χ(i)(e_i + s·χ(i)χ(j) e_j): the orbits (mod ±) have size 2 and there are **exactly 42** — the planes are the Ĝ₄-quotient of the ZD points. The remaining 126 basis sums are all vacua (V = 0 to machine precision).

## B. What Haar pushes forward to

**B0. On the algebra.** (1/16)Σ_v χ_v·x = (x₀, 0, …, 0): the Haar average over Ĝ₄ is the projection onto ℝ·1 (max deviation 9·10⁻¹⁶). Equivalently the Fourier transform of Haar, m ↦ (1/16)Σ_v χ_v(m), is δ_{m,0}. So the dual Cantor group's Haar "selects" the real unit — the ground field that was doubled — and on the state sphere (x₀ = 0) it averages every orbit to **0**. Any pushforward of Haar to S¹⁴ needs a base point x₀ (a chart): the orbit of ℓ gives ½(δ₊ℓ + δ₋ℓ) — the **struck Prop 11** measure, now seen as "Haar on Ĝ₄ through the base point ℓ"; the orbit of any generic x₀ gives 16 atoms at ±-sign images of x₀. Nothing continuum-valued.

**B1. (i) Basis vectors → the cone points of S²(2,2,3).** Counting measure on the 15 imaginary indices (Haar on the *finite* index group G₄, conditioned off the real unit) pushes to the orbit space as three atoms:

| Indices | (|a|, |Im b|, b₀) | θ | Point of S²(2,2,3) (Prop 15) | Weight |
|---|---|---|---|---|
| 1..7 (Im𝕆) | (1, 0, 0) | 0° | order-2 cone point {0°, 60°, 120°} | 7/15 |
| 9..15 (Im𝕆·ℓ) | (0, 1, 0) | 90° | order-2 cone point {30°, 90°, 150°} | 7/15 |
| 8 (ℓ) | (0, 0, ±1) | — | order-3 cone point (±ℓ) | 1/15 |

This is the **branch locus of Prop 15 weighted by the dimensions of the Cayley–Dickson grading pieces** of Im𝕊 = 7_a ⊕ 1 ⊕ 7_c (NOT the G₂-isotypic decomposition, which is 14 ⊕ 1; 7_a and 7_c are both copies of the 7). It is chart-free once pushed to S¹⁴/Aut (any Aut-conjugate CD basis pushes to the same atoms), but on S¹⁴ itself it is basis-dependent (Prop 14: "the 84 planes are a basis artifact" — so is this). **⟨b₀²⟩ = 1/15 = 0.0667.** V = 0 and the rule field F = 0 on all 15 atoms: the measure is a fixed point of the quench and of e^{−βV} for every β, so quench and anneal both return 1/15; the ℓ-axis map (s + ℓ)/‖s + ℓ‖ sends 14 of the 15 atoms to ℓ and fixes e₈ (−e₈ is excluded: −e₈ + e₈ = 0) → ⟨b₀²⟩ → 1.

**B2. (ii) The ZD planes → one point, off the vacuum S².** All 84 normalised basis-sum ZDs have (|a|, |Im b|, b₀, ⟨a,Im b⟩) = (1/√2, 1/√2, 0, 0), V = **1**: the single G₂-orbit "ZD ridge" of Prop 14 (dim 11, the maximum of V). The uniform measure on the 42 planes pushes to a **delta at the ridge**, not to any measure on the vacuum S² — uniform or otherwise. Each plane's unit circle e_i cos φ + e_j sin φ runs along the b₀ = 0, ⟨a,Im b⟩ = 0 arc of the orbit space from the a-vacuum (φ = 0°, θ = 0°) over the ridge (φ = 45°, V = 1) to the c-vacuum (φ = 90°, θ = 90°), V = sin² 2φ. A plane's *intrinsic* vacuum content is therefore the two order-2 cone points, weight ½ each, ⟨b₀²⟩ = **0**. Any map plane → vacuum other than that is the rule: a 10⁻³ kick + quench from the 84 ridge points lands on the b₀ = 0 equator at θ spread over [0.9°, 89.4°] (kick-dependent; ⟨b₀²⟩ = 0.0007) — rule- *and* noise-dependent, i.e. circular, as expected.

**B3. (iii) Numbers.**

| Index-native discrete measure | Support in orbit space | ⟨b₀²⟩ |
|---|---|---|
| uniform on the 15 imaginary basis vectors | 3 cone points, weights (7,7,1)/15 | **1/15** = 0.0667 |
| uniform on the 84 basis-sum ZDs (= 42 planes) | ZD ridge, V = 1 (not a vacuum) | 0 |
| uniform on the 126 basis-sum vacua | 5 atoms: 42 @ (θ=0, b₀=0), 42 @ (θ=90, b₀=0), 14 @ (θ=0, |b₀|=1/√2), 14 @ (θ=90, |b₀|=1/√2), 14 @ (θ=45°, b₀=0, a ∥ Im b) — the last is **not** a cone point | **1/9** = 0.1111 |
| uniform on all 210 basis sums | above two combined | 1/15 |
| uniform on all 2¹⁵−1 index subsets (any signs) | many atoms | 1/15 |
| *for comparison:* N-measure initial (β = 0) | continuum | 1/15 (0.067 in Prop 9) |
| *rule endpoints:* quench / anneal / ℓ-map from N | continuum | 0.146 / ≈1/3 / 1 |

None of the index-native numbers is a rule endpoint. 1/15 is the isotropic second moment — forced by index-permutation symmetry, hence identical to the N-measure's β = 0 value (E[b₀²] under the uniform measure on S¹⁴ is 1/15 because the 15 imaginary coordinates are exchangeable and sum to 1) and carrying no information the norm did not already carry. 1/9 is a fourth number, but it depends on the combinatorial level (pairs, with ZD pairs deleted) and nothing in the algebra selects "pairs". **Not a striking match; a family of level-dependent rationals.**

## C. The Cantor-set connection

The ledger's first link (`INSIGHT-locale-condensed-chain`) was computed on 2^ℕ; Prop 1 (Lean) is its reviewable form; Prop 8 objected that any algebra-native locale built from ℝ + doubling is circular; Prop 10′ that any *other* profinite tower needs a chart. Ĝ = ∏_ℕ ℤ/2 **is** 2^ℕ as a space, and here it has an algebra-native meaning that is *not* circular in Prop 8's sense: it is the dual of the tower's indexing, and it is the tower's **Galois group** — the CD doubling is a ℤ/2-extension tower (adjoin ℓ with ℓ² = −1, non-commutative and eventually non-associative), each level is the fixed subalgebra of an open subgroup of Ĝ (verified [C1]: Fix(χ_v : v ⊥ G_k) = CD_k for k = 0..4), and averaging over the Galois group is the projection to the ground field ℝ·1 [B0]. This is a genuine and, as far as the #473 record goes, unrecorded structural reading of the tower: the "Galois tower" Round-8 Line 2 looked for does exist — as a tower of *algebras*, not of covers of the vacuum S².

But it answers Prop 8's objection by making the profinite object **inert** rather than circular. Three independent reasons, in increasing strength:

1. On any finite level CD_n the action of Ĝ factors through the finite Ĝ_n (order 2ⁿ) [C2]: the levels above n act trivially. Nothing profinite reaches 𝕊.
2. The fixed points of the whole group are ℝ·1: forcing "ℝ" from the Galois group returns exactly the ℝ that was the input of the doubling — Prop 8's circularity in its most literal form, and the *only* real number the Cantor group forces.
3. **Theorem (no small subgroups).** Aut(𝕊) is a closed (polynomial-equation) subgroup of GL(16, ℝ), hence a Lie group (Cartan's closed-subgroup theorem), and compact because it preserves the norm N; the identification Aut(𝕊) = G₂ × S₃ (Brown 1967) is NOT formalised on record (Hosting.lean §11) and is not needed here. A profinite group has a neighbourhood basis of the identity by open normal subgroups; a Lie group has no small subgroups; so any continuous homomorphism from a profinite group into Aut(𝕊) has open kernel and finite image. So *no* profinite group — this one or any other candidate, Galois or not — can act non-trivially "in the limit" on a finite-dimensional algebra or on its state sphere by automorphisms. A non-continuous action (using choice) carries no measurable pushforward of Haar. This strictly strengthens Prop 10′: the obstruction is not that the algebra supplies too few covers, it is that profinite ⇒ finite on 𝕊.

The dyadic chart 2^ℕ ↠ [0,1] of Prop 10′ remains the *only* way to make 2^ℕ touch a continuum, and the tower's own Ĝ provides no such map: its only maps into 𝕊 are the orbit maps χ ↦ χ·x₀ with finite image.

## D. Verdict against the sealed position

| Sealed clause | Outcome |
|---|---|
| Haar induces only uniform measure over index-labelled combinatorial objects | **Held**, and sharpened: Haar on Ĝ (dual side) induces the *84 → 42 identification* and the *projection to ℝ·1*; it induces no measure on states at all without a base point. The uniform measures on basis vectors / ZDs / planes come from Haar on the **finite index group G₄**, not from the Cantor group. |
| nothing on the continuum S¹⁴ | **Held** (theorem-grade via NSS): the profinite structure acts through a group of order 16. |
| nothing on the vacuum S² | **Held in substance, amended in form**: the index-counting measure does push a chart-free atomic measure onto the vacuum S² — (7,7,1)/15 on the three cone points of S²(2,2,3). It is a measure on S² other than N's in the letter of Prop 13(a), but (i) it is the branch locus Prop 15 already exhibited, now weighted by isotypic dimensions, (ii) it is basis-dependent on S¹⁴ (canonical only after the Aut-quotient), (iii) its one number is the isotropic 1/15, (iv) sibling measures at other combinatorial levels give other rationals (1/9, 0) and nothing selects a level. Not forced; not ℝ-non-trivial. |
| no ℝ-non-trivial number | **Held.** 1/15 is the trace of the identity divided by 15. |

**What is forced:** Ĝ_n ⊂ Aut(CD_n) at every level (exactly the sign-flip group; Ĝ₃ ⊂ G₂ of order 8; Ĝ₄ = Ĝ₃ × ⟨r₀⟩ of order 16); the Galois correspondence Fix ↔ CD_k; the projection to ℝ·1 as the Haar average; the 42 planes as Ĝ₄\84; the ZD ridge as a single orbit-space point; the (7,7,1)/15 atoms on the cone points; the finite-image theorem for *any* profinite action.

**What is not forced:** any measure on the continuum; any selection among the index-native discrete measures; any rule; any number other than isotropic moments. Prop 12's crux (FORCED vs PERMITTED initial class) is untouched — if anything the attack adds a *discrete* candidate to the PERMITTED class (the basis-atom measure), on which quench and anneal happen to agree (1/15) while the ℓ-map does not (1), so the three-rule ambiguity of Prop 16 survives even there.

**Recommended edits to the target document (not made here — ledger/proofs untouched):** re-word Prop 10′'s last sentence to "the algebra supplies a canonical profinite object — the dual ∏ℤ/2 of its index tower, acting by sign automorphisms and giving the tower its Galois correspondence — and every profinite group acting by continuous automorphisms on a finite-dimensional algebra acts through a finite quotient (Aut is a compact Lie group; no small subgroups), so no profinite structure reaches S¹⁴"; add to Prop 15 that the branch locus carries the algebra's one chart-free discrete measure, the isotypic-dimension weights (7,7,1)/15 with ⟨b₀²⟩ = 1/15; add the Galois-tower reading to §6 "bought". Prop 13(a) stays unmet.

**What a follow-up would need to reverse this:** (1) a *continuous* map from Ĝ (or any profinite object of the tower) to S¹⁴ or the vacuum S² that is not an orbit map — by the NSS theorem this cannot go through Aut, so it would have to be a completion of the direct-limit algebra 𝔸_∞ (an ℓ²- or Cantor-coefficient completion) and that completion *is* a chart; (2) or an algebra-native principle that selects one combinatorial level (basis vectors vs pairs vs subsets) *and* argues that the atomic measure is the initial ensemble — this is Prop 12's crux again, for a discrete candidate; (3) a check not done here: whether every CD grading of 𝕊 is Aut(𝕊)-conjugate to the standard one (true for 𝕆 via transitivity of G₂ on Cayley triples; for 𝕊 the choice of ℓ′ ⟂ 𝕆′ may admit non-conjugate gradings, in which case even the (7,7,1)/15 atoms are grading-dependent).

## Files

- `attack4_dual_cantor.py` — all computations (sections A–C; `run-bounded 2G 300`, ~2 min, < 300 MB).
- `attack4_output.txt` — full run log; `attack4_results.json` — key numbers; `sigma_n4.txt` — the 16×16 sign table σ(m,k) from `mulCoeff 4`.
- `flowlib.py` (copied from the local branch `research/635-analysis-records`, not yet on origin/master) — copied from `research/635-analysis-records:analysis/rule-flow-tests-2026-09-20/flowlib.py` (products, V, rule field).
- Sources read: `docs/foundations/473-ac1-first-link-2026-09-04.md` §1 rows 1, 7′, 8, 9, 10′, 12–16, §2, §6, §7; `proofs/QBP/Foundations/CDAlg.lean` §3 (`mulCoeff`, `conjSign`); `analysis/473-dirac-probe/aut_s3.py` (the (M, s) parametrisation of S₃); `analysis/D2-42-moreno-bijection-2026-06-04.md` (42-B grid definition).


**SCOPE NOTES (Red Team #678, applied):** the Galois correspondence Fix(ker(Ĝ→Ĝ_k)) = CD_k is stated within Ĝ (the sign-flip subgroup), not for Aut as a whole; "σ is not a 2-cocycle" holds for n ≥ 3 (0 failures at n = 2, 168 at n = 3). The no-small-subgroups argument uses only that Aut(𝕊) is a compact Lie group (closed subgroup of GL(16, ℝ) preserving N), not the unformalised identification with G₂ × S₃.
