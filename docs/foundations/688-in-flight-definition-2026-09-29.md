# The in-flight region — definition D: InFlight with its canonical 𝕆_s-leaf foliation (issue #688, 2026-09-29)

**Status:** output document for issue #688 step 5 (parent #473, AC1 (c), ruled 2026-09-30, Option A — §3); branch `foundations/688-inflight-algebra`, Lean head **77a4c60** (PR #689); author qbp-oppenheimer; Tier-3 review owed (Red Team → Gemini → §I4) before anything is encoded. **Nothing is encoded; no #473 acceptance criterion is claimed; no #635 protocol and no Strategy-C branch is chosen; no rule is derived.** Ledger of record: `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json` 6.11.0 on master. Conversation MO followed (sealed position → record pass → rounds 1–5 → two Lean interludes → confirmer). The confirmer report (issue #688, 2026-09-28) is the spine of §§1, 3–5, 9; carried, not re-derived.

## 0. Reading guide

| Tag | Meaning | Cites |
|---|---|---|
| **PROVED** | a 0-sorry Lean 4 theorem, anchored on the master ledger (anchor id) or on this branch (PR #689, head 77a4c60) (a name in `proofs/QBP/Foundations/InFlightAlgebra.lean`: unanchored, unreviewed, encode only after review); the sentence stays inside the NOT-claimed clause | anchor id or Lean name |
| **NUMERICAL** | a scripted computation, not machine-checked | script name (location note below) |
| **ARGUMENT** | a derivation from PROVED / NUMERICAL ingredients, not itself machine-checked (classical theorems, BOTE counts, equivariance readings) | ingredients and step |
| **OPEN** | not settled either way | owning issue or tracker anchor |

Every claim carries exactly one tag; a conversation "ARGUMENT + NUMERICAL" is tagged by the bucket it rests on.

**Numerics.** The five session scripts and the saved `r4_out.txt` are under `analysis/688-in-flight/` (README: what each computes, the number reported, the round served); not re-run.

| Item | State after the conversation |
|---|---|
| Sealed position (issue #688) | "Candidate 2, the locale: the in-flight region is definable as the **open sublocale {V > 0} of Ω(StateSphere)** — the frame-theoretic complement of the vacuum sublocale … **What primitive it yields (AC2). None beyond what the state sphere already has.**" |
| The object | **unmoved**: InFlight = {V > 0} ⊂ S¹⁴ (PROVED) |
| AC2 | **unmoved**: none |
| "complement sublocale" wording | **dropped** — the open sublocale of Ω(S¹⁴) is the frame of opens of a spatial open set: spatial, decorative (round 2 finding 6; record pass P1) |
| The 𝕆_s-leaf foliation | **not in the sealed position**: arrived in round 4 (Red Team finding 2), accepted by Gemini in one turn, pressure-tested by the confirmer |
| §3 Completeness Gate | **met per the confirmer, as of 77a4c60 (rebased 14b8160) + audit — not as declared by the dyad at round 5** (3.3 premature: a Lean theorem cited before it existed; 3.5: foliation and "AC2 = none" untested) |

The sealed "NUMERICAL: nothing new expected" was wrong: the kernel-algebra numerics drove the Lean work.

## 1. The definition D, in one construction

> **D.** The in-flight region is **InFlight = {V > 0} ⊂ S¹⁴** — equivalently {s : ker Δ(s) ⊊ 𝕊}, Δ(s) = L_s² + N(s)·id = −[s, s, ·] the left alternator — **together with its canonical (§1, K-a) foliation by the 6-dimensional leaves S⁶(𝕆_s) ∩ InFlight**, where 𝕆_s = CD(H_s), H_s = span{1, a, Im b, a·Im b} ⊂ 𝕆 (s = a + bℓ) an associative quaternion algebra; leaf space {ℍ ⊂ 𝕆} = G₂/SO(4); the leaves are invariant under every deterministic G₂-equivariant rule (the anneal: in law only); rule-blind within that class; spatial.

Notation: 𝕊 = `CDAlg ℝ 4`, 𝕆 = `CDAlg ℝ 3`, a = `cdLo s`, b = `cdHi s`, c = Im b = `imHi s`; ℍ_s = span{1, s, ℓ, sℓ}.

| Clause of D | Tag | Source |
|---|---|---|
| InFlight = {V > 0} = {ker Δ(s) ⊊ 𝕊} as sets | **PROVED** | `mem_inFlight_iff_potential`, `isVacuum_iff_alternator_flat`, `delta_eq_neg_assoc`; PROOF-substrate-hosting-definition, PROOF-alternator-vanishes-iff-commute |
| Δ(s) = −T_s on imaginary s; Δ blind to b₀ (L_s² alone is not) | **PROVED** | `left_mul_sq_imaginary`; `delta_blind_to_ell`, `assoc_self_add_smul_ell`, `left_mul_sq_ell_shift` (branch) |
| ℍ_s closed under the product and associative at every imaginary s; 4-dimensional for unit imaginary s iff s ≠ ±ℓ (there span{1, ℓ} ≅ ℂ); ℍ_s ⊆ ker Δ(s) | **PROVED** | `inFlight_closed_associative`, `inFlight_independent`, `pOf_eq_zero_iff`, `delta_vanishes_on_inFlightSpan` (branch); the span was first-link Prop 16(ii), `genByPair_ell_mem_quatSpan` |
| Associativity of ℍ_s is not alternativity restated: it holds at s = e₁ + e₁₀ where 𝕊's alternator at s is nonzero | **PROVED** | `inFlight_associative_even_where_alternator_nonzero`, via `sedWitX_alternator_ne_zero` |
| H_s ⊂ 𝕆 closed under product and conjugation, associative — a quaternion algebra (degenerate at a vacuum); 𝕆_s = H_s ⊕ H_s ℓ closed under +, • | **PROVED** | `inQuatSpanOct_mul`, `inQuatSpanOct_conj`, `inQuatSpanOct_assoc`, `inKernelAlgebra_add`, `inKernelAlgebra_smul` (branch), on `span4_mul_closed`, `assoc_vanishes_on_span4`, `octonion_artin` |
| ∇V(s) ∈ 𝕆_s for every s (no imaginarity or unit norm); s ∈ 𝕆_s; hence α·s + β·∇V(s) ∈ 𝕆_s | **PROVED** (modulo the next row) | `gradV_mem_kernelAlgebra`, `gradVof_mem_kernelAlgebra`, `self_mem_kernelAlgebra`, `smul_self_add_smul_gradV_mem_kernelAlgebra` (branch) |
| `gradVof` (Foundations copy of the closed form) = `RuleFlow.gradV` | **OPEN** | text-identical to `cdLo_gradV` / `cdHi_gradV`, matched by citation only; bridge lemma on #683 |
| The rule field F(s) = −(∇V − ⟪∇V, s⟫s − (∇V)₀·1) lies in 𝕆_s | **ARGUMENT** | the row above plus 1 ∈ 𝕆_s; not a stated theorem; F's form: PROOF-rule-gradient-and-tangent-field |
| ker Δ(s) has rank 8 on 200 random states + the ridge witness (e₁+e₁₀)/√2, and equals 𝕆_s (reverse inclusion) | **NUMERICAL** | 200 states, `analysis/688-in-flight/delta_spectrum_check.py`; rank[Fix, ker] = 8, 3 trials, `r4_out.txt` |
| The P2 rule is G₂-equivariant | **ARGUMENT** | ingredients PROVED: `map_N`, `map_re`, `map_one`; no Lean `ruleField (φ s) = φ (ruleField s)`; F(s) ∈ 𝕆_s to 1.4·10⁻¹⁵, 200 states (`confirm_leaf.py`) |
| Leaf invariance: a deterministic G₂-equivariant integral curve starting in S⁶(𝕆_s) stays there | **ARGUMENT** | two routes (§2); P2 trajectories stay in ker Δ(s₀) to 2.2·10⁻¹⁵ (`r4_out.txt`); conditional on FLAG-rule-flow-open |
| Leaf space = {quaternion ℍ ⊂ 𝕆} = G₂/SO(4), dimension 8 | **ARGUMENT** | G₂ transitive on orthonormal 2-frames in Im 𝕆 (first-link Prop 5); stabiliser of ℍ is SO(4) (INSIGHT-octonion-quaternion-branching); 14 − 6 = 8 (PR #553 §5.2), already on record as 8-dim, nonzero, kinematic moduli (PROOF-level-set-invariants-rule-blind). "H_s ⊂ 𝕆" uses the CD chart; 𝕆_s ⊂ 𝕊 is S₃-invariant, so S₃ acts trivially on leaves (tag: next row) |
| Leaves partition InFlight: s′ ∈ S⁶(𝕆_s) ∩ InFlight ⇒ 𝕆_{s′} = 𝕆_s | **ARGUMENT** | H_{s′} ⊆ H_s, dim 4 for in-flight s′ on the leaf (non-parallel a′, c′); `InQuatSpanOct`'s 4-dimensionality not itself in Lean ("at most 4-dimensional") |
| 𝕆_s chart-independent / S₃-invariant, via the only chart-free candidate ker Δ(s) | **NUMERICAL**; reverse **OPEN** | rank 8, `delta_spectrum_check.py`; reverse inclusion is K-a's target (§5) |
| 8 + 6 = 14; each leaf closure meets the 8-dim vacuum manifold in a 4-dim set; leaves through a crystal form a ℂP² (4 + 4 = 8) | **ARGUMENT** (BOTE) | confirmer §2; PROOF-vacuum-parametrisation |
| Rule-blind within the deterministic equivariant class; spatial, no pointless content | **ARGUMENT** | §3 N2; INSIGHT-locale-condensed-chain |

## 2. What D adds over the bare open set, and what it does not

| Adds | Tag | Does not add | Tag |
|---|---|---|---|
| A 14-dim flow on InFlight becomes a family of 6-dim flows, one per leaf, the 𝕆-problem one CD rung down (a, b ∈ H ≅ ℍ, V = ‖[a, b]‖²_H) | **ARGUMENT** | Rule content: leaves are identical for every deterministic G₂-equivariant rule; a preferred frame *would* break them — "rule-blind" is class-relative | **ARGUMENT** |
| Eight kinematic conservation laws (constancy of 𝕆_s along a trajectory), from the algebra, not from dV | **ARGUMENT** | Prop 13(b) contact: nothing in D selects quench vs anneal or supplies a per-level-set measure or transport (FLAG-locale-forcing-route-reopened open) | **ARGUMENT** |
| A converging trajectory's target axis u_end lies in S² ⊂ Im H_s — by symmetry, no endpoint map needed | **ARGUMENT** | The endpoint itself: no ω-limit map, no existence | **OPEN** (FLAG-rule-flow-open) |
| Hosting sharpened: at every in-flight s, s(sx) = −N(s)x holds on ℍ_s | **PROVED** (`left_mul_sq_on_inFlightSpan`) | Locale content: the foliation partitions a spatial open set into embedded 6-spheres minus vacuum points | **ARGUMENT** |

**Two routes to leaf invariance (ARGUMENT, confirmer §3).** *Group route:* for a G-equivariant locally Lipschitz field with flow φ_t, K ≤ G, x₀ ∈ Fix(K), k ∈ K, the curve k·φ_t(x₀) is an integral curve through x₀, so by uniqueness Fix(K) is invariant; Fix(Stab_{G₂}(s)) ∩ 𝕊 = 𝕆_s is NUMERICAL (3 trials). *Group-free route:* F(s) ∈ 𝕆_s pointwise (PROVED, up to the `gradV = gradVof` citation) and S⁶(𝕆_s) is a compact embedded sphere, so uniqueness confines the curve — the P2 rule only. Both use uniqueness of integral curves, on record only backwards (PROOF-rule-flow-finite-time-uniqueness); existence is FLAG-rule-flow-open. *Scope:* the Gibbs anneal (#635 B) is a diffusion — a 10⁻³ kick leaves the leaf by 3·10⁻³ (NUMERICAL, `confirm_leaf.py`); invariance holds in law, not per path. Protocol C, (s + ℓ)/‖s + ℓ‖, preserves leaves since ℓ ∈ 𝕆_s.

## 3. AC1 — consistency with the five negatives

| Anchor (Tier 1, 0 sorry) | Contact | Reason | Tag |
|---|---|---|---|
| N1 PROOF-in-flight-first-order-data-constrains-at-most-one-direction | contact, consistent | D confines F(s) to the 6-dim leaf tangent (8 constraints) from the algebra, not from dV; the anchor counts dV's constraints (≤ 1): 1 ≤ 6 ≤ 14. On the frozen ridge F = 0, the anchor counts 14, the leaves still exist (rank 8, NUMERICAL) | **ARGUMENT** |
| N2 PROOF-level-set-invariants-rule-blind | consistent; contact by extension | D is not a functional of level-set topology (a leaf crosses every level 0 < V ≤ 1), so the anchor's inference clause does not cover it; D is rule-blind by equivariance, only within the deterministic class. No Prop 13(b) contact, as the NOT-claimed clause requires; wording: "identical for every deterministic G₂-equivariant rule" | **ARGUMENT** |
| N3 PROOF-hosting-identity-fails-in-flight | contact, sharpens | The identity fails globally (the anchor) yet holds on ℍ_s — filling the anchor's NOT-claimed clause ("a 4-dim subalgebra could in principle exist without s acting as a complex structure on all of 𝕊") with a theorem: it does, at every imaginary s off ±ℓ | **PROVED** (`inFlight_closed_associative`, `left_mul_sq_on_inFlightSpan`) |
| N4 PROOF-vacuum-sublocale-v-natural | consistent, vacuous | D's open set is the complement of the vacuum support; the foliation adds no locale content, measure, transport or clock | **ARGUMENT** |
| N5 PROOF-sublevel-infimum-rule-independent | consistent, vacuous | leafwise inf V = 0 (a ∥ c reachable inside Im H_s on every leaf); the sublevel filtration is unchanged | **ARGUMENT** |

**Honest statement on AC1 (c).** D is *spatial*. By the 2026-09-30 ruling (Option A, beekeeper, issue #688, reflected in #473) **D's spatial character is no longer an AC1 (c) deficit**; the pointless demand is carried by the CONJ-condensed-math-for-transition-state record, OPEN, not as an AC of #473. **AC5 guard:** cite the ruling only — do not claim (c) is met; D still hosts no transport or measure, and (c)'s satisfaction is #473's call, not this doc's. Against #688's AC1, D is a construction, consistent with all five negatives, contact on N1 and N3.

## 4. AC2 — which primitive D yields

| Candidate | What W1 (PR #553 §5.1) needs | What D supplies | Verdict | Tag |
|---|---|---|---|---|
| A leaf S⁶(𝕆_s) ∩ InFlight | a 3-dim base of *locations*, configurations as sections | 6-dim; each point a whole state, not a place; metric N restricted | fails all three | **ARGUMENT** |
| The leaf space G₂/SO(4) | a measure not N relabelled (first-link Prop 8, relocation test) | 8-dim; points are seeds ℍ ⊂ 𝕆; its unique G₂-invariant probability measure is the pushforward of N's surface measure under s ↦ 𝕆_s — N relabelled | fails | **ARGUMENT** |
| The kernel bundle s ↦ ker Δ(s) | a geometric datum the frame of opens lacks | a rank-8 subalgebra bundle: algebraic, not spatial | not spatial | **ARGUMENT** |

**AC2 = NONE (spatial)**, as sealed and as #688 allows. **Addendum (ARGUMENT):** D yields one *non-spatial* primitive — a canonical 8-dimensional moduli space of quaternion seeds with an N-derived measure. Not W1's ∫d³x: wrong dimension, points are algebras not locations, measure is N's. Neither touches "points not yet available". For PR #553 §5.1 the fundamental branch is not unblocked; the fork stands.

## 5. AC3 — kills, in positive-measure form

| Kill | Form | Fires on | Testable | Tag |
|---|---|---|---|---|
| **K-a** (algebraic) | a positive-measure set of in-flight states with ker Δ(s) ⊋ 𝕆_s (rank > 8) | **canonicity only** — 𝕆_s = ker Δ(s) and S₃-triviality (§1); leaf *invariance* (∇V(s) ∈ CD(H_s)) holds regardless of ker Δ(s), so K-a cannot touch it, only "canonical" | **now**, by computation or the reverse-inclusion Lean target; 200 states show rank 8 (`delta_spectrum_check.py`) | **NUMERICAL** (not fired; reverse inclusion OPEN) |
| **K-b** (scope) | #635 rules the anneal (protocol B) the rule | "flow-invariant" fails on every path; D restated in law | when #635 rules | **OPEN** (#635) |
| Gemini's S4 (round 5) | a positive-measure K where the rule's second-order data (Hessian / divergence) depends on transverse coordinates | nothing: leaf invariance is first-order (P⊥F = 0 on a leaf ⇒ P⊥·DF·P = 0) while P⊥·DF·P⊥ is unconstrained and large (9.1 vs 4·10⁻¹⁰, `confirm_leaf.py`) — S4 fires at essentially every state and kills nothing; the version that would kill, P⊥F ≠ 0 on positive measure, is ∇V ∉ 𝕆_s, excluded by theorem at 77a4c60. A kill that cannot fire is not a kill (2026-09-25 lesson); the scalar-Hessian appeal conflates the normal space to the vacuum manifold with that to a leaf | **not a kill** | **ARGUMENT** |

**No dynamical kill inside the class (ARGUMENT).** D's only dynamical falsifier is a symmetry-breaking or stochastic term, which changes the class, not D — N2's rule-blindness in another form, and why D makes no Prop 13(b) contact. Round 2's static kill (vary b₀² on a level set) killed the *Δ-decorated* definition's added content, not D: those states lie on different leaves.

## 6. What was proved in Lean (branch `foundations/688-inflight-algebra`, head 77a4c60, PR #689)

`proofs/QBP/Foundations/InFlightAlgebra.lean` (Foundations layer, no Substrate import). By grep: 68 `theorem`s + 10 `def`s (78 declarations); 39 audited via `#print axioms` (29 un-audited helper lemmas). 0 `sorry`, 0 `native_decide`, axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}; `lake build` exit 0; both gates exit 0. **Not re-run here.** Every row is **PROVED** on the branch.

| Lean name(s) | One-line statement |
|---|---|
| `Delta`, `delta_eq_neg_assoc` | Δ(s)x := s(sx) + N(s)x; for imaginary s, Δ(s)x = −[s, s, x] |
| `assoc_self_add_smul_ell`, `delta_blind_to_ell`, `left_mul_sq_ell_shift` | [s + tℓ, s + tℓ, ·] = [s, s, ·]; Δ(s + tℓ) = Δ(s); L_s² alone shifts by (N s − N(s + tℓ))·id |
| `mul_ell_add_ell_mul`, `ell_mul_eq` | sℓ + ℓs = −2b₀·1; s, ℓ anticommute iff b₀ = 0 |
| `pOf`, `pOf_eq_zero_iff`, `inFlightSpan_iff_quatSpan` | p := s − b₀ℓ; for unit imaginary s, p = 0 iff s = ±ℓ; ℍ_s = span{1, ℓ, p, ℓp} |
| `inFlightSpan_mul_closed`, `quatSpan_mul_expand`, `quatSpan_assoc`, `inFlightSpan_assoc`, `inFlight_closed_associative` | the span is closed under the product (explicit quaternion table) and associative, for every imaginary s |
| `inFlight_associative_even_where_alternator_nonzero` | at s = e₁ + e₁₀ the alternator at s is nonzero and the span is still associative |
| `quatSpan_independent`, `inFlight_independent` | {1, ℓ, p, ℓp} independent for nonzero imaginary p ⊥ ℓ (generalises `crystal_quatSpan_independent`); {1, s, ℓ, sℓ} independent iff p ≠ 0 |
| `delta_vanishes_on_inFlightSpan`, `left_mul_sq_on_inFlightSpan`; `one_mem_ker_delta`, `s_mem_ker_delta`, `ell_mem_ker_delta`, `s_mul_ell_mem_ker_delta`; `assoc_self_one`, `assoc_self_self`, `assoc_self_ell` | ℍ_s ⊆ ker Δ(s); s(sx) = −N(s)x on ℍ_s; the four kernel witnesses in Δ and alternator form |
| `InQuatSpanOct`, `inQuatSpanOct_mul`, `inQuatSpanOct_conj`, `inQuatSpanOct_assoc` | H = span{1, a, c, ac} ⊂ 𝕆 closed under product and conjugation, associative |
| `imHi`, `cdHi_mem_hostQuat`, `cdComm`, `cdComm_eq_comm_imHi`, `cdComm_mem_hostQuat` | c := Im b; b ∈ H_s; [a, b] = [a, c] ∈ H_s |
| `gradVlo`, `gradVhi`, `gradVof`, `gradVlo_mem_hostQuat`, `gradVhi_mem_hostQuat` | Foundations copies of the closed-form CD components of ∇V; both in H_s |
| `InKernelAlgebra`, `gradV_mem_kernelAlgebra`, `gradVof_mem_kernelAlgebra`, `self_mem_kernelAlgebra`, `inKernelAlgebra_add`, `inKernelAlgebra_smul`, `smul_self_add_smul_gradV_mem_kernelAlgebra` | x ∈ 𝕆_s iff both CD components in H_s; ∇V(s), s ∈ 𝕆_s; closed under +, •; α·s + β·∇V(s) ∈ 𝕆_s |

| Not proved on the branch | Tag | Where it would live |
|---|---|---|
| Reverse inclusion ker Δ(s) ⊆ 𝕆_s (the *full* kernel) | **OPEN** | Foundations; needs H ⊕ H^⊥ |
| Bridge `gradVlo s = cdLo (gradV s)`, `gradVhi s = cdHi (gradV s)` | **OPEN** | Substrate/RuleFlow (#683) |
| Flow invariance as an ODE statement | **OPEN** | Substrate; conditional on a given curve, like `stateSphere_invariant` |
| `ruleField (φ s) = φ (ruleField s)` for φ ∈ CDAut | **OPEN** | Substrate/RuleFlow |
| T2b: Δ³ = VΔ, ‖Δ‖_op = √V, spectrum {0⁸, ±√V⁴} | **OPEN** (NUMERICAL to 3·10⁻¹⁶) | Foundations/Alternator ("flashlight-only" gap) |

## 7. The conversation record

| Turn | Seat | Advanced | Fell |
|---|---|---|---|
| Sealed position + record pass | qbp-oppenheimer; sub-agent | candidate 2 (open sublocale {V > 0}); AC2 none; pressures P1–P4 (P1: an open sublocale is spatial) | — |
| Round 1 | Gemini (Furey/Feynman) | Δ(s) as a "defect section"; a static kill against the bare sublocale; AC2 none; W1 (bundles live over `Top`), W2 (Δ kinematic) | "P1 is a category error" |
| Round 2 | Red Team (Sabine/Grothendieck/Knuth) | Δ = −T_s (PROVED, PR #629); Δ's invariant content is V alone (NUMERICAL); Gemini's kill, made gauge-invariant, fires on (𝓘, Δ); **finding 8 (confirmer's numbering; round 2 called it a "bonus finding"): ker Δ(s) = CD(H_s), ℍ_s associative in flight** (NUMERICAL); the `inFlight_no_quaternion_closure` over-read | "Δ is new"; "Δ distinguishes states on a level set"; P1 as category error; W1 |
| Round 3 | Gemini | conceded locale-theoretic pointlessness; retracted "non-associativity tears the quaternions apart"; set {s : ker Δ(s) ⊊ 𝕊}; Stab_{G₂}(crystal) = SU(3), five relative invariants — **the genuine pushback** | — |
| Interlude 1 (Lean, e9037da → rebased ddd289b) | lean-prover | F2 PROVED; F3 PROVED **with the correction** 4-dim for unit imaginary s iff s ≠ ±ℓ; F4 partial | "sℓ ≠ −ℓs" (a b₀ ≠ 0 sample) |
| Round 4 | Red Team | set identity (PROVED); **finding 2: the kernel bundle is a first integral; InFlight foliated by invariant 6-dim leaves, leaf space G₂/SO(4)**; Lean targets re-ranked; AC1 (c) Options A/B | "{ker Δ ⊊ 𝕊} is new"; blow-up as Prop 13(b) contact (identity fibration to O(ε²)); "relative to a fixed crystal" as definition (circular: the target is the ω-limit) |
| Round 5 | Gemini | accepted finding 2 via the pointwise Fix argument; stated D; AC2 none; declared the gate passed; **declared weakness: D is rule-blind** | A2; S4 as a kill; "deterministic" dropped; a Lean theorem cited before it existed |
| Interlude 2 (Lean, 14b8160 → rebased 77a4c60) | lean-prover | ∇V(s), α·s + β·∇V ∈ 𝕆_s PROVED | — |
| Confirmer | Red Team | gate MET as of 14b8160 (rebased 77a4c60) + audit; the seven corrections below | the dyad's declaration (3.3 premature, 3.5 unmet) |

**Sycophancy and over-reach, both sides (confirmer §8).** *Gemini:* round 5 mirrors round 4 — S2 is finding 2 restated as the definition; S5(4) "restates the Red Team's position and is satisfied"; blow-up and relative kinematics conceded without engaging the numerics; S5(1) cited `gradVof_mem_kernelAlgebra` at e9037da, where it did not exist. Genuine: the pointwise Fix argument, the declared weakness. *Red Team:* (i) "identical for every G₂-equivariant rule" rested on 3 numerical trials, stated as settled; (ii) finding 8 presented as new when the span was Prop 16(ii) (new content: associativity + independence); (iii) "identity fibration" extrapolated from three directions at one crystal; (iv) "sℓ ≠ −ℓs" was a sample. Precedent: `473-ac1-first-link` §3b.

**Corrections carried:** (1) "flow-invariant" scoped to deterministic rules, anneal in law; (2) A2 dropped; (3) S4 → K-a, K-b; (4) `gradV = gradVof` a citation; (5) finding 8 = Prop 16(ii); (6) "complement sublocale" dropped; (7) foliation dated to round 4.

## 8. Consequences and follow-ups

| Target | Consequence | Tag | Owner |
|---|---|---|---|
| **#473 AC1 (c)** | **Ruled: Option A**, 2026-09-30, issue #688 comment, reflected in #473 (§3, AC5 guard). Option B's content lives on as the CONJ record | **—** | beekeeper |
| **PR #553 §5.1** (W1) | AC2 = none: the fork stands | **ARGUMENT** | qbp-oppenheimer |
| **PR #553 §5.2–§5.3** | The leaf space of D *is* the §5.2 coset G₂/SO(4) (moduli already on record as kinematic, §1). §5.3 leaves OPEN whether that coset is the crystal moduli; D gives a candidate relation — leaf closures meet the 8-dim vacuum manifold in 4-dim sets, the leaves through a crystal form a ℂP², 4 + 4 = 8. A BOTE count, not an identification; §5.3 stays OPEN | **ARGUMENT** | #553; #551 |
| **`Substrate/Hosting.lean`** l.57, `inFlight_no_quaternion_closure` | Docstring ("makes 'not yet crystallised' a theorem") and name over-read a statement saying only L_s² ≠ −N(s)·id globally; the anchor's NOT-claimed clause is right. Fix: reword; rename (e.g. `inFlight_no_global_scalar_spectrum`) with the old name as alias, or docstring-only | housekeeping | **#683** (filed) |
| **Lean follow-ups** | (a) bridge lemma; (b) reverse inclusion; (c) flow-invariance ODE statement; (d) `ruleField` equivariance; (e) T2b; (f) `lake build QBP.Foundations` OOM at `Octonion32Count` under the 6 GB cap | **OPEN** | lean-prover; #683 |
| **Substrate draft v0.2** (#684) | §4 "Positive in-flight account" and §8: "no issue" → #688, D as candidate | **OPEN** | #684 |

**Encode plan — would-be PROOF anchors after review (ENCODE NOTHING NOW; slugs, not ids).**

| Candidate slug | Lean theorem(s) | NOT-claimed clause it would carry |
|---|---|---|
| `in-flight-alternator-blind-to-ell` | `assoc_self_add_smul_ell`, `delta_blind_to_ell`, `left_mul_sq_ell_shift` | that L_s² alone is ℓ-blind; anything about Δ's spectrum (T2b) |
| `in-flight-quaternion-closes-and-associates` | `inFlight_closed_associative`, `inFlight_independent`, `pOf_eq_zero_iff`, `inFlight_associative_even_where_alternator_nonzero` | 4-dimensionality at ±ℓ; that ℍ_s is the full kernel; the flow; any reversal of PROOF-hosting-identity-fails-in-flight (whose NOT-claimed clause this fills) |
| `in-flight-span-in-alternator-kernel` | `delta_vanishes_on_inFlightSpan`, `left_mul_sq_on_inFlightSpan`, the `*_mem_ker_delta` four | the reverse inclusion; rank 8 |
| `gradient-lies-in-host-kernel-algebra` | `gradV_mem_kernelAlgebra`, `gradVof_mem_kernelAlgebra`, `smul_self_add_smul_gradV_mem_kernelAlgebra` | that `gradVof` = `RuleFlow.gradV` in Lean; flow invariance (conditional on existence); 𝕆_s = ker Δ(s); leaf space = G₂/SO(4); the anneal; the endpoint |

FLAG/CONJ notes touched, if at all, only via the confined writer in the Tier-3 PR: FLAG-rule-flow-open (leaf invariance conditional on it), CONJ-condensed-math-for-transition-state (D spatial, no bearing). Neither touched here.

## 9. Four-bucket exit, and what would reverse D

| Bucket | Contents |
|---|---|
| **PROVED** | the set identity (master); Δ = −T_s, ℓ-blind; ℍ_s closed, associative, 4-dim for unit imaginary s off ±ℓ, ⊆ ker Δ(s); H_s a conjugation-closed associative subalgebra of 𝕆; ∇V(s), α·s + β·∇V(s) ∈ 𝕆_s (modulo the `gradV = gradVof` citation); scalar transverse Hessian at vacua (PROOF-vacuum-hessian-transverse-eigenvalue) |
| **NUMERICAL** | ker Δ(s) rank 8 and = 𝕆_s; Δ's spectrum {0⁸, ±√V⁴}, Δ³ = VΔ; Δ depends on s only through a ∧ Im b; P2 trajectories stay in 𝕆_{s₀} to 2.2·10⁻¹⁵; the anneal leaves a leaf per path; endpoint drift 0.40ε² at one crystal |
| **ARGUMENT** | P2 rule G₂-equivariance; leaf invariance (two routes); leaves partition InFlight; leaf space = G₂/SO(4); 8 + 6 = 14, 4 + 4 = 8; F(s) ∈ 𝕆_s; class-relative rule-blindness; AC2 = none; S4 cannot fire; D spatial |
| **OPEN** | ker Δ(s) ⊆ 𝕆_s (K-a's target, §5); `gradV = gradVof`; the flow-invariance ODE statement; `ruleField` equivariance in Lean; T2b; uniqueness of 𝕆_s among octonion subalgebras ⊇ ℍ_s; the pointless-locale demand, carried as CONJ-condensed-math-for-transition-state (not AC1 (c), post-ruling — §3); existence and the ω-limit map (FLAG-rule-flow-open); which #635 protocol is the rule (K-b) |

**What would reverse D.** (i) K-a fires: ker Δ(s) strictly larger than 𝕆_s on positive measure — the foliation is by the wrong algebra (the set InFlight is a theorem, irreversible). (ii) K-b: #635 rules the anneal the rule — the invariance clause becomes a statement in law. (iii) A ruling admitting a rule outside the deterministic G₂-equivariant class — the algebraic clauses survive, the invariance clause does not. (iv) A pointless construction answering CONJ-condensed-math-for-transition-state would add to D, not supersede it — AC1 (c) no longer demands one; none on record. Not a reversal: any fact about ⟨b₀²⟩ or quench vs anneal — D is blind to them by construction, and says so.
