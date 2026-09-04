# #473 AC1 — the first link, v0.1 (something to test against)

**Status:** v0.1 proposition ladder, written 2026-09-04 after two Gemini rounds (Furey/Feynman, session `debate-20260904-151140`) with Claude as Red Team. Refs #473 (AC1 first pass; issue stays open). Research thread — **not** foundation. Nothing here authorises a Lean file under `proofs/QBP/Substrate/` (Prop 2).

**AC1 text:** *Formalize the proposed chain's first link (locale-from-condensed for the relevant spatial case) to a reviewable standard — extend beyond the Cantor-set anecdote toward a forcing argument for ℝ.*

**One-line result:** the spatial first link is a two-line corollary of library facts (ℝ included), so the Cantor anecdote was never load-bearing; the *only* place the substrate can pay rent is a **probability measure on the 3-dimensional orbit space S¹⁴/G₂** — and the map from any pointless locale to that space is currently **undefined**. That undefined map is the gate.

---

## 1. Proposition ladder

Status tags: `THEOREM(cited)` classical, citation given · `PROVABLE-NOW` a few lines from existing Lean · `NUMERICAL` checked by committed script this session · `CONJECTURE` · `BLOCKER` · `KILL-TEST` · `POLICY`.

| # | Statement | Status | Evidence / role |
|---|---|---|---|
| **1** | **Spatial first link.** For X compactly generated (in particular compact Hausdorff; in particular ℝ, metrisable ⇒ CG), the locale Ω(X) is determined by the condensed set X̲: Ω(X) ≅ Ω(condensedSetToTopCat X̲). Cond_CG → Top → Loc is faithful on CompHaus and lands in spatial locales. | `PROVABLE-NOW` | Mathlib `fullyFaithfulCompactlyGeneratedToCondensedSet` (counit iso) composed with `topToLocale`; `CompHausToLocale.faithful`. This is the reviewable form of the ledger's Cantor calculation, and ℝ is already an instance. |
| **2** | **Lean policy.** Prop 1 is a type-check composing two library functors. It does **not** open `proofs/QBP/Substrate/`. | `POLICY` | Empty-Substrate rule / #471 lesson; both reviewers and Red Team agree. First Substrate file waits for Prop 10/11. |
| **3** | **Quotient route to ℝ.** [0,1] = C/∼ (Cantor set, binary-tail identification 0111… ∼ 1000…); ℝ = colim [−n,n]. Locale-level: the surjection C ↠ [0,1] is a **frame injection** Ω([0,1]) ↪ Ω(C), i.e. [0,1] is a quotient locale of C. ℝ is the Dedekind completion of the halving ring ℤ[1/2]. | `THEOREM(cited)` | Alexandroff–Hausdorff (every compact metrisable space is a continuous image of C); Johnstone, *Stone Spaces* / *Elephant* C1. Route, not forcing: "which quotient is [0,1]" is answered by the classical uniqueness of ℝ restated. |
| **4** | **Generics are reals.** The generic point a pointless locale acquires internally (ledger Layer 2) is, in both canonical cases, a real number: the Cohen real (Cantor tower = Cohen poset) and the random real (measure algebra Borel/null of [0,1]). | `THEOREM(cited)` | Jech, *Set Theory* ch. 14–15; Johnstone, *Elephant* C1.2 / D4.7. The sharpest sense in which the substrate's mechanism "produces ℝ". Still classical. |
| **5** | **The algebraic gap.** Aut(𝕊) = G₂ × S₃. G₂ acting diagonally on Im𝕊 = Im𝕆 ⊕ 𝕆 (s = a + bℓ) has generic orbit dimension **11**; the orbit space **S¹⁴/G₂ is 3-dimensional**, coordinatised by the invariants (|a|², b₀, ⟨a, Im b⟩) with |a|² + b₀² + |Im b|² = 1. | `NUMERICAL` + provable | `analysis/473-dirac-probe/orbit_space.py` (rank of the 14 derivations at generic points = 11, five samples). Stabiliser chain G₂ ⊃ SU(3): orbit ≅ S⁶ × S⁵. Aut(𝕊) per Brown (1967). |
| **6** | **Descent of the landscape.** V(s) = δ² = ‖[a,b]‖² = **4(|a|²·|Im b|² − ⟨a, Im b⟩²)** — a function of the three invariants only. Hence the #629 gradient flow commutes with G₂ and descends to a flow on the 3-dim orbit space; the endpoint statistic ⟨b₀²⟩ depends only on the pushforward of the initial measure to S¹⁴/G₂. | `NUMERICAL` + `PROVABLE-NOW` | `orbit_space.py` (3): residual 7·10⁻¹⁶ over 2000 Haar samples. Proof: [a,b] = 2 a × Im b and the octonion identity ‖a × c‖² = ‖a‖²‖c‖² − ⟨a,c⟩² for a, c ∈ Im𝕆 — provable in QBP's `CDAlg` (not Mathlib, which has no octonions). Picture: `hvr_orbit_space.png`. |
| **7** | **Haar is an assumption.** The O(15)-Haar measure on S¹⁴ used in #629 §8 is not forced by ℝ + doubling: the algebra's symmetry leaves a free measure on a 3-dimensional space (Prop 5); Haar is one point in that family. | `THEOREM` (from 5) | Defines the boundary of the current bedrock precisely. **The AC2 residual is: a probability measure on a 3-dim orbifold.** |
| **8** | **Algebra-native poset.** The pointless locale relevant to the first link must be native to the algebra — not the EEG τ-mod-Δ tower (a scale hierarchy inside a 3+1 metric solution, which belongs to links 2–3). Candidates: the Cantor/ℤ₂ tail tower (Prop 3); the CD doubling ladder itself. | `CONJECTURE` | Gemini's pivot after the Red Team hole (§3). ⚠ The "infinite CD limit" candidate is in tension with the ratified 2026-06-01 decision (*do not climb above 𝕊*) — recorded, not resolved. |
| **9** | **The gate: Φ is undefined.** There is no map Φ : L_native → S¹⁴/G₂ (nor from the EEG tower) anywhere — not in the ledger, not in Ecker–Grumiller, not in this document. A measure cannot be pushed forward along a map that does not exist. | `BLOCKER` | Both reviewers concede. Defining Φ — what on the substrate side carries the three invariants (|a|², b₀, ⟨a, Im b⟩) — is the next concrete step, **ahead of** any measure claim. |
| **10** | **Intrinsic measure.** Conditional on L_native (Prop 8), its pointless locale admits a uniquely constrained, strictly positive probability measure on its Boolean algebra. | `CONJECTURE` | The load-bearing mathematical claim of the substrate. |
| **11** | **Kill-test (AC1 → AC2 bridge).** Conditional on Φ: if Φ_*(μ) fails to select a *specific* G₂-invariant measure on S¹⁴/G₂ beyond what G₂-invariance already allows — or returns O(15)-Haar for a trivial reason — the substrate is downgraded to PERMITTED and the thread parked. If it selects one, ⟨b₀²⟩ and the full endpoint distribution of the descended flow are forced numbers with zero free functions: that is the AC2 prediction. | `KILL-TEST` | The one place rent is payable. Prop 6 makes it small and plottable. |

## 2. What changed relative to the ledger (`INSIGHT-locale-condensed-chain`, 2026-05-22)

| Ledger position | v0.1 position |
|---|---|
| Spatial case "verified" by a Cantor-set sympy calculation (no surviving script) | Spatial case is Prop 1: a corollary of two Mathlib facts, ℝ included. The Cantor anecdote is decoration; no script needed |
| Pointless case is THE gating question; next step = the EEG τ-mod-Δ tower as forcing poset | EEG tower rejected for link 1 (category error: imports links 2–3). New gate = **Φ undefined** (Prop 9); the target space is now known and small: S¹⁴/G₂, dim 3 |
| "Forcing" (set-theoretic) supplies points | Kept as Prop 4, with the pun firewalled (§4). It produces ℝ-points, not a *selection* of ℝ — route, not forcing in the firewall's sense |
| No statement of what the substrate would have to *deliver* | Props 5–7 + 11: a measure on a 3-dim orbifold, fixing the #629 flow endpoint |

## 3. The two rounds, in one table

| Round | Gemini (Furey/Feynman) | Red Team (Claude) | Outcome |
|---|---|---|---|
| 1 | Accepts L1 as the spatial statement but *trivial — no Lean file*; rejects "Dedekind reals in the pyknotic topos" as classical math in a heavier coat; L3(c) (measure on S¹⁴/G₂) = "100% the earns-in slot"; aims the pointless case at the EEG tower | Prop 3 wording (ℝ not compact); Prop 5 mis-tagged as cited (it is numerical); **hole: no map EEG → S¹⁴** — Prop 9 of round 1 was not a statement | Corrections accepted |
| 2 | Concedes the hole ("we were smuggling link 3 into link 1"); pivots to an algebra-native poset; adds Prop 9 as BLOCKER; confirms the descent identity | Flags the CD-infinite-limit candidate against the do-not-climb decision; corrects "sublocale" → quotient locale; Mathlib has no octonions (identity is provable in `CDAlg`) | Ladder above |

## 4. Vocabulary firewall (three collisions, all real)

| Word | Meaning A | Meaning B | Rule |
|---|---|---|---|
| **locale** | point-free topology, Frmᵒᵖ (this document) | QBP observer-frame construction Λ(Γ) (#539, `substrate-foundational-concerns-resolution-2026-06-13.md` §5) | Never cross-cite; the #539 "locale instinct" is not evidence for this thread |
| **forcing** | set-theoretic forcing, generics of a poset (Prop 4) | FORCED-vs-PERMITTED firewall (2026-06-01 decision) | Prop 4 is meaning A. "A forcing argument for ℝ" in AC1 is meaning B; the ladder shows meaning A does not deliver meaning B |
| **doubling** | Cayley–Dickson doubling (dims 1,2,4,8,16) | binary/halving tower 2^ℕ, ℤ[1/2] (Prop 3) | Resonance, not identity; no derivation connects them (cf. the ledger's own echo-harmony "honest boundary") |

## 5. Human Visual Review

| Artifact | What to eyeball |
|---|---|
| `analysis/473-dirac-probe/hvr_orbit_space.png` | V = δ² over the orbit space (parabolic region |a|² + b₀² ≤ 1, three slices in ⟨a,Im b⟩). One peak at the zero-divisor ridge (½, 0), V = 1; vacua (white) on the edges |a| = 0, Im b = 0, a ∥ Im b. The entire #629 landscape is this picture — the 14-sphere collapsed to three numbers. |
| `orbit_space.py` output | `(1) 14`, `(2) [11,11,11,11,11] → dim 3`, `(3) residual ~1e-16` |

## 6. Next concrete step (one)

**Define Φ** (Prop 9) or prove it cannot be defined from the algebra alone. Concretely: name a pointless locale built from ℝ + doubling data only (Prop 8 candidates) and say which of its structure maps to (|a|², b₀, ⟨a, Im b⟩). Until Φ exists, Props 10–11 are not statements and no Lean or ledger anchor is minted for them. Props 5–6 can be anchored as ordinary `CDAlg` theorems when someone wants them (not substrate work).

## 7. Provenance

- Gemini rounds: `debate-20260904-151140` turns 1–2 (Furey/Feynman, gemini-3.1-pro-preview, thinking). Packets and replies in the session store.
- Numerical: `analysis/473-dirac-probe/orbit_space.py` (this PR), building on `dirac_probe.py` (#629).
- Ratified constraints: 2026-06-01 "Tower height + floor" decision (`gemini/state/decisions/qbp.md`); #473 disposition; empty-Substrate rule (`proofs/QBP/Substrate/README.md`).
- Related: #629 (AC2 first-pass kill; the δ-landscape), `INSIGHT-locale-condensed-chain`, `INSIGHT-echo-harmony-z2`, `CONJ-condensed-math-for-transition-state`.
