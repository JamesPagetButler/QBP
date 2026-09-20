# Conversation-runner report — the rule's flow (#635 Phase B), 2026-09-20

**Status:** the runner's report as returned to the dispatching seat (qbp-oppenheimer); written to disk by the driver because the transcript cites it. The runner does not assess the §3 gate; the heterogeneous confirmer does (`rule-flow-research-conversation-confirmer-verdict-2026-09-20.md`). **Nothing here is anchored, encoded or ruled.** Brief: `rule-flow-research-conversation-brief-2026-09-20.md`; transcript and verbatim alongside; probe scripts in `analysis/rule-flow-conversation-2026-09-20/`.

**Session:** `debate-20260920-051302` (new). **Verbatim:** turns 0–9, all 10, complete. **Rounds:** 5 of 5. Model gemini-3.1-pro-preview, thinking on.

## Four buckets (runner's sort; see the confirmer's audit for demotions/promotions)

| # | Claim | Bucket | TEST |
|---|---|---|---|
| 1 | No merging in finite time; sphere invariant; V̇ = −‖F‖²; crystals are rest points | 1 PROVED | `flow_time_map_injective`, `eulerStep_injOn`, `stateSphere_invariant`, `potential_nonincreasing_along_flow`, `ruleField_eq_zero_of_isVacuum` |
| 2 | Rest points ⊋ crystals | 1 (existence) / 3 for the Lean line | `potential_witness = 4` + compactness; probe1: 8/8 ascents → V = 1, ‖F‖ ≤ 7.7e-16 |
| 3 | spec(L_sᵀL_s) = {N−√V}×4 ∪ {N}×8 ∪ {N+√V}×4, all s | 3 (numerically exact 8.3e-15 / 200; UNDERIVED) | probe4; kill: a proof or one counterexample |
| 4 | V ≤ N(s)² (max V on S¹⁴ = 1) | 3 provable-now, S–M | ‖x×y‖² = ‖x‖²‖y‖² − ⟨x,y⟩² + AM–GM (probe6, 8.5e-14) |
| 5 | Zero divisor ⟺ V = N² (s ≠ 0 — confirmer); crystals are NOT zero divisors (σ_min = 1) | 3 provable-now, M | probe2/3; only ZD ⇒ V = N² is load-bearing |
| 6 | ZD locus = argmax V = manifold of rest points; frozen | 3 provable-now, S given 4+5 | constrained max ⇒ F = 0 |
| 7 | ω(s) never meets the ZD locus when V(s₀) < 1 — kill conjunct 1 fails from below | 3 provable-now, S given monotonicity | needs no convergence |
| 8 | ω-limit map is constant along flow lines ⇒ non-injective on every positive-measure set with motion; the DISCHARGE clause is unsatisfiable by construction | 3 OPEN / §10 impasse | see the confirmer |
| 9 | Crystal set is 8-dimensional | 3 (derived + probe5) | flat-direction count ≠ dimension |
| 10 | Point convergence (Łojasiewicz) | 3 open, XL | Mathlib gap, not nature's |
| 11 | Local existence (`IsPicardLindelof`) | 3 open, L | everything above the finite-time facts is conditional on it |
| 12 | Div F: contracts below V_c ≈ 0.659, expands above (corr 0.958, N = 400) | 3 (numerical) | probe7 |
| 13 | FLAG-seam-dynamics-open's seam scattering is unreachable by the deterministic rule | 3 open | the seam language is stochastic; #635 is T = 0 descent |
| 14 | Gemini's Δ = 2⟨[a,b]c,d⟩; "Div F < 0 everywhere"; the bet against point convergence; "a,b ∈ Im 𝕆"; "crystal set is 9-dim" | 4 WITHDRAWN — author: Gemini | each within one round of a check |
| 15 | The rule's form; AXIOM-1 kill/discharge wording | 2 FORCED | #635; ledger `AXIOM-1.kill_condition[0]`; `FLAG-rule-flow-open` |

## §7 tells
R1 post-hoc reasoning (assumed a,b ∈ Im 𝕆, then "derived" it) and premature confidence (Hessian flat count read as a dimension). R2 premature convergence ("I cannot break your computation … thoroughly discharged") in the same turn as a defect identity failing a 200-sample check. R3 an overconfident forward prediction (Div F < 0 everywhere) offered as decisive. R4 a bet against a classical theorem. All withdrawn on contact with a check; the strongest argument in the conversation (item 8) is Gemini's.

## The last easy answer
"The zero-divisor locus is the global max of V and is frozen, so the flow never reaches it and AXIOM-1's kill can't fire." Test on: item 3 is numerics only; the chain needs local existence for the continuous case; it says nothing about the discharge (item 8).

## Sealed positions vs Gemini
R1 (LaSalle + maximiser as a non-vacuum rest point) matched; R3 (crystals are not zero divisors) matched and checked numerically before Gemini answered. A match is not evidence; the probes are.

## Not verified by the runner
The 4/8/4 spectrum (numerics only); the seam-kernel theorems (on another branch); the "1.000 vs 0.146" flag — RESOLVED by the confirmer: 0.146 is the endpoint mean of b₀², not a crystallisation fraction; the same run gives both.

## Research approach (sorted)
Provable now: `potential_le_normForm_sq`; `abs_normForm_mul_sub_le` (|N(sx) − N(s)N(x)| ≤ √V(s)·N(x)); `mul_injective_of_potential_lt` (V(s) < 1 on the sphere ⇒ s· injective); `ruleField_eq_zero_of_potential_eq_one`; `omegaLimit_potential_lt_one` (a forward curve from V < 1 never meets a zero divisor); `exists_ruleField_eq_zero_and_potential_pos`. Numerical probes: 4/8/4 derivation search; crystal-set dimension; non-crystal endpoint fraction (0/2000 so far; needs biased seeding to say anything about stable manifolds). Open with kills: local existence (L); point convergence (XL); the discharge impasse (item 8); the seam (a stochastic extension of #635, or a proof none is algebra-compatible).
