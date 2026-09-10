# Red Team confirmer pass — P2 vs P2′ rigor audit (`docs/foundations/p2-audit-2026-09-09.md`, branch `research/p2-audit` @ 79dd705)

Read: the audit; verbatim turns 62–65; `holographic-boundary-tail-2026-09-08.md` (master, v0.3); ledger v0.3 entries AXIOM-2, DERIV-sedenion, DERIV-holographic, DERIV-observation, DERIV-3plus1, OBS-desi-4thirds; `CrystalHosting.lean`, `Hosting.lean`, `NoAutonomousDynamics.lean` (`InQuatSpan`, `cdLo_mul`/`cdHi_mul`). Three computations run with the repo's own `cd_mul` (`analysis/473-dirac-probe/dirac_probe.py`); nothing edited, committed, or posted.

## Findings

| # | Finding | Where | Severity | Persona |
|---|---|---|---|---|
| 1 | **"0 new roots / canonical" for P2′ is false in the abstract algebra.** There is an order-3 automorphism ρ of 𝕊 fixing ℓ (a ↦ cos(2π/3)·a + sin(2π/3)·aℓ on Im 𝕆, ℓ ↦ ℓ; automorphism residual 7e-15, ρ³ = id) that carries the low half 𝕆 to a *different* closed octonion subalgebra (rank(𝕆 ∪ ρ𝕆) = 15). ρ preserves the vacuum set (V(ρs) = 0 for every crystal s; V is ρ-invariant even generically), so **the crystal does not pick a half**, and ℍ_s ∩ ρ(𝕆) = ℂ_{u′} with u′ = cos(2π/3)U + sin(2π/3)Uℓ — a *different* ℂ in ℍ_s. "The cell" is a choice in a Z₃-torsor (three CD halves, three ℂ's at 120° in the (U, Uℓ)-plane). Consistent with the literature's Aut(𝕊) ≅ G₂ × S₃ (Brown 1967 — cited from memory, §7 rule: verify before relying). Root count P2′ = **1 discrete** (or "a definition doing physical work" if the substrate is the coordinatised `CDAlg ℝ 4`); P2 = a ℂP² (4 continuous). Ordering survives; the number and the word "canonical" do not. | audit §1, §2, §4; turn 62 "canonical, no choice" | **HIGH** | Grothendieck |
| 2 | **"P2 + O contradicts DERIV-observation" is an artifact of the quantifier in (O).** Read as an upper bound (O⊆: accessible ⊆ encoded-in-cell), P2 + O⊆ says accessible ⊆ ℍ_s — no contradiction; EM's ℂ is picked by EM as before. Read as equality (O=: everything encoded is accessed, no further projection), P2 + O= contradicts — but P2′ + O= then *over*-entails ("EM accesses all of ℂ_u") and still owes DERIV-observation's second step ℂ → ℝ. "Entails" also needs (E): EM's ℂ = ℂ_u (the U(1) axis = the crystal direction, up to the Z₃ of #1) — not on record; DERIV-pati-salam's ℂ is a separate summand of A_F, not a subalgebra of ℍ. And DERIV-observation is `derived_from` DERIV-holographic, the P2-literal entry: a premise under which P2 contradicts its own downstream entry is evidence against the premise before it is evidence against P2. Honest statement: **P2′ + O⊆ selects the ℂ; P2 + O⊆ selects none; neither contradicts.** | audit §3 row 1, §4, §5 verdict; turn 64 A ("State it that way, or refute"), turn 65 A | **HIGH** | Sabine |
| 3 | Under P2′ the cell 𝕆 is **the same for every universe** (a global half, not per-crystal), so "its own cell" in (O) has no per-observer referent, and DERIV-sedenion *on record* ("inter-cell boundary structure is 𝕊") presupposes many cells. The "DERIV-sedenion exact" fit is to PR #648's rewrite ("𝕊 = 𝕆 ⊕ 𝕆ℓ, two copies"), unmerged (§I4), not to the ledger. Under P2 each universe has its own 𝕆′_v. | audit §2 fit row | MEDIUM | Grothendieck |
| 4 | **"Constitutional edits forced: one sentence" undercounts.** Under P2′ ℍ_s is not a subalgebra of the encoding, so "the largest associative subalgebra of 𝕆 is ℍ" (T2) stops describing the observer at all; DERIV-3plus1's route (ℍ ⊂ 𝕆 maximal-associative ⇒ 1+3) is severed, two of its three spatial directions leaving the encoding; and the flag-3 split draft (boundary doc §5 INTERP entry "ℍ_s-line in ℍ_s^⊥ inside 𝕆′_v ⊃ ℍ_s", the three-name vocabulary) is written under P2 and must be redrafted. "Already being rewritten" is true of the *slot*, not of the draft on master. | audit §2, §5 "Cost" | MEDIUM | Grothendieck |
| 5 | The (O)-discriminator was authored by the driver (turn 64 A) and returned verbatim (turn 65 A); Gemini held no counter-position in either round (pro-P2′ from turn 63 §1); the sealed table sat in the same prompt as "write yours first" (not a thing a single forward pass can honour); the turn-62 framing pre-computed the counts ("asserted numerically", "CONJECTURE", "five-line lemmas", "canonical"). My recount differs on two rows (#1, #4) — the counts are framing-dependent, so the match is a §7 tell (anchoring + sycophancy), not evidence. Nobody pressure-tested round 8's conclusion; #2 is that test and it fails. | verbatim 62–65; audit §2 heading | MEDIUM | Sabine |
| 6 | **Sign error:** (Uℓ)·ℓ = −U, not U (`cdLo_mul` with x = hiOf u, y = hiOf 1 gives −conj(1)·u; numerically −u). The +U example is (ℓU)·ℓ. The point (cell component ±U ≠ 0·0) stands. | audit §3 row 4; turn 64 D; turn 65 D | LOW | Knuth |
| 7 | P2 "unproved links: 2" — completeness is not a link *in P2* ("some octonion ⊃ ℍ_s" needs only (i)); it is a conjecture about the root's moduli (that it is ℂP²). Count as 1 unproved link + 1 conjecture on the root. | audit §2 | LOW | Knuth |
| 8 | The two P2′ lemmas are real five-to-eight-liners (sketches below). Add a third: `∃ ρ : automorphism, ρ ℓ = ℓ ∧ ρ '' lowHalf ≠ lowHalf`, or at least the ρ check in `boundary_octonion_check.py` — it is the whole content of #1. | audit §6 item 2 | LOW | Knuth |
| 9 | Gemini's measurement gloss leaks in two places: §5's kill is turn 65's kill with "lossy projection" shortened to "projection" (it presupposes the gloss), and §3's last sentence imports "lossy projection" — DERIV-arrow's phrase — into DERIV-observation, which does not say it. The kill is nominal: no observable on record can fire it. | audit §3 row 4, §5 | LOW | Sabine |
| 10 | Withdrawals correct (ℓU = −Uℓ, both high-half; no propagation mechanism on record — the hosted physics is `SkyrmionCharge`/H-space, direction-blind). Refinement to the replacement: the in/out "orientation of the pair" is itself Z₃-ambiguous (#1), so P2′ fixes *a* type-asymmetry only after the half is chosen. | audit §3 rows 2–3 | LOW | Knuth |
| 11 | §5 "cannot say which is true; no experiment distinguishes" is honest and should stay. The added honesty: the *only* discriminator is a quantifier choice in a premise introduced in-round. | audit §5 | LOW | Sabine |

## 1. The counts, recomputed

| Count | P2 | P2′ (audit) | P2′ (recount) |
|---|---|---|---|
| New roots | 1 continuous (ℂP²) — right | 0 | **1 discrete** (Z₃ choice of half) or a coordinate definition doing work (#1) |
| Unproved links | 2 | 0 | 0 for the algebra; the *reading* "AXIOM-2's 𝕆 = a CD half" is the reading itself, not a link — but "= *the* half" hides #1 |
| Provable-now | 1 | 2 trivial | 2 trivial + the ρ lemma (#8) |
| Constitutional edits | none beyond flag 3 — right | one sentence | T2's relevance, DERIV-3plus1's route, the flag-3 draft (#4) |
| Fit | DERIV-holographic literal — right | DERIV-sedenion "exact" | exact to #648's draft text; strained against the ledger's "inter-cell" (#3) |

Existence of 𝕆′_v as an octonion ⊃ ℍ_s: numerically asserted (5 trials, closure 5e-16, alternativity 2e-14) and provable via `cdLo_mul`/`cdHi_mul` from the associativity of ℍ′_v — correctly an unproved link. Completeness: correctly a conjecture, but see #7.

**Lean sketches.** (i) `quatSpan_inter_lowHalf`: `InQuatSpan (loOf u) x ∧ cdHi x = 0 ↔ ∃ a c, x = a•1 + c•loOf u`. →: `obtain ⟨a,b,c,d,rfl⟩`; `cdHi_quatComb` gives `b•1 + (−d)•u = 0`; `coeff_zero_of_span_one_u` ⇒ b = 0; the `N_smul`/`hNu` step of `crystal_quatSpan_independent` ⇒ d = 0; `simp`. ←: witness `⟨a,0,c,0⟩` + `cdHi_quatComb`. Needs `N u = 1`. ~8 lines. (ii) `quatSpan_eq_cd_double`: `InQuatSpan (loOf u) x ↔ ∃ a c b d, x = (a•1 + c•loOf u) + (b•1 + d•loOf u) * ell`; expand with `add_mul`, `smul_mul_assoc`, `one_mul`, then `inQuatSpan_ell_right`; directness is `crystal_quatSpan_independent`. ~5 lines. The cell-component map on ℍ_s is `cdLo` restricted: linear by `cdLo_add`/`cdLo_smul`, not multiplicative by `cdLo_mul`'s second term — the audit's fact is right, its example's sign is not (#6).

## 2. Premise (O)

Correctly identified as a root both readings need for *any* observation statement — the geometry alone says nothing about access. But it was written without its quantifier, and the discriminator lives entirely in that quantifier (#2). DERIV-observation's ℂ is *EM's* ℂ (the ledger says "electromagnetic observation"; ℍ has an S² of ℂ-subalgebras and the ledger's definite article is loose). P2′ + O gives a *geometric* ℂ, ℂ_u, and — after #1 — one of three. That is a sharper claim than the ledger's and a genuine asymmetry with P2 (which selects nothing); it is not an entailment of the ledger's sentence, and the P2 side is not a contradiction. The consistency discriminator should be restated as a *selection* discriminator.

## 3–4. Withdrawals; the gloss

Both withdrawals are right (#10). "Interpretation, not adopted" is the correct disposition of the hidden-variables/decoherence gloss; it is not fully honoured — the kill and one sentence carry its residue (#9).

## 5. Tells

Fast agreement on both rounds; the driver's proposals returned as conclusions; no counter-position ever held; counts dictated by the setup text (#5). Per MO §7 the match is not evidence either way, and the one place the dyad could have diverged — whether the cell is canonical — was the one place neither looked.

## 6. Gate §3

| Condition | Status |
|---|---|
| 1 Next steps reasoned | met (audit §6 has reasons) |
| 2 Load-bearing assumptions validated | **not met**: "canonical" was load-bearing and false (#1); (O)'s quantifier is load-bearing and unexamined (#2) |
| 3 Grounded | mostly — Lean and ledger cited; the DERIV-sedenion fit cites an unmerged draft (#3) |
| 4 Shared understanding | met between the two parties; but no party held the P2 side |
| 5 Easy answer pressure-tested | met for round 7's three over-claims; **not met** for round 8's own conclusion |

§5's "cannot say which is true; no experiment distinguishes" is honest and should be kept verbatim.

## 7. Verdict — CONFIRMED-ON-CONDITIONS

The structural ordering — **P2′ asserts less than P2** — is confirmed: a discrete choice against a 4-parameter one, no octonion-existence link, no completeness conjecture. The two headline sentences as written may not go to the beekeeper:

1. **"P2′ is the more rigorous reading"** — may be put, provided §2/§4 say "one discrete root (the choice of Cayley–Dickson half among the three related by the order-3 automorphism; the crystal does not pick one)" in place of "0 / canonical", and #4's edits are listed as the cost.
2. **"P2 + O contradicts DERIV-observation"** — may **not** be put as a result. Replace with: "with (O) as an upper bound neither reading contradicts DERIV-observation; P2′ + O selects the observed ℂ (ℂ_u, up to the Z₃), P2 + O selects none; the contradiction appears only under the equality reading of (O), under which P2′ + O also over-entails and still owes ℂ → ℝ." Fix §4's consistency row accordingly.
3. Fix the sign (#6); reword the P2 unproved-link count (#7); attribute the DERIV-sedenion fit to #648's draft (#3).
4. Strip the gloss residue from §5's kill and §3's last sentence, or mark the kill nominal (#9).
5. Record #5 as the round's §7 tell in the audit's status line; this pass is the missing pressure-test and it changed the discriminator.
6. Add the ρ automorphism as a third Lean lemma or a scripted assertion in `boundary_octonion_check.py` before the beekeeper ruling — it is the fact that turns "0" into "1" and "canonical" into "chosen".

— Red Team confirmer — Sabine · Grothendieck · Knuth
