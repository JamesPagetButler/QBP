# Ruling bundle — five decisions that edit the same sentences (v0.1, 2026-09-10)

**Status:** decision page for the beekeeper, prepared on request after PRs #648 and #649 merged. qbp-architecture asked (#643 §I4) that the flag-3 split, the P2/P2′ reading, and the boundary vocabulary be ruled **together**, because each edits DERIV-holographic's last sentence. Two further open rulings are listed because their outcome feeds the same encode PR. Every option below already exists as a draft in a merged document; this page only puts them side by side with costs. **Nothing here is applied.** Written by qbp-oppenheimer.

## 0. The five decisions and how they couple

| # | Decision | Options | Recommended | Drafted in |
|---|---|---|---|---|
| 1 | **Which octonion encodes a universe** | P2 (an octonion chosen around the crystal's ℍ; a ℂP² of them) / **P2′** (a Cayley–Dickson half — one of three) | P2′ | `p2-audit-2026-09-09.md` |
| 2 | **Flag 3 — split DERIV-holographic** | keep the single entry with the theorem anchors attached / **split** into POST-observer-associativity + DERIV-holographic-theorem + INTERP-holographic-boundary, re-pointing 8 dependents | split | `holographic-boundary-tail-2026-09-08.md` §5 |
| 3 | **Boundary vocabulary** | keep one word / **three names**: encoding octonion (8-dim), holographic gap (its complement of the observer's algebra), seam (the zero-divisor locus between universes) | three names | boundary note §2 |
| 4 | **#634 AC4** (transverse Hessian) | leave open / **rescope** to the proved spectrum-at-crystal statement and file the Hessian as a follow-up | rescope | #634 issuecomment-5577181264 |
| 5 | **Adopt the AXIOM-2 package for its encode PR** | adopt / hold | adopt, with the six roots named | `axiom2-demotion-proposal-2026-09-09.md` (v0.6) |

**Coupling.** 1 fixes what "the encoding octonion" in 3 means and how the INTERP entry in 2 is worded. 2 and 5 both re-point DERIV-holographic's dependents and should land in one encode PR. 4 is independent but closes #634, which the encode PR also cites. Decisions 1–3 can be ruled in one line each; 5 is a yes/no; 4 is a yes/no.

## 1. Decision 1 — P2 or P2′ (the copy of 𝕆)

Facts on master: the crystal's algebra ℍ_s = span{1, ℓ, U, ℓU} contains ℓ and is not inside the Cayley–Dickson half; it meets the half in exactly ℂ_u = span{1, U} and is the doubling of that ℂ by ℓ. There is an ℓ-fixing order-3 automorphism ρ that carries the half to a different half, preserves the vacuum set, and fixes each ℍ_s as a set (acting on it as an inner automorphism), so the halves form a ℤ/3-torsor and the three ℂ's in ℍ_s are indistinguishable from inside the observer's algebra (`p2_cell_torsor_check.py`, asserted; Lean construction in progress).

| | P2 | P2′ |
|---|---|---|
| New datum a universe carries | a point of ℂP² (4 continuous parameters) | a choice among three halves (1 discrete) |
| Unproved links | the doubled frame is an octonion ⊃ ℍ_s (provable); completeness of the family (conjecture) | none |
| Observation | with the premise O⊆ ("accessible ⊆ encoded in the half"), selects no ℂ | selects a ℂ — the observed one only under (E) "EM's ℂ = ℂ_u" |
| Fits | DERIV-holographic literal; DERIV-sedenion's "inter-cell" natural (each universe its own 𝕆) | DERIV-sedenion as rewritten in the package ("two copies of the encoding"); DERIV-observation's ℂ selected |
| Constitutional cost | none beyond flag 3 | DERIV-holographic's "4D gap" (→ 6-dim complement of ℂ_u); T2 ("largest associative subalgebra of 𝕆 is ℍ") stops describing the observer's algebra; DERIV-3plus1's route (ℍ ⊂ 𝕆 ⇒ 1 + 3) is severed — two of the three spatial directions lie outside the encoding; the flag-3 draft is written under P2 and must be redrafted |
| Truth | undecided; no experiment on record distinguishes them | undecided |

**Recommendation: P2′**, with the ℤ/3 named as the discrete datum. It asserts less and is the only reading that selects a ℂ for observation. **Its price is the T2 / DERIV-3plus1 rewording**, which must be paid in the same encode PR as decision 2. If you prefer to keep DERIV-holographic literal, rule P2 and accept a ℂP² datum with an open completeness conjecture.

**Ruling text (one line):** "Decision 1: P2′ — the encoding octonion of a universe is a Cayley–Dickson half, one of three; the choice is a discrete datum; ℍ_s meets it in ℂ_u." (or "P2".)

## 2. Decision 2 — the flag-3 split

DERIV-holographic today: "Observers require associativity. The largest associative subalgebra of O is H (dim 4). The 4D gap is the holographic boundary." — one entry, three kinds of statement. Proved on master: composition ⇔ associative (T1); frame-maximality (T2); codimension 4 (T3).

| Proposed entry | Text (under P2′; the P2 variant differs only in INTERP) | Kind |
|---|---|---|
| **POST-observer-associativity** | "An observer is a subset of 𝕊 on which its actions compose; by the composition theorem such a subset is associative and lies inside one ℍ. Under the hosting definition the observer's ℍ is the crystal's ℍ_s (definition D; premise P1′: observers are entities of clause (a)). **Exclusivity** — no observer lives outside the hosted algebra — is the postulate's content. **Observation clause (O⊆):** what an observer can access is contained in what is encoded in its half; **(E):** the electromagnetic ℂ is ℂ_u." | postulate |
| **DERIV-holographic-theorem** | "Quaternion frames span{1,u,v,uv} are associative subalgebras of 𝕆; no associative subalgebra of 𝕆 properly contains one (frame-relative; the global bound is deferred); the codimension of ℍ in 𝕆 is 4. **Under P2′ this describes the frame inside the encoding half, not the observer's algebra, which straddles the halves.**" | theorem, proved |
| **INTERP-holographic-boundary** | P2′: "The holographic gap of a universe is the 6-dim complement of ℂ_u in its encoding half; the seam boundary between universes is the zero-divisor locus (DERIV-sedenion). The encoding half is one of three, a discrete datum." P2: "…the 4-dim gap ℍ_s^⊥ inside an encoding octonion 𝕆'_v ⊃ ℍ_s; the encodings form a ℂP²…" | interpretation, proposed |

**Re-pointing** (from the boundary note §5, Red Team-completed): DERIV-3plus1 → POST + theorem (and under P2′ its route must be re-argued); DERIV-observation → POST (O⊆, E) + theorem; DERIV-pati-salam → theorem; DERIV-arrow → POST + INTERP + AXIOM-1; DERIV-constants → POST + INTERP; anchors PROOF-3gen → theorem, PRED-gw-em and PRED-revival-exact → POST + INTERP. Six Lean docstring sites that say "NOT identified with the observer's ℍ … pending flag 3" are updated in the same PR.

**Recommendation: split.** Every citation can then say which part it rests on; the two theorems stop carrying a postulate's weight. **Ruling text:** "Decision 2: split DERIV-holographic into POST / theorem / INTERP as drafted; re-point the eight dependents; update the six guardrail docstrings."

## 3. Decision 3 — three names for "boundary"

| Name | Object | Dim | Parent |
|---|---|---|---|
| encoding octonion | the octonion AXIOM-2's "boundary encoding" refers to (under P2′: a Cayley–Dickson half) | 8 | AXIOM-2 |
| holographic gap | the complement of the observer's algebra inside its encoding (under P2′: of ℂ_u in the half, 6-dim; under P2: of ℍ_s in 𝕆'_v, 4-dim) | 6 or 4 | DERIV-holographic |
| seam | the zero-divisor locus V = 1 in the substrate, between universes | 11 | DERIV-sedenion |

**Recommendation: adopt**, and forbid the bare word "boundary" in any ledger entry or Lean docstring without one of the three. **Ruling text:** "Decision 3: adopt the three names."

## 4. Decision 4 — #634 AC4

AC4 asked for the transverse Hessian 4r²·I on the 6-dim normal space (or the {1−δ, 1, 1+δ} multiplicities). Delivered on master: the spectrum *at* the crystal — −L_s² = N(s)·id ⇔ vacuum, the unique eigenvalue, the exact first-order alternator expansion. Both reviewers on #641 marked it PARTIAL.

**Recommendation: rescope** AC4 to the proved statement and file the Hessian as a follow-up issue; #634 then closes. **Ruling text:** "Decision 4: AC4 rescoped to the spectrum-at-crystal statement; Hessian filed as a follow-up."

## 5. Decision 5 — adopt the AXIOM-2 package for its encode PR

What the encode PR would apply (package v0.6, all drafts): META-2 level saturation (schema: `meta_axiom` becomes a list); POST-hosting (final form: non-crystal states are physically realised; almost every history starts in flight; theory-internal kill); DERIV-encoding-level (replaces AXIOM-2); DERIV-substrate-level (with the level-generic crystal definition); DERIV-sedenion's derived_from inverted to [DERIV-substrate-level, DERIV-encoding-level] (its clause is already option B, PR #651); re-pointing of 14 anchors, 5 principles, 7 chain texts, 4 docs and the `Hosting.lean` docstrings. **Honest outcome:** six named roots (AXIOM-1, POST-hosting, the rule, META-2, the crystal definition, the state-space identification), not fewer. Nothing is derived that was not already proved; what changes is that every root is named.

**Recommendation: adopt.** **Ruling text:** "Decision 5: adopt the package; encode as drafted."

## 6. What the encode PR contains if all five are ruled as recommended

One PR, constitutional, Tier 3: the package's texts (5); the flag-3 split (2) worded under P2′ (1) with the three names (3); the re-pointing lists; the Lean docstring updates; #634 closed on AC4's rescope (4). Lean owed separately and already in progress: the order-3 automorphism as a `CDAut 4`, the two P2′ lemmas, the docstring correction that the order-3 elements fix ℓ.

## 7. What stays open after the bundle

The definition conversation (the beekeeper's step 4 of 2026-09-07), whose starting position now includes P2′, the ℤ/3 datum, premises O⊆ and E, and the boundary note's §5 questions; #647 (the process question, on its trigger); #650 (the σ-blind status convention); flag 1's rescope price if #647 is ever ruled "yes"; the bulk-to-boundary map, which no reading supplies.
