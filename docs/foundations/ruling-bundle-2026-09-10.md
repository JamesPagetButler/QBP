# Ruling bundle — six decisions that edit the same sentences (v0.2, 2026-09-10)

**Status:** decision page for the beekeeper, prepared on request after PRs #648 and #649 merged; **v0.2 applies the PR #652 Red Team review** (six must-changes, should-fixes). qbp-architecture asked (#643 §I4) that the flag-3 split, the P2/P2′ reading, and the boundary vocabulary be ruled **together**, because each edits DERIV-holographic's last sentence. Two further open rulings are listed because their outcome feeds the same encode PR, and a **Decision 0** is added because one of the package's texts rests on a ruling that has no source in the beekeeper's hand yet. Most texts below are drafts carried from merged documents and say where from; the two that are **composed on this page** (v0.1/v0.2) are marked as such. **Nothing here is applied.** Written by qbp-oppenheimer.

## 0. The decisions and how they couple

| # | Decision | Options | Recommended | Drafted in |
|---|---|---|---|---|
| **0** | **AXIOM-1 option B — a ruling line in the beekeeper's own hand** | post one line on #647 or #651 / do not | post | PR #651 Red Team F1; package §8 item 2 ("owed") |
| 1 | **Which octonion encodes a universe** | P2 as a line (a ℂP² point) / P2 as the bundle (no datum; the module ℍ_s^⊥ ≅ ℍ_s³ with its cone of admissible lines) / **P2′** (a Cayley–Dickson half — one of three) | P2′, by parsimony; see the caveats in §1 | `p2-audit-2026-09-09.md`; boundary note §3, §7 Q2 |
| 2 | **Flag 3 — split DERIV-holographic** | keep the single entry with the theorem anchors attached / **split** into POST-observer-associativity (+ a separate POST-observation) + DERIV-holographic-theorem + INTERP-holographic-boundary, re-pointing 8 dependents | split | boundary note §5; the POST texts as re-homed here (§2) |
| 3 | **Boundary vocabulary** | keep one word (cost: "boundary" currently names three objects — an 8-dim algebra, its 4- or 6-dim complement, and an 11-dim locus — and qbp-architecture flagged the overload) / **three names**: encoding octonion, holographic gap, seam | three names | boundary note §2 |
| 4 | **#634 AC4** (transverse Hessian) | (ii) leave AC4 as written: #634 stays open past #641 and the Hessian is proved in a later PR against the same anchor batch / **(i) rescope** to the proved spectrum-at-crystal statement and file the Hessian as a follow-up | rescope | #634 issuecomment-5577181264 |
| 5 | **Adopt the AXIOM-2 package for its encode PR** | adopt (**conditioned on Decision 0**) / hold (until Decision 0 and, if wanted, the definition conversation) | adopt, conditioned | `axiom2-demotion-proposal-2026-09-09.md` v0.6 |

**Coupling — stated in full (Red Team #652 F7).**
- 1 fixes what "encoding octonion" means in 3 and how the INTERP entry in 2 is worded (4-dim gap under P2, 6-dim complement of ℂ_u under P2′).
- 2 and 5 both touch DERIV-holographic **itself**, not only its dependents: 5 re-points its `derived_from` to [AXIOM-1, DERIV-encoding-level] and re-derives its preamble ("the boundary is derived, not axiomatic"); 2 deletes the entry and replaces it with three. Encoded separately in the wrong order, 5 edits an entry 2 removes.
- The package (5) leaves one premise **unplaced** — "there is a boundary encoding" (package §2a: "the interpretation I of the boundary note"). Decision 2's INTERP entry is where it must land.
- The package's rewritten DERIV-sedenion ("𝕊 = 𝕆 ⊕ 𝕆ℓ: the substrate decomposes as two copies of the encoding") is **P2′-worded** (audit §2 Fit row; confirmer #3). Under P2 it needs rewording. So 5 is not independent of 1 as encoded.
- 4 is independent of 1–3 and 5; it is on this page only because the encode PR cites #634.
- 0 gates 5 and the merge of #651.

**One PR or two?** The merged package's own §8 item 4 says: *"Do not fold P2 / P2′ or the flag-3 split into this PR — because they are independent rulings and the package is orthogonal to the copy question."* This page proposes the opposite (§6) **and says so**: the reason is the second and fourth coupling bullets above, found after the package was written — the package's encode edits DERIV-holographic and words DERIV-sedenion under P2′, so encoding it alone would land texts that decisions 1–2 immediately rewrite. The beekeeper can still choose two PRs (5 first, then 1–3); §6 gives both shapes.

## Decision 0 — the option-B ruling line

PR #648 merged and PR #651 (the ledger edit) is open, unmerged, and **blocked** on one thing both reviewers flagged: the AXIOM-1 option B ruling exists in the package, in the commit, in #647's body and in this page — all agent-authored — and nowhere in the beekeeper's own hand on GitHub. The ledger entry's new `ruling` field has a placeholder for that URL.

**Ruling form:** one comment on #647 or #651: "AXIOM-1 option B — ruled 2026-09-09; apply." The URL goes into DERIV-sedenion's `ruling` field in #651 before it merges.

## 1. Decision 1 — P2 or P2′ (the copy of 𝕆)

Facts on master: the crystal's algebra ℍ_s = span{1, ℓ, U, ℓU} contains ℓ and is not inside the Cayley–Dickson half; it meets the half in exactly ℂ_u = span{1, U} and is the doubling of that ℂ by ℓ. There is an ℓ-fixing order-3 automorphism ρ that carries the half to a different half, preserves the vacuum set, and fixes each ℍ_s as a set (inner on it), so the halves form a ℤ/3-torsor and the three ℂ's in ℍ_s are indistinguishable from inside the observer's algebra. ρ is **asserted by script** (`p2_cell_torsor_check.py`, which meets the confirmer's "ρ lemma or scripted assertion before the ruling"); its Lean construction as a `CDAut 4` is owed and in progress on a local branch, not yet a PR.

| | P2 as a line | P2 as the bundle | P2′ |
|---|---|---|---|
| New datum a universe carries | a point of ℂP² (4 continuous parameters) | **none** — the boundary is the canonical module ℍ_s^⊥ ≅ ℍ_s³ with its cone of admissible lines; no line chosen (boundary note §3, §7 Q2) | a choice among three halves (1 discrete) |
| Unproved links | the doubled frame is an octonion ⊃ ℍ_s (provable, moderate); completeness of the family (conjecture — live under P2 only) | the same two | none |
| Observation | with O⊆ ("accessible ⊆ encoded in the encoding"), selects no ℂ | selects no ℂ | selects a ℂ under O⊆ — the *observed* one only under (E) "EM's ℂ = ℂ_u" |
| Fits | DERIV-holographic literal; DERIV-sedenion's "inter-cell" natural (each universe its own 𝕆) | as P2 | DERIV-sedenion **as rewritten in the package** ("two copies of the encoding"); **strained against the ledger's own "inter-cell" wording** — the half is global, the same for every universe, so "its own cell" has no per-observer referent (confirmer #3); DERIV-observation's ℂ selected |
| Constitutional cost | none beyond flag 3 | none beyond flag 3 | DERIV-holographic's "4D gap" (→ 6-dim complement of ℂ_u); T2 ("largest associative subalgebra of 𝕆 is ℍ") stops describing the observer's algebra; DERIV-3plus1's route (ℍ ⊂ 𝕆 ⇒ 1 + 3) is severed — two of the three spatial directions lie outside the encoding; the flag-3 draft is written under P2 and must be redrafted |
| Truth | undecided | undecided | undecided — **no experiment on record distinguishes any of the three; the ruling is by parsimony** |

**Recommendation: P2′**, with the ℤ/3 named as the discrete datum — **with three caveats the record insists on.** (i) The selection discriminator holds only under O⊆, a premise introduced in-round, and gives the *observed* ℂ only under (E); (ii) the audit's §7 tell is on record: both Gemini rounds were fast agreement and no party ever argued the P2 side; (iii) P2's bundle form costs no datum at all, and if the beekeeper weighs "no new datum" above "fewer unproved links", the bundle form is the rigorous P2. What P2′ buys is: one discrete choice instead of a four-parameter family, no octonion-existence link, no completeness conjecture. What it costs is the T2 / DERIV-3plus1 rewording, paid in the same encode PR as Decision 2.

**Ruling text (one line):** "Decision 1: P2′ — the encoding octonion of a universe is a Cayley–Dickson half, one of three; the choice is a discrete datum; ℍ_s meets it in ℂ_u." (or "P2 as a line" / "P2 as the bundle".)

## 2. Decision 2 — the flag-3 split

DERIV-holographic today: "Observers require associativity. The largest associative subalgebra of O is H (dim 4). The 4D gap is the holographic boundary." — one entry, three kinds of statement. Proved on master: composition ⇔ associative (T1); frame-maximality in 𝕆 (T2 — **in 𝕆 only; whether any associative subalgebra of 𝕊 properly contains ℍ_s is open**, boundary note §6 (ix)); codimension 4 (T3).

The boundary note §5 drafted three entries. Two later documents added observation premises (§1a: D, P1′, exclusivity; the P2 audit §6 item 4: O⊆, E) and the audit offered **two homes** for O⊆/E — "as the observation clause of POST-observer-associativity, or as their own POST". **This page recommends the separate POST** (Red Team #652 F5): folding a physical identification like (E) into the associativity postulate would recreate the one-entry-three-claims conflation the split exists to cure. The texts below are therefore **composed on this page** from those drafts, not carried verbatim.

| Proposed entry | Text | Kind | Reading-dependent? |
|---|---|---|---|
| **POST-observer-associativity** | "An observer is a subset of 𝕊 on which its actions compose; by the composition theorem such a subset is associative, and — **if it lies inside an octonion** — inside one ℍ by frame-maximality (in 𝕊 at large this is open). Under the hosting definition the observer's ℍ is the crystal's ℍ_s (definition D; premise P1′: observers are entities of clause (a)). **Exclusivity** — no observer lives outside the hosted algebra — is the postulate's content." | postulate | no |
| **POST-observation** (new home for O⊆ and E) | "**(O⊆)** What an observer can access is contained in what is encoded in its encoding octonion. **(E)** The electromagnetic ℂ of DERIV-observation is the ℂ selected by that encoding." | postulate | (E) has content only under P2′ (where a ℂ is selected); under P2 it is empty and DERIV-observation's ℂ is EM's own |
| **DERIV-holographic-theorem** | "Quaternion frames span{1,u,v,uv} are associative subalgebras of 𝕆; no associative subalgebra of 𝕆 properly contains one (frame-relative; the global bound is deferred); the codimension of ℍ in 𝕆 is 4." | theorem, proved | **no** — the same text under either reading |
| **INTERP-holographic-boundary** | **Common to both readings:** "There is a boundary encoding: each universe has an encoding octonion (AXIOM-2), and the holographic gap is the complement of the observer's algebra inside it; the seam boundary between universes is the zero-divisor locus (DERIV-sedenion)." **Under P2′:** "The encoding octonion is a Cayley–Dickson half, one of three, a discrete datum; ℍ_s meets it in ℂ_u; the theorem above describes the frame inside the half, not the observer's algebra, which straddles the halves; the gap is 6-dim." **Under P2 (line):** "The encoding octonion is 𝕆'_v ⊃ ℍ_s, chosen from a ℂP²; the gap is the 4-dim ℍ_s^⊥ ∩ 𝕆'_v." **Under P2 (bundle):** "The boundary is the canonical module ℍ_s^⊥ ≅ ℍ_s³ with its cone of admissible lines; no encoding is chosen." | interpretation, proposed; **houses the package's unplaced premise "there is a boundary encoding"** | yes — three variants |

**Re-pointing** (boundary note §5, Red Team-completed): DERIV-3plus1 → POST-associativity + theorem (under P2′ its route must be re-argued); DERIV-observation → POST-observation + theorem; DERIV-pati-salam → theorem; DERIV-arrow → POST-associativity + INTERP + AXIOM-1; DERIV-constants → POST-associativity + INTERP; anchors PROOF-3gen → theorem, PRED-gw-em and PRED-revival-exact → POST + INTERP. Sites that also cite the old entry and must move: `CHAIN-born-to-revival.source_ids`; the four flag-3 PROOF anchors' descriptions ("DERIV-holographic, theorem part n"); PROOF-crystal-hosts-quaternion's "NOT claimed" note; CONJ-condensed-math's `converges_with`. Guardrail docstrings that say "NOT identified with the observer's ℍ … pending flag 3", to update in the same PR: `proofs/QBP/Substrate/Hosting.lean` lines 73–75, 288–289, 566–568; `proofs/QBP/Foundations/CrystalHosting.lean` 82–83, 555–557; `proofs/QBP/Substrate/README.md` 26; `proofs/QBP/Foundations/HolographicSubalgebra.lean` 9; `docs/foundations/substrate-hosting-definition-2026-09-07.md` status line and §3.

**Recommendation: split**, with the separate POST-observation. **Ruling text:** "Decision 2: split DERIV-holographic into POST-associativity / POST-observation / theorem / INTERP as drafted; re-point the eight dependents and the listed sites; update the guardrail docstrings."

## 3. Decision 3 — three names for "boundary"

| Name | Object | Dim | Parent |
|---|---|---|---|
| encoding octonion | the octonion AXIOM-2's "boundary encoding" refers to (under P2′: a Cayley–Dickson half) | 8 | AXIOM-2 |
| holographic gap | the complement of the observer's algebra inside its encoding (P2′: of ℂ_u in the half, 6-dim; P2: of ℍ_s in 𝕆'_v, 4-dim) | 6 or 4 | DERIV-holographic |
| seam | the zero-divisor locus V = 1 in the substrate, between universes | 11 | DERIV-sedenion |

**Cost of keeping one word:** the three objects differ in dimension by a factor of two and in ambient space, and qbp-architecture flagged the overload on #643 as the thing to fix together with the split. **Recommendation: adopt**, and forbid the bare word "boundary" in any ledger entry or Lean docstring without one of the three. **Ruling text:** "Decision 3: adopt the three names."

## 4. Decision 4 — #634 AC4

AC4 asked for the transverse Hessian 4r²·I on the 6-dim normal space (or the {1−δ, 1, 1+δ} multiplicities). Delivered on master: the spectrum *at* the crystal — −L_s² = N(s)·id ⇔ vacuum, the unique eigenvalue, the exact first-order alternator expansion. Both reviewers on #641 marked it PARTIAL. Options as put on #634: (i) rescope AC4 to the proved statement and file the Hessian as a follow-up; (ii) leave AC4 as written — #634 stays open past #641 and the Hessian is proved in a later PR against the same anchor batch.

**Close mechanics if (i) is ruled** (Red Team #652 F8 — #634 was auto-reopened on 2026-09-08 when a commit keyword closed it with AC4 unchecked): edit AC4's text in the issue body to the rescoped statement; tick it citing #641's Red Team and Gemini evidence; record the follow-up issue number for the Hessian in the body; close **by hand**, not by a commit keyword.

**Recommendation: (i) rescope.** **Ruling text:** "Decision 4: AC4 rescoped to the spectrum-at-crystal statement; Hessian filed as a follow-up; close by hand."

## 5. Decision 5 — adopt the AXIOM-2 package for its encode PR (conditioned on Decision 0)

What the encode PR would apply (package v0.6, all drafts): META-2 level saturation (the top-level `meta_axiom` object becomes a list — a ledger-shape change plus its consumer scripts; the JSON schema does not constrain it); POST-hosting (final form: non-crystal states are physically realised; almost every history starts in flight; theory-internal kill); DERIV-encoding-level (replaces AXIOM-2); DERIV-substrate-level (with the level-generic crystal definition); DERIV-holographic's `derived_from` → [AXIOM-1, DERIV-encoding-level] and its preamble (superseded by Decision 2 if ruled together); DERIV-sedenion's `derived_from` inverted to [DERIV-substrate-level, DERIV-encoding-level] — its clause is option B **in PR #651, open and unmerged, blocked on Decision 0**; re-pointing of 14 anchors, 5 principles, 7 chain texts, 4 docs and the `Hosting.lean` docstrings (DERIV-3plus1, DERIV-pati-salam and DERIV-holographic appear in both this list and Decision 2's). **Honest outcome:** six named roots (AXIOM-1, POST-hosting, the rule, META-2, the crystal definition, the state-space identification), not fewer. Nothing is derived that was not already proved; what changes is that every root is named.

**"Hold" waits for:** Decision 0 (without it the package encodes a text whose ruling has no source), and optionally the definition conversation (§7), if the beekeeper wants the substrate's definition conversed before its roots are constitutional.

**Recommendation: adopt, conditioned on Decision 0.** **Ruling text:** "Decision 5: adopt the package; encode as drafted once Decision 0 is posted."

## 6. What the encode PR(s) contain

**Shape A — one constitutional PR** (this page's proposal, overriding package §8 item 4 for the reason in §0): the package's texts (5); the flag-3 split (2) worded under the ruled reading (1) with the three names (3); the re-pointing lists and the listed sites; the guardrail docstring updates; #634 handled by hand per §4 (4).

**Shape B — two PRs** (the package's own instruction): first the package (5) with DERIV-holographic's `derived_from` re-pointed and DERIV-sedenion worded neutrally ("the substrate decomposes as two copies of an encoding octonion"); then 1–3 as a second PR that deletes DERIV-holographic and lands the split. Cost: the first PR edits an entry the second removes.

Lean owed separately and in progress: ρ as a `CDAut 4`, the two P2′ lemmas, the docstring correction that the order-3 elements fix ℓ (`Hosting.lean` §11; `substrate-hosting-definition-2026-09-07.md` §2 (e)).

## 7. What stays open after the bundle

The definition conversation (the beekeeper's step 4 of 2026-09-07), whose starting position now includes the ruled reading, the ℤ/3 datum, POST-observation's O⊆ and E, and the boundary note's §5 questions; the line-versus-bundle question (boundary note §7 Q2) if P2 is ruled; the completeness conjecture (live under P2 only); T2 in 𝕊 (§6 (ix)) and the global dim ≤ 4 deferral; H-dom and the pole corollary (§6 (viii)); #647 (the process question, on its trigger); #650 (the σ-blind status convention); flag 1's rescope price if #647 is ever ruled "yes"; the bulk-to-boundary map, which no reading supplies; and the fact that **no experiment on record distinguishes the readings of Decision 1** — the ruling is by parsimony and the discriminator stays open.
