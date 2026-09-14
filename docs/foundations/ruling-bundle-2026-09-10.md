# Ruling bundle — what is proved, what is open, and the four process questions (v0.4, 2026-09-14)

**Status:** v0.4 applies the fresh Tier-3 cycle on v0.3 (Red Team and Gemini, both REQUEST-CHANGES, 2026-09-11) and the standard the beekeeper set on 2026-09-11: *the beekeeper rules scope, priority and process, never a physical truth; anything the axioms under-determine is encoded `open` with a kill condition, never put to him as a choice; an axiom changes only because it has been proven that it must.* v0.3 met that standard on Decision 1 and broke it on Decision 5: it relabelled two unproved roots (POST-hosting, META-2) as "consequences of rulings already made" and proposed that the beekeeper's merge of this page stand as the ruling record. Both are withdrawn (§8). **Nothing on this page is ruled, and nothing is "forced by a ruling".** Every item is sorted into one of four buckets from the ledger alone — proved (cite), open (kill condition), editorial (a process question, legitimately the beekeeper's), or withdrawn — and the encode PR writes exactly that sort. Written by qbp-oppenheimer.

## 0. The sort

| Item | Bucket | Basis | Asked of the beekeeper |
|---|---|---|---|
| Composition ⇔ associative (T1); frame-maximality in 𝕆 (T2); codimension 4 (T3) | **proved** | `PROOF-associative-composition-iff`, `PROOF-quaternion-frame-maximal`, `PROOF-quaternion-frame-codim-four` | nothing |
| ρ, the ℓ-fixing order-3 automorphism, permutes the three Cayley–Dickson halves; ℍ_s meets a half in exactly ℂ_u; ℍ_s = ℂ_u ⊕ ℂ_u ℓ | **proved** | `rotAut3_*` (`CrystalHosting.lean` 1404–1480, PR #653); `quatSpan_inter_lowHalf`, `quatSpan_eq_cd_double`; the ℤ/3-torsor (exactly three halves) is still scripted, `p2_cell_torsor_check.py` | nothing |
| The level ladders: division, norm composition and alternativity hold through 𝕆 and fail at 𝕊; a non-crystal exists at 𝕊 and none below | **proved** | `PROOF-ops-division-ladder`, `PROOF-ops-norm-composition-ladder`, `PROOF-ops-alternativity-ladder`, `PROOF-normed-division-tower-existence`, `inFlight_nonempty`, `sedWitX_alternator_ne_zero` | nothing |
| DERIV-sedenion's algebraic clause (a zero divisor's left multiplication has a kernel) | **proved** | `PROOF-42zd` (PR #651; re-recorded PR #659) | nothing |
| Decision 0 — the AXIOM-1 "option B" record | **proved + open**, record corrected | PR #659 (ledger 5.7.1): the kernel clause proved; whether crystallisation is a process AXIOM-1 governs, and whether the selection clause ranges over the substrate, are two `open` questions on `AXIOM-1.kill_condition`; the old "ruled by the beekeeper" record is superseded | one line on #659 confirming that "I choose option B." (#647, 2026-09-11) was a process ratification — a question about his own words |
| Decision 1 — which copy of 𝕆 encodes a universe (P2 vs P2′) | **open** | the axioms do not select a copy; ρ permutes the halves; no discriminator on record; the kill **cannot fire today — recorded as such, not as a pass** (§1) | nothing |
| POST-observer-associativity (exclusivity) | **open** root | drafted in §2; kill: an observer exhibited outside any associative subalgebra, or a non-associative subset on which actions compose | nothing |
| POST-observation — (O⊆) and (E) | **open** root, encoded beside P2/P2′ | (E) has content only under P2′ and is empty under P2 — so it is open exactly as Decision 1 is, not applied content (§2) | nothing |
| META-2 — level saturation | **open** root (new) | the "largest" clause that was AXIOM-2's axiomatic act, now a named root with a kill (§5) | nothing |
| POST-hosting — non-crystal states are realised | **open** root | kill is theory-internal and **cannot fire**; the package said so and v0.3 dropped the sentence — restored (§5) | nothing |
| DERIV-encoding-level, DERIV-substrate-level | **proved conditional on META-2 (and POST-hosting)** | the ladders are theorems; the "last information-preserving level = 𝕆" and "first level hosting a non-crystal = 𝕊" follow from them GIVEN saturation — so they are derived principles whose `derived_from` names the open roots (§5) | nothing |
| AXIOM-2's retirement to `retired_axioms` | **derivation, not a change of axiom** | AXIOM-2's content is restated as DERIV-encoding-level; nothing it asserted is denied; the root moves to META-2, which is open where AXIOM-2 was unfalsifiable (§5) | nothing |
| Decision 2 — split DERIV-holographic into POST / theorem / INTERP | **editorial (process)** | "one kind of statement per entry" is not a ledger rule on record — it is proposed here as one (§2) | ratify the editorial rule, or not |
| Decision 3 — three names for "boundary" | **editorial (process)** | "one name per object" likewise (§3) | ratify, or not |
| Decision 4 — #634 AC4 | **scope (process)** | an unmet AC is not ticked (forced by the AC rule); **rescope vs hold is a scope call** and is the beekeeper's (§4) | rescope or hold? |
| One encode PR or two | **process** | §6 | one or two? |
| "merge = ratification"; "the hosting frame ⇒ POST-hosting"; horn 1 as a basis; "ruled by parsimony"; "Lean owed"; the two "ledger rules" cited as existing | **withdrawn** | §8 | nothing |

**The four process questions** (ratify two editorial rules; rescope or hold AC4; one PR or two) are the only things this page puts to the beekeeper, and none of them is a physical truth. Everything else is encoded as proved or open; the gate (`scripts/root_audit.py`, PR #658) reads the result and hard-fails any root that is neither.

## 1. Decision 1 — P2 or P2′ (the copy of 𝕆): open

Facts on master: the crystal's algebra ℍ_s = span{1, ℓ, U, ℓU} contains ℓ and is not inside the Cayley–Dickson half; it meets the half in exactly ℂ_u = span{1, U} and is the doubling of that ℂ by ℓ. The ℓ-fixing order-3 automorphism ρ carries the half to a different half, preserves the vacuum set, and fixes each ℍ_s as a set, so the three ℂ's in ℍ_s are indistinguishable from inside the observer's algebra. ρ is Lean (`rotAut3_ell`, `rotAut3_pow_three`, `rotAut3_ne_id`, `rotAut3_moves_lowHalf`, `rotAut3_hosting_equivariant`; PR #653); that there are exactly three halves (the ℤ/3-torsor) remains scripted (`p2_cell_torsor_check.py`).

| | P2 as a line | P2 as the bundle | P2′ |
|---|---|---|---|
| New datum a universe carries | a point of ℂP² (4 continuous parameters) | **none** — the boundary is the canonical module ℍ_s^⊥ ≅ ℍ_s³ with its cone of admissible lines; no line chosen | a choice among three halves (1 discrete) |
| Unproved links | the doubled frame is an octonion ⊃ ℍ_s; completeness of the family (conjecture) | the same two | none |
| Observation | with (O⊆), selects no ℂ | selects no ℂ | selects a ℂ under (O⊆) — the *observed* one only under (E) |
| Fits | DERIV-holographic literal; "inter-cell" natural | as P2 | DERIV-sedenion as the package rewrote it; strained against "inter-cell" (the half is global) |
| Cost if adopted | flag 3 only | flag 3 only | DERIV-holographic's "4D gap" → 6-dim; T2 stops describing the observer's algebra; DERIV-3plus1's route severed |
| Status | **open** | **open** | **open** — no experiment on record distinguishes the three; no theorem selects one |

**Encoding.** INTERP-holographic-boundary carries the reading-independent content (there is an encoding octonion; the gap is the complement of the observer's algebra inside it; the seam is the zero-divisor locus) with `decision_state: open` and names P2 and P2′ as hypotheses. DERIV-sedenion's first clause is worded neutrally ("two copies of an octonion"). **Kill condition, in hosting §4's form:** *this kill cannot fire today — recorded as such, not as a pass.* What would fire or discharge it: a defining property for the encoding stated as an object (if "a Cayley–Dickson half", P2′ becomes a theorem; if "contains the observer's algebra", P2 does); the encoding *map* (a map forces its domain); or an observable distinguishing the readings — none on record. The first two are stipulations someone would write, not discoveries; the page says so rather than counting them as discriminators.

## 2. Decision 2 — the flag-3 split: an editorial proposal, with two open roots inside it

DERIV-holographic today: "Observers require associativity. The largest associative subalgebra of O is H (dim 4). The 4D gap is the holographic boundary." — one entry carrying a postulate, a theorem and an interpretation. Proved on master: T1, T2 (in 𝕆 only; whether any associative subalgebra of 𝕊 properly contains ℍ_s is open, boundary note §6 (ix)), T3.

**The editorial rule proposed:** *one kind of statement per ledger entry* (postulate / theorem / interpretation). It is not a rule the ledger has on record (a repo-wide search finds it only on this page); it is put to the beekeeper as **process**, which is his. If ratified, the split below is its first application; if not, the split still goes into the encode PR as this author's editorial choice, revertible without touching any claim.

| Entry | Text (drafted; the encode script is the source) | Bucket |
|---|---|---|
| **POST-observer-associativity** | "An observer is a subset of 𝕊 on which its actions compose; by the composition theorem such a subset is associative, and — if it lies inside an octonion — inside one ℍ by frame-maximality (in 𝕊 at large this is open). Under the hosting definition the observer's ℍ is the crystal's ℍ_s. Exclusivity — no observer lives outside the hosted algebra — is the postulate's content." | **open** root; kill: an observer exhibited outside any associative subalgebra, or a non-associative subset on which actions compose |
| **POST-observation** | "(O⊆) What an observer can access is contained in what is encoded in its encoding octonion. (E) The electromagnetic ℂ of DERIV-observation is the ℂ selected by that encoding. Under P2′ (E) has content (the selected ℂ is ℂ_u); under P2 no ℂ is selected and DERIV-observation's ℂ is EM's own; the reading is open." | **open** root, **beside P2/P2′** (Red Team v0.3 F5: (E) is empty under P2, so it cannot be applied content while Decision 1 is open); kill: an observable requiring access outside the encoding (O⊆ failing), or an EM ℂ shown distinct from the encoding-selected ℂ (E failing) |
| **DERIV-holographic-theorem** | "Quaternion frames span{1,u,v,uv} are associative subalgebras of 𝕆; no associative subalgebra of 𝕆 properly contains one (frame-relative; the global bound is deferred); the codimension of ℍ in 𝕆 is 4." | **proved** (T1–T3); reading-independent |
| **INTERP-holographic-boundary** | common content + the open hypothesis pair (§1) | **open** (`provenance_kind: philosophy`, `decision_state: open`) |

**Re-pointing** (boundary note §5, completed by the v0.1 Red Team): DERIV-3plus1 → POST-observer-associativity + theorem (its 1 + 3 route must be re-argued if P2′ is ever established); DERIV-observation → POST-observation + theorem; DERIV-pati-salam → theorem; DERIV-arrow → POST-observer-associativity + INTERP + AXIOM-1; DERIV-constants → POST-observer-associativity + INTERP; anchors PROOF-3gen → theorem, PRED-gw-em and PRED-revival-exact → POST + INTERP. Other sites citing the old entry: `CHAIN-born-to-revival.source_ids`; the four flag-3 PROOF anchors' descriptions ("DERIV-holographic, theorem part n"); PROOF-crystal-hosts-quaternion's "NOT claimed" note; `CONJ-condensed-math-for-transition-state` and `INSIGHT-condensed-math-deferred` (`converges_with`). Guardrail docstrings saying "NOT identified with the observer's ℍ … pending flag 3", updated in the same PR: `proofs/QBP/Substrate/Hosting.lean` 73–75, 288–289, **586–589** (566–568, cited in v0.3, is the #635 rule docstring — wrong site); `proofs/QBP/Foundations/CrystalHosting.lean` 82–83, 555–557; `proofs/QBP/Substrate/README.md` 26; `proofs/QBP/Foundations/HolographicSubalgebra.lean` 9; `docs/foundations/substrate-hosting-definition-2026-09-07.md` status line and §3 (the guardrail); its §2(e) is a separate item — the ρ docstring correction, already landed in #653.

## 3. Decision 3 — three names for "boundary": editorial

| Name | Object | Dim | Parent (after the split) |
|---|---|---|---|
| encoding octonion | the octonion the boundary encoding refers to (a Cayley–Dickson half under P2′; an octonion ⊃ ℍ_s under P2) | 8 | DERIV-encoding-level |
| holographic gap | the complement of the observer's algebra inside its encoding | **undetermined while Decision 1 is open** (6 under P2′, 4 under P2) | INTERP-holographic-boundary |
| seam | the zero-divisor locus in the substrate, between universes | 11 | DERIV-sedenion |

Three objects with three parents and dimensions differing by up to a factor of two cannot honestly share one word; qbp-architecture flagged the overload on #643. **The editorial rule proposed:** *one name per object*, put to the beekeeper as process (as in §2). "Boundary" bare is then forbidden in ledger entries and Lean docstrings.

## 4. Decision 4 — #634 AC4: a scope question, put plainly

AC4 asked for the transverse Hessian 4r²·I on the 6-dim normal space (or the {1−δ, 1, 1+δ} multiplicities). Delivered on master: the spectrum *at* the crystal — −L_s² = N(s)·id ⇔ vacuum, the unique eigenvalue, the exact first-order alternator expansion. Both reviewers on #641 marked it PARTIAL. **Forced by the AC rule:** an unmet AC is not ticked; AC4 stays `- [ ]` and #634 stays open. **Scope, the beekeeper's:** (i) rescope AC4 to the proved statement and file the Hessian as its own issue, or (ii) leave AC4 as written and prove the Hessian later against the same anchor batch. Close mechanics if (i): edit AC4's text, tick it citing #641's two reviews, record the follow-up issue, close by hand (never by a commit keyword — #634 was auto-reopened on 2026-09-08 for exactly that).

## 5. Decision 5 — the AXIOM-2 package: re-sorted

v0.3 filed the package as "consequences of rulings already made". The v0.3 Red Team showed the cites do not hold: the 2026-09-07 hosting comment is a working definition and contains none of POST-hosting's content; the horn-1 → POST-hosting route was withdrawn as circular by this project's own confirmer (package §9c); META-2 has zero ledger occurrences and the package itself calls it "the one new epistemic root". Re-sorted:

| Package item | Bucket | Text / basis |
|---|---|---|
| **META-2 — level saturation** | **open** root (new) | "A structural level sits exactly at the bound its constraint sets; no slack. Domain: Cayley–Dickson levels only. It does not select states, copies, orientations, or signs." Kill: a Cayley–Dickson level shown to sit strictly inside its constraint's bound — a crystal-hosting division or alternative structure above 𝕆, or a non-crystal below 𝕊 — either would break saturation and the two level principles with it. |
| **POST-hosting** | **open** root | "The state sphere at the substrate level carries an in-flight region V > 0 of positive measure, and almost every history starts in it." Kill (theory-internal): a substrate level at which V ≡ 0. **It cannot fire:** the kill is the negation of the postulate and no observable reaches it (observers live in crystals; FLAG-seam-dynamics-open is incoherent) — *"a structural claim with a stated collapse condition, not a falsifiable one"* (package). Recorded as such, not as a pass. |
| **DERIV-encoding-level** | **proved conditional on META-2** | the ladders (theorems) + saturation ⇒ the encoding sits at the last information-preserving level, 𝕆. `derived_from: [AXIOM-1, META-2]`; supersedes AXIOM-2 as the root of that statement. |
| **DERIV-substrate-level** | **proved conditional on META-2 and POST-hosting** | the level-generic crystal definition (alternator vanishes) + the ladders ⇒ the substrate is the first level hosting a non-crystal, 𝕊. `derived_from: [POST-hosting, META-2]`. |
| **AXIOM-2 → `retired_axioms`** | **derivation, not a change of axiom** | nothing AXIOM-2 asserted is denied; its content is now DERIV-encoding-level and its "largest" clause is META-2's. The root count does not fall (AXIOM-2 → META-2); what improves is that META-2 carries a kill where AXIOM-2 was unfalsifiable. |
| DERIV-sedenion's `derived_from` → [DERIV-substrate-level, DERIV-encoding-level]; first clause neutral | **follows the retirement** | the entry's derivation now names the level principles; its algebraic clause is proved (PR #651/#659); the scope of AXIOM-1's selection clause over 𝕊 is `open` on AXIOM-1 (PR #659, question 2), with DERIV-encoding-level as the discharge route |
| Re-pointing of 14 anchors, 5 principles, 7 chain texts, 4 docs, `Hosting.lean` docstrings | **editorial consequence of the retirement** | mechanical; listed in the encode script |

**Honest root list after the encode** (the D6 report's expectation reconciled): AXIOM-1 (`open`, two questions, #659); META-1 (registered, #655); META-2 (`open`); POST-hosting (`open`, kill cannot fire); POST-observer-associativity (`open`); POST-observation (`open`); the rule (#635), the crystal definition and the state-space identification live inside DERIV-substrate-level and PROOF-substrate-hosting-definition under non-root prefixes and are outside the root gate's reach until encoded as roots — the gate says so. Not fewer roots than before; every one of them named, and every one either registered or carrying a kill.

## 6. What the encode PR contains

Everything in §0's proved rows as theorems (already anchored); every open root with `decision_state: open` and a `kill_condition` list (one entry per open question); INTERP with `provenance_kind: philosophy`, `decision_state: open`; the two conditional derivations with `derived_from` naming their open roots; AXIOM-2 and DERIV-holographic to the retired lists with their records; the re-pointing; the guardrail docstrings. **No entry carries a `ruling` field citing this page or its merge.** The gate (#658) reads the result: every root sorts into bucket 3 or is registered; nothing is FORCED by fiat.

**One PR or two** — the beekeeper's process call. The package's own §8 item 4 said two (package first, then the split); this page's reason for one is that the package edits DERIV-holographic's `derived_from` and words DERIV-sedenion in a way the split immediately rewrites — two PRs edit an entry the second removes. Default if unanswered: one PR (`scripts/encode_ruling_bundle.py`, branch `research/encode-bundle`, writing through the #654 confined-write helper).

## 7. What stays open after the bundle

The definition conversation (the beekeeper's step 4 of 2026-09-07), whose starting position now includes the open hypothesis pair, the ℤ/3 datum, POST-observation's (O⊆) and (E), and the boundary note's §5 questions; the line-versus-bundle question inside P2; the completeness conjecture (live under P2 only); T2 in 𝕊 (§6 (ix)) and the global dim ≤ 4 deferral; H-dom and the pole corollary (§6 (viii)); #647 (AXIOM-1's process question, derived at trigger time, never ruled); #650 (the σ-blind status convention); the bulk-to-boundary map, which no reading supplies; and the fact that **no experiment on record distinguishes the readings of Decision 1** — the kill cannot fire and the ledger says so.

## 8. Withdrawn (the record of v0.1–v0.3)

- **"The beekeeper's merge of this page is the record"** (v0.3) — withdrawn: layer-1 entries need a source or an `open` state; a merge is neither. Nothing is applied on the strength of a merge.
- **"The hosting frame ⇒ POST-hosting"; "horn 1" as a basis** (v0.3) — withdrawn: the frame is a working definition without POST-hosting's content; the horn-1 route was withdrawn as circular by the confirmer (package §9c).
- **Decision 5 as "consequence"; META-2 omitted from §0** (v0.3) — withdrawn: both are open roots (§5).
- **"One kind of statement per entry" / "one name per object" as "the ledger's own rules"** (v0.3) — restated as editorial proposals put to the beekeeper as process (§2, §3).
- **Decision 4 as "bookkeeping, not a choice"** (v0.3) — restated as a scope question (§4).
- **"Ruled by parsimony"; the "Recommended" column** (v0.1–v0.3) — gone: nothing is recommended or ruled.
- **"Lean owed … not yet a PR"** (v0.2–v0.3) — false since #653 merged (this branch's ancestor); corrected in §1.
- **`Hosting.lean` 566–568; `CONJ-condensed-math`** — wrong site and wrong id; corrected in §2.
- **Decision 0 as "already ruled, nothing asked"** (v0.3) — replaced by the PR #659 record: proved + open, with one question to the beekeeper about his own words.

The prior texts are in git history (`484c4e1` v0.3, `6368045` v0.2, `8cb713e` v0.1) and the review comments on PR #652.
