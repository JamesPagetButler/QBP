# Demoting AXIOM-2 — proposal package from the qbp-oppenheimer × Gemini conversation (v0.5, 2026-09-09)

**Status:** conversation outcome under the Conversation MO. **Confirmer (Red Team round 4): CONFIRMED-ON-CONDITIONS**, six conditions — v0.2 applied all six; **v0.3 added rounds 5–6** (beekeeper-directed: arrow-of-time rooting; precision observables) — §9; **v0.5 records the beekeeper's ruling of 2026-09-09: AXIOM-1 option B** (AXIOM-1 untouched; DERIV-sedenion algebraic; flag 1 dissolved as a category error; the real question — is crystallisation a physical process to which AXIOM-1 applies? — filed as a trigger issue that fires when the ledger has the rule written as dynamics). **v0.4 applied the confirmer's delta pass** (`axiom2-demotion-confirmer-delta-review-2026-09-09.md`: §9a and §9b CONFIRMED-ON-CONDITIONS, all applied; **§9c NOT CONFIRMED as "POST-hosting is not a root"** — the kill is dead, the root stays; the driver's derivation claim was circular and is withdrawn) (§10 lists each with where it landed). Gate §3 as assessed by the confirmer: (1) met; (2) partial → addressed by §2a/§4a; (3) partial → addressed by §3 DERIV-substrate-level; (4) met with the AXIOM-1 caveat now stated in §3; (5) partial → addressed by §2a/§3/§4a. Constitutional texts below are **drafts for the beekeeper**; nothing in the ledger is edited by this document. Transcript: driver summary `axiom2-demotion-conversation-transcript-2026-09-09.md`; **verbatim turns** `axiom2-demotion-conversation-verbatim-2026-09-09.md` (Gemini session turns 50–55, thinking included). Beekeeper brief: demote AXIOM-2?; refine "use the largest structure available"; downstream impacts and re-proofs traced through the CTH, Lean and Agda; rephrase "fewer axioms + more derived work = more rigorous" as a wisdom.

## 0. The result in one table

| Question | Answer | Basis |
|---|---|---|
| Can AXIOM-2 be derived? | **Yes — as a level statement**: the encoding is the last Cayley–Dickson level where AXIOM-1 holds (8 = 𝕆). Tower-relative; the Hurwitz classification is not used. | PROOF-ops-division-ladder, PROOF-normed-division-tower-existence (Lean) |
| Does the axiom count drop? | **No — and honestly it is a split, not a demotion.** The derivation needs a physical postulate the ledger never wrote down — POST-hosting ("physical states exist that are not crystals") — and a level-selection rule, META-2, which carries exactly the "largest" clause that was AXIOM-2's axiomatic act. Roots after: AXIOM-1, POST-hosting, META-2, the level-generic crystal definition, the CD tower (§2a). What changes is the *kind* of root: an unexplained structural choice becomes a theory-internal claim with a stated kill (which cannot yet fire, §3). | rounds 2–3; confirmer #5 |
| The refined principle | **META-2, level saturation:** a structural level sits exactly at the bound its constraint sets, no slack. Domain: Cayley–Dickson *levels* only — not states (the ensemble is MaxEnt, not saturation), not copies (ℂP² of encodings), not orientation. | round 2 (A), round 3 (2) |
| The derivation direction | **Flips.** Today: AXIOM-2 (𝕆) → double → DERIV-sedenion (𝕊). Proposed: POST-hosting forces the substrate up to 16 (crystallisation needs a state that is not a crystal; **with "crystal" defined as alternator-flat** every state of an alternative algebra is a crystal); AXIOM-1 forces the encoding down to 8; DERIV-sedenion is derived from both. | PROOF-ops-alternativity-ladder ✓ℝℂℍ𝕆 ✗𝕊 (`CDLifting.assoc_diag_left`); PROOF-alternator-vanishes-iff-commute (𝕊 only — see §3); PROOF-42zd |
| Flag 1 (DERIV-sedenion vs AXIOM-1) | **RULED 2026-09-09: option B.** AXIOM-1 untouched; DERIV-sedenion's clause becomes the algebraic fact (a multiplication map with a kernel is not a process); flag 1 dissolved as a category error; the question "is crystallisation a physical process AXIOM-1 governs?" is deferred to a trigger issue (§8 item 8) that fires when the rule (#635) is written as a flow. Options as they were put: (A) rescope AXIOM-1 to the encoding — a content change with a 22-anchor blast radius (§4a); or (B) leave AXIOM-1 untouched and rewrite DERIV-sedenion algebraically ("the multiplication map is non-injective at seams", L_a has a kernel for a zero divisor a, PROOF-42zd) — no *process* is asserted, the ledger has no autonomous dynamics (KILLED-locale-forcing-route), and flag 1 dissolves as a category error. The confirmer put (B) on the table; the dyad had not. | AXIOM-1 text; PROOF-42zd; confirmer #3 |
| Downstream | AXIOM-2 side: 14 anchors + 5 derived principles + **7** chain texts + 4 docs and the `Hosting.lean` docstrings **re-point**; 2 derived principles **re-derive**; 31 anchors **unaffected**. AXIOM-1 side (only under option A): 22 direct citers + 5 principles triaged in §4a — 7 sit in the transition/vacuum regime and need a re-read. Lean owed: the level-generic crystal definition as an anchor statement and a one-line corollary at 𝕆 (`assoc_diag_left` already says it); Agda: nothing. | scripted triage over ledger v5_3.v0.3 (287 anchors); confirmer #9, #10 |
| The wisdom | **"Rigor is few roots and long chains."** | round 2–3 |
| Empirical face of the split (rounds 5–6) | **one unpredicted rate.** POST-hosting has no observable and only a theory-internal kill; the split's entire empirical content is DERIV-crystallisation-asymptotic's α̇ / Ġ, for which the ledger predicts no number. g-2 and the electron moment bound unnamed seam terms; they test nothing the split asserts. | §9; confirmer delta C5 |

## 1. AXIOM-2 taken apart

| Clause | Kind | Status |
|---|---|---|
| "there is a boundary encoding" | premise | the holographic picture; no QBP-internal map (triangle-bootstrap §5) |
| "…uses a normed division algebra" | half-derived | AXIOM-1 selects division; "normed" enters through the tower |
| "…the largest is 𝕆 (dim 8)" | theorem | Lean: ℝ, ℂ, ℍ, 𝕆 compose, 𝕊 does not (PROOF-normed-division-tower-existence, existence + termination); classification "only four" = PROOF-hurwitz, citation |
| "…uses *the largest*" | the axiomatic act | the maximality choice — what META-2 replaces |
| "the encoding" is one copy | silent | the P2 / P2′ question of the boundary note — **untouched by this package** |

## 2. The derivation (D2) and its premises, counted honestly

| Premise | Kind (criterion: physical postulate / epistemic principle / definition) | Counts as an axiom? | Why |
|---|---|---|---|
| AXIOM-1 — information is preserved; selects division algebras | physical postulate | **yes** | testable demand on the encoding; scope clarified below, sentence unchanged |
| Cayley–Dickson doubling as the generator of the tower | definition | no | the framework's phase space; not derived (KILLED-locale-forcing-route, Prop 12 ratified) |
| POST-hosting — physical states exist that are not crystals | physical postulate (**new to the ledger; was implicit in the hosting frame**) | **yes** | it does the work of "level ≥ 16"; without a kill it would be a definition doing physical work |
| META-2 — level saturation | epistemic principle **that selects a level** | **contested — counted in §2a** | it carries the "largest" clause that was AXIOM-2's axiomatic act (confirmer #5); META-1 selects nothing, META-2 does |
| Level-generic definition of "crystal" (alternator-flat; equivalently L_s² scalar) | definition **doing physical work** | **yes, as a root (§2a)** | the derivation's key step "alternative ⇒ every state is a crystal" holds under this definition and **fails** under the hosting doc's primary CD-commutator form (confirmer #1) |

Count: **2 physical axioms before (AXIOM-1, AXIOM-2), 2 after (AXIOM-1, POST-hosting)** — but see §2a: by the package's own wisdom the honest root count *rises* until META-2 and the crystal definition are either defended as non-roots or accepted as roots. The gain is not fewer roots; it is that every root is now named, and the second physical one is a theory-internal claim with a stated kill rather than a structural preference with none.

### 2a. Honest root count (confirmer condition 5)

| Root after the package | Kind | Counted? | Defence or admission |
|---|---|---|---|
| AXIOM-1 | physical | yes | unchanged (option B) or rescoped (option A) |
| POST-hosting | physical | yes | new; kill cannot yet fire (§3) |
| META-2 level saturation | selection rule | **yes** | it selects a level; "largest" moved here from AXIOM-2 — **the demotion is a split**: maximality → META-2, type → derived, "there is a boundary encoding" → the premise that DERIV-holographic still carries (unplaced; it is the interpretation I of the boundary note) |
| crystal := alternator-flat (level-generic) | definition doing physical work | **yes** | the CD-commutator form of the hosting doc diverges from it at 𝕆 (s = i + jℓ ∈ 𝕆 has T_s ≡ 0 but [i, j] = 2k ≠ 0); the alternator form is the one under which "alternative ⇒ all crystals" holds. Argument that it is forced: the crystal condition is *defined* in Lean by `IsVacuum` ⇔ alternator-flat (`isVacuum_iff_alternator_flat`) and the CD-commutator form is proved equivalent **at 𝕊 only**; the alternator is the level-generic object (`assoc s s x`), the commutator is not. So the alternator form is the primary definition and the commutator its 𝕊-specific computation — but that choice must be *stated*, and it is now. |
| the Cayley–Dickson tower | definition (phase space) | no | not doing physical work; the language |

Roots: **4 counted** (2 physical, 1 selection rule, 1 definition) versus 2 physical axioms before with the selection rule and the definition *hidden*. Fewer roots is not what this package delivers; named roots is.

**Why MaxEnt alone fails (round 2 A).** "Populate the maximal state space consistent with the constraints" bounds the encoding from above (AXIOM-1 ⇒ ≤ 8) but the substrate only from below (crystallisation ⇒ ≥ 16); the tower is infinite, so maximality picks no substrate level. What stops at 16 is minimality. One principle covering both: **saturate the bound** — hence META-2, and hence its restriction to levels: for *states* the ruled ensemble is MaxEnt (horn 1), which is the opposite of saturation (saturating a bound in phase space is T = 0).

## 3. Draft ledger texts (constitutional; for the beekeeper; not applied)

| Entry | Draft text | derived_from / anchors |
|---|---|---|
| **AXIOM-1 — option A: rescope** (a **content change**, not a clarification: "no physical process" → "no physical process in the encoding"; crystallisation becomes a process the axiom exempts) | "No physical process destroys information. Selects division algebras (no zero divisors). — Scope: the encoding. The second sentence already uses this axiom to select the encoding algebra; the substrate, where crystallisation runs, is where that selection fails by construction (PROOF-42zd; PROOF-ops-alternativity-ladder). That failure is DERIV-sedenion's content, not a violation." Price: §4a (22 direct citers, 7 in the transition regime). Gemini's round-2 model was a *different sentence*; round 3 accepted the line — that disagreement is now named, not smoothed. | — |
| **AXIOM-1 — option B: leave untouched** (confirmer's alternative; **cheaper**) | AXIOM-1 unchanged. DERIV-sedenion's "information CAN be destroyed" is rewritten as the algebraic statement it always was: "left multiplication by a zero divisor is non-injective (PROOF-42zd)". No *process* is asserted — the ledger has no autonomous algebraic dynamics (KILLED-locale-forcing-route; NoAutonomousDynamics.lean) — so "no physical process destroys information" is not contradicted by a linear map having a kernel. Flag 1 dissolves as a category error. Price: none to AXIOM-1's citers; DERIV-sedenion text only. **Recommended — and RULED (beekeeper, 2026-09-09).** Option A stays on record as the edit that becomes due if the trigger issue is later ruled "yes". | KILLED-locale-forcing-route |
| **POST-hosting** (new) | "Physical states exist that are not crystals: the in-flight region V > 0 of the state sphere is physically populated, and a universe's history includes a transition from it to the vacuum manifold V = 0. **Kill (theory-internal):** if every physically realised state is a crystal, the substrate need not be non-alternative, level 8 suffices, and the substrate collapses onto the encoding. **This kill cannot fire until an observable for V > 0 is named** (FLAG-seam-dynamics-open; observers live in crystals, so an in-flight state has no observer reading by construction) — recorded as such, not as a pass." Not yet a falsifiable claim; a structural one with a stated collapse condition. | PROOF-substrate-hosting-definition, PROOF-delta-landscape-descent; confirmer #4 |
| **META-2 — level saturation** (new, beside META-1) | "A structural level sits exactly at the bound its constraint sets; no slack. Domain: Cayley–Dickson levels only. It does not select states (the ensemble is MaxEnt), copies (the ℂP² of encodings), orientations, or signs." | — |
| **DERIV-encoding-level** (replaces AXIOM-2) | "The encoding is the Cayley–Dickson level below the first failure of AXIOM-1's selection: 𝕆 (dim 8) — division, norm composition and alternativity all hold through 𝕆 and all fail at 𝕊. Tower-relative — 'largest in the Cayley–Dickson sequence'; the classification 'only four normed division algebras exist' (PROOF-hurwitz) is not used." ("Level below the first failure" rather than "last level where it holds" — the latter needs a monotonicity lemma the Lean does not carry; the former needs only the ladders.) | [AXIOM-1, META-2]; PROOF-ops-division-ladder, PROOF-ops-norm-composition-ladder, PROOF-ops-alternativity-ladder, PROOF-normed-division-tower-existence; confirmer #10 |
| **DERIV-substrate-level** (new) | "**Definition (level-generic):** a state s is a crystal iff its left alternator vanishes, `assoc s s x = 0` for all x (equivalently `L_s²` is scalar). At 𝕊 this is equivalent to the Cayley–Dickson components of s commuting, V = ‖[a, b]‖² = 0 (PROOF-alternator-vanishes-iff-commute) — **an equivalence that holds at 𝕊 only**: the commutator form is the 𝕊-specific computation, not the definition, and diverges at 𝕆 (s = i + jℓ has `assoc s s x = 0` for all x by `assoc_diag_left` while [i, j] ≠ 0). **Statement:** the substrate is the first Cayley–Dickson level at which a non-crystal exists: 𝕊 (dim 16). In every alternative algebra `assoc s s x = 0` for all s, x, so every state is a crystal (levels ≤ 3: `CDLifting.assoc_diag_left` at 𝕆, associativity below); at 𝕊 a non-crystal exists (`sedWitX_alternator_ne_zero`, `inFlight_nonempty`)." Lean owed: none for the 𝕆 case (`assoc_diag_left` is the statement); the anchor must cite it *as* the 𝕆 case and carry the definition. | [POST-hosting, META-2, crystal-definition]; PROOF-ops-alternativity-ladder, `CDLifting.assoc_diag_left`, `Alternator.sedWitX_alternator_ne_zero`, `Hosting.inFlight_nonempty`; confirmer #1, #11 |
| **DERIV-sedenion** (inverted) | "𝕊 = 𝕆 ⊕ 𝕆ℓ: the substrate decomposes as two copies of the encoding. Its zero-divisor locus is where AXIOM-1's selection fails — seams where **the multiplication map is non-injective** (left multiplication by a zero divisor has a kernel, PROOF-42zd). Flexible topology at the seams." Under option B this algebraic wording replaces "information CAN be destroyed" and flag 1 is a category error; under option A the old wording may stand as a scoped statement. | [DERIV-substrate-level, DERIV-encoding-level] (was [AXIOM-2]) |
| **DERIV-holographic** | text unchanged (its own re-statement is #643 §5); derived_from [AXIOM-1, AXIOM-2] → [AXIOM-1, DERIV-encoding-level] | — |

**Flag 1 under the package.** Option A: the contradiction stops because the axiom is scoped to the encoding — a rescope, priced in §4a. Option B: it never was a contradiction — a linear map with a kernel is not a "physical process", and the ledger asserts no process at the seams — a category error, dissolved. Gemini's round-3 "destroyed ≠ scrambled, therefore a resolution not a relabel" is a phase-space-volume restatement of "kernel" (**a relabel**, per the confirmer), exact and not an observable in the measurement sense; what crosses a seam stays FLAG-seam-dynamics-open under either option.

## 4. Downstream impact, computed

| Class | Count | Items |
|---|---|---|
| Re-point only (cite AXIOM-2 as the fact "encoding = 𝕆"; none uses maximality as a premise) | 14 anchors | PROOF-42zd, PROOF-g2, PROOF-cl6, PROOF-3gen, PROOF-quat-closure, PROOF-fano (killed), MEAS-alpha, OBS-tenfold-division, PROOF-majorana-charge, PRED-no-dm-particle, FLAG-inflation, OBS-desi-4thirds, PROOF-stelle-no-linear, KILLED-f4-info-theoretic-justification |
| Re-point (derived_from) | 5 principles | DERIV-holographic, DERIV-3plus1, DERIV-pati-salam, DERIV-crystallisation-asymptotic, DERIV-sedenion |
| Re-derive | 2 principles | DERIV-sedenion (direction inverted, text above); DERIV-holographic (preamble: the boundary is derived, not axiomatic) |
| Chain texts | **7** (not 9: CHAIN-zd-to-lambda and CHAIN-born-to-revival carry no "Axioms →" text — confirmer #9) | CHAIN-axioms-to-{gauge, alpha, kramers, honeycomb, z2gauge}, CHAIN-sedenion-to-gw, CHAIN-ncg-to-proton: "Axioms →" becomes "AXIOM-1 + POST-hosting + META-2 → DERIV-encoding-level →" |
| Docs and docstrings naming AXIOM-2 | 4 docs + `Hosting.lean` docstrings | to re-point in the encode PR (confirmer #9) |
| Unaffected | 31 anchors | cite only a derived principle; inherit the re-pointing |
| Lean owed | a definition + a citation, no new proof | the level-generic crystal definition stated in DERIV-substrate-level; `assoc_diag_left` cited as the 𝕆 case; the ladders (division, norm-composition, alternativity), tower existence, alternator ⇔ commute (𝕊), 42 ZD are on master |
| Agda owed | 0 | the S³ H-space and baryon witnesses are unaffected |
| Pre-existing gap, neither opened nor closed | 1 | PROOF-born's "unique multiplicative positive-definite norm on ℍ" is uniqueness *internal* to ℍ, a citation the Lean does not carry (PROOF-hurwitz-quat proves only composition); 10 anchors cite "Hurwitz" by name, all as shorthand for the composition property |

### 4a. AXIOM-1 rescope blast radius (only under option A; confirmer condition 2)

22 anchors and 5 derived principles cite AXIOM-1 directly. Classified by the regime in which they *use* it:

| Class | Count | Items | Why |
|---|---|---|---|
| Encoding regime — unaffected by a rescope to the encoding | 15 anchors + 4 principles | PROOF-hurwitz, PROOF-born, MEAS-alpha, PROOF-quat-closure, OBS-tenfold-division, PROOF-majorana-charge, PRED-no-dm-particle, FLAG-inflation, OBS-desi-4thirds (seam *rate* enters a crystal-side equation of state), PRED-correlated-alpha-G, PROOF-stelle-no-linear, FIT-zeta-modulated-profile, DERIV-vaidya-accreting-horizon-spacelike, DERIV-hubble-half-entropy-factor (horizons of an encoded universe); DERIV-holographic, DERIV-arrow, DERIV-born, DERIV-pati-salam | they apply information preservation to the norm, the spectral action, horizons, or measurement inside a crystal |
| Transition / vacuum regime — **re-read required** | 7 anchors + 1 principle | KILLED-f4-info-theoretic-justification (already killed for using AXIOM-1 in the vacuum — the rescope *confirms* the kill), PROOF-fano-choice-information (crystallisation threshold as information cost), REF-ecker-grumiller-spacetime-crystal, CONJ-condensed-math-for-transition-state, INSIGHT-condensed-math-deferred, INSIGHT-locale-condensed-chain, INSIGHT-threshold-transition-new-stable-state; DERIV-crystallisation-asymptotic ("time IS the crystallisation") | they invoke AXIOM-1 while describing the in-flight regime, where option A says it no longer applies; each needs a one-line ruling: re-point to POST-hosting / DERIV-substrate-level, or keep with the loss made explicit |

Under option B this table is moot: AXIOM-1's text and scope are untouched.

## 5. What the package does not decide

- **The copy.** "The last information-preserving level" picks the *type* 𝕆, not which octonion subalgebra of 𝕊 encodes a universe. P2 (an octonion containing the crystal's ℍ; a ℂP² of them) versus P2′ (the Cayley–Dickson cell, meeting the crystal's ℍ in a ℂ) is exactly as open as in the boundary note.
- **The map.** Nothing here supplies the bulk-to-boundary map; "holographic" remains a name.

## 6. Pre-mortems (NOT independently sealed — confirmer #6: the driver's seed was in the same prompt both times, so anchoring cannot be excluded; treat the agreement as weak evidence)

| Author | Retrospective: the package was reverted because… | Lesson already in the package |
|---|---|---|
| qbp-oppenheimer (in-prompt, round 3) | META-2 was applied to a level where the constraint was a preference, not a bound (the ensemble), and "saturation" arguments accreted for things that were choices | META-2's domain restriction to levels; states are MaxEnt |
| Gemini (round 3, after reading the driver's; round 1's reproduced the driver's level-32 seed) | later physics required the *encoding* to be ℍ, not 𝕆 (a strict associativity requirement at the boundary); AXIOM-1 + META-2 had forced the maximal level | the same: META-2 is a theory-construction rule, not a law — a new constraint moves the bound, and DERIV-encoding-level's *value* changes while the rule stands |

Both locate the fragility in META-2; both fixes are the domain restriction written into it.

## 7. The wisdom

> **Rigor is few roots and long chains.**
> Every derivation moves a doubt from a leaf to a root, where it can be tested once. Fewer axioms is not the aim; fewer roots bearing more weight is. A definition that does physical work is a root in disguise — count it.

Pressure-tested against: (F1) one axiom hiding ten assumptions in a definition (fewer axioms, less rigor); (F2) a derivation inherits the provisionality of its premises (META-1) — it adds traceability, not certainty; (F3) adding an axiom can raise rigor when it turns an unfalsifiable definition into a falsifiable claim — which is exactly what POST-hosting does to the hosting frame. The beekeeper's raw statement ("fewer axioms and more derived work is more rigorous") is false as a rule and true as a lens.

## 8. Next steps, with reasons

1. **Confirmer (Red Team round 4)** — done: CONFIRMED-ON-CONDITIONS; all six conditions applied in v0.2 (§10). *Because* rounds 1 and 3 both showed fast agreement and the count claim reversed between rounds — and the confirmer found the two load-bearing gaps (crystal definition; AXIOM-1 blast radius) the dyad had not.
2. **Beekeeper ruling** on: (i) AXIOM-1 option A (rescope, priced) or option B (untouched, DERIV-sedenion algebraic — recommended); (ii) adopt POST-hosting, META-2 (schema note: `meta_axiom` is a single object today, so META-2 needs a list), DERIV-encoding-level, DERIV-substrate-level with the crystal definition, DERIV-sedenion inverted, the re-pointing; (iii) whether the honest outcome "a split into named roots, not fewer roots" is what the beekeeper wants recorded. *Because* every text above is a layer-1 edit.
3. **Encode** on ratification: one PR that applies the ledger texts, re-points the 14 + 5 + 9, and adds the AXIOM-1 clarification; no Lean. *Because* the derivation is already fully anchored.
4. **Do not** fold P2 / P2′ or the flag-3 split into this PR. *Because* they are independent rulings and the package is orthogonal to the copy question.
5. **Rounds 5–6 (run on the beekeeper's direction, 2026-09-09):** see §9. Outcome: the *thermodynamic* arrow cannot root POST-hosting (the Γ-arrow rooting is the α-drift route); g-2 and the electron moment bound unnamed seam terms, they discriminate nothing; the α-drift clocks test DERIV-crystallisation-asymptotic, not POST-hosting; POST-hosting is re-worded as a statement about histories; its Gemini-kill is **dead** (decidable, cannot fire) — **but POST-hosting stays a root**, sharpened to the level lower bound; the driver's "derived from horn 1" claim was circular and is withdrawn (§9c).
6. **Confirmer delta** on §9 — done (C1–C7 applied in v0.4). It caught: the circularity of "derived from horn 1" (horn 1 already lives on the level-16 sphere; run one level down, at 𝕆 every state is a crystal and the kill *fires*); "every" vs "almost every" (vacua exist and are fixed points); the owed convergence bundled into the history form; a false ergodicity clause; DERIV-arrow half-quoted; and **MEAS-alpha's own 5σ discrepancy at M_Z** hidden under `discrepancy_pct 0.08` with status `coherent` — a pre-existing ledger problem now surfaced (§9b). *Because* the post-yield claim had been tested by no one.
8. **Trigger issue (beekeeper direction, 2026-09-09):** file the real question — *does crystallisation count as a physical process to which AXIOM-1 applies?* — with its trigger: it becomes answerable when the ledger holds the rule (#635) as a flow through the zero-divisor ridge, i.e. when "process" has an object. Until then option B stands; if ruled "yes" at trigger time, option A and its §4a price become due.
7. **Beekeeper flag (new, pre-existing):** MEAS-alpha predicts 1/α(M_Z) = 128.05 against 127.95 ± 0.02 — five standard deviations at the ledger's own comparison scale, recorded as `coherent`; CHAIN-axioms-to-alpha says the RGE step is "standard physics" and blames INST-f0. Either the chain note is wrong (RGE not done, the M_Z label wrong) or the anchor's status is. Needs a ruling independent of this package.

## 9. Rounds 5–6: rooting POST-hosting in an observation; precision observables (beekeeper-directed)

### 9a. The arrow-of-time rooting fails

| Step of the proposed chain | Status |
|---|---|
| the arrow of time is observed | measurement |
| dynamics is the algebra's own maps | the hosting frame — a definition |
| where the norm composes, every map R_t is an isometry, so iteration is a rotation with no transient | true (PROOF-ops-norm-composition-ladder; round 14/15 record) |
| **hence an arrow needs a non-isometric map** | **false for the thermodynamic arrow.** Volume-preserving dynamics plus coarse-graining gives the second law (Boltzmann); no dissipation is needed. (An earlier draft added "compositions of isometric R_t are ergodic on the state sphere" — **struck**: for t ∈ 𝕆 ∪ 𝕆ℓ the maps x ↦ x·t preserve or swap ‖cdLo x‖², ‖cdHi x‖² and generate a subgroup of (O(8) × O(8)) ⋊ ℤ/2, not transitive; the refutation never needed it.) DERIV-arrow read whole has two clauses: "lossy projection ⇒ irreversibility in the bulk" (projective) **and** "the Γ counter is monotonic" (a fundamental arrow: Γ counts crystallisation steps). The crystal is unitary (PRED-revival-exact). So: the *thermodynamic* arrow cannot root POST-hosting; the *Γ-arrow* rooting is exactly the α-drift route of §9b — which tests the local claim only (§9c). |

Both parties agreed the chain fails; the confirmer corrected the *reason*: not "the arrow is projective" (half of DERIV-arrow) but "the thermodynamic arrow needs no dissipation, and the Γ-arrow's only observable is the α-drift route". The only fundamental dissipation on record is the substrate transient onto the zero-divisor ridge, invisible from inside a crystal by construction. Gemini's "physically illiterate" endorsement of the driver's self-attack, with the false ergodicity clause included, is recorded as a fast-agreement tell (confirmer delta #11).

### 9b. Precision observables (beekeeper's question: Muon g-2, the electron moment, or another high-precision observable)

Sourced numbers used (no others): Fermilab Muon g-2 final (2025-06-03) a_μ = 0.001165920705(114), 0.127 ppm, 0.5σ from the 2025 lattice-based Standard Model value; electron a_e = 0.00115965218059(13), ≈ 0.11 ppb (Gabrielse group, 2023); MEAS-alpha: 1/α(M_Z) predicted 128.05 vs measured 127.95 ± 0.02.

| Observable | What QBP predicts for it | Use | Why |
|---|---|---|---|
| Muon g-2, electron a_e | **no mechanism named** — not a prediction of a null: DERIV-sedenion and DERIV-observation contain no computation bounding seam contributions to a QED vertex, and DERIV-crystallisation-asymptotic has α (hence a_e) drifting at an unpredicted rate | the SM–experiment agreement **bounds any unnamed seam term** at ≲ 10⁻¹⁰ relative (arithmetic on the sourced a_e uncertainty; the SM comparison is itself limited by the independent α input) | discriminates nothing the split asserts; PRED-no-gup (ħ per Γ-step) is not what a_e tests |
| α from a_e vs MEAS-alpha | **the ledger contradicts the "category mismatch" story** (confirmer delta #8): MEAS-alpha is labelled 1/α_em *at M_Z* = 128.05 vs 127.95 ± 0.02 — **5σ** at its own comparison scale, recorded as `discrepancy_pct 0.08`, status `coherent`; CHAIN-axioms-to-alpha calls the RGE step "standard physics" and blames INST-f0. Gemini's re-attribution of the 0.08% to "uncalculated RGE running" was adopted by the driver without opening the chain — withdrawn | a_e determines α(0); the run to M_Z is standard QED + hadronic vacuum polarisation with ±0.02 in 1/α — a_e's ppb never reaches M_Z; the relevant precision is MEAS-alpha's own ±0.02, **already violated** | either the chain note is wrong or the anchor's status is — flagged to the beekeeper (§8 item 7) |
| **α-drift** (Th-229 nuclear clock, REF-th229-alpha-sensitivity; optical clocks) | DERIV-crystallisation-asymptotic: constants converge, never freeze — but **no rate is predicted** | the in-flight observable **of our universe, now**; today a bound, not a measurement; DERIV-crystallisation-asymptotic stays `untested` until α̇ or Ġ is predicted | rank 1 — but it tests the local claim, not the global postulate (§9c) |
| PRED-revival-exact, PRED-gamma-universality | exact revival, no collapse | tests the *crystal's* unitarity; says nothing about the substrate | rank 3 |

### 9c. POST-hosting re-worded, and its kill is decidable

Round 5's "α frozen ⇒ in-flight region empty ⇒ level 16 unnecessary" was the new easy answer and does not follow: POST-hosting is global (all universes, per the 2026-09-07 scope) and historical (our crystal had to pass through V > 0 whether or not it is over). Two claims, separated:

| Claim | Scope | Observable | Status |
|---|---|---|---|
| **POST-hosting (history form):** "the substrate possesses an in-flight region V > 0 that every universe's history must pass through to reach a crystallised state" | global, structural | none directly | root — **or derived, see below** |
| DERIV-crystallisation-asymptotic: constants converge, never freeze | our universe, now | α̇, Ġ (CONSTRAINT-gdot, MEAS-G-cmb, MEAS-jwst-alpha-constraint) | `untested` until a rate is predicted; re-points to [POST-hosting, DERIV-constants] as the observational face |

**Gemini's kill for the history form:** the ruled initial ensemble (horn 1) places all its measure on the vacuum manifold V = 0 at Γ = 0 — the universe is born crystallised and no history passes through V > 0.

**Driver's observation (after Gemini yielded), as corrected by the confirmer delta:** that kill is decidable now, and it fails — but the inference drawn from it was wrong. Under horn 1 the ensemble is the surface measure on S¹⁴. The vacuum locus is parametrised by u ∈ S⁶ and (α, γ, b₀) ∈ S² (Prop 15, `vacuum_iff_parametrised`): an 8-dimensional subset of a 14-manifold, hence of surface measure zero. With probability 1 a history starts in flight. Numerically (`analysis/473-dirac-probe/inflight_measure_check.py`, asserted): Jacobian rank 8 at 20 random vacua; 20 000 Haar-random imaginary unit sedenions, none with V < 10⁻³ (V: min 0.030, median 0.683, max 0.9999 at the ridge). **What is confirmed:** Gemini's kill is dead. The vacuum locus has codimension 6 in the state sphere (simpler proof: V is a non-trivial polynomial on the sphere — `inFlight_nonempty` — so its zero set has measure zero), and *any* absolutely continuous ensemble puts no mass on it; horn 1 is the surface measure and is far more than needed.

**What is NOT confirmed — withdrawn:** "POST-hosting is therefore derived from horn 1 + Prop 15, so it is not a root." Three faults (confirmer delta #1–#3):
- **Circular.** Horn 1 is a measure on the *sedenion* sphere S¹⁴ — it already lives at level 16. D2 uses POST-hosting to supply "level ≥ 16". Run the same argument one level down: level-generic horn 1 at 𝕆 is the surface measure on S⁶, every imaginary octonion is a crystal (`assoc_diag_left`), and the universe *is* born crystallised — the kill **fires at 8**. So "almost every history starts in flight" ⇔ "V ≢ 0 at the substrate level" ⇔ "substrate level ≥ 16": the measure argument *re-expresses* POST-hosting as the level lower bound; it does not derive it from the ruling.
- **"Every" is false; "almost every" is what holds.** Vacua exist and are Lean-named (`ell_isVacuum`, `sAll_isVacuum`); V = 0 is the global minimum, so they are fixed points of any V-descending rule; a history starting there never passes through V > 0.
- **The history form bundles an owed claim.** "…to reach a crystallised state" needs the rule's flow to converge (hosting §4(c), Łojasiewicz owed). D2 needs only "non-crystal states are physically realised".

**POST-hosting, final form (v0.4):** *"Non-crystal states are physically realised: the state sphere at the substrate level carries an in-flight region V > 0 of positive measure, and almost every history starts in it."* Kill: theory-internal only — a substrate level at which V ≡ 0 (i.e. the level bound failing); no observable. Convergence to 𝓤 is the rule's claim (#635), separate. **It is a root.** The root list stays as §2a, with **the rule** now visible as a fifth (the confirmer's #3) and horn 1 not among them (absolute continuity does the work, not MaxEnt — the "matched pair" sentence was rhetoric and is struck).

**What this does to the beekeeper's original question.** "Could we enable the derivation by writing down a physical postulate?" — yes: POST-hosting, now stated exactly, is that postulate, and it is the level lower bound in physical clothing. It cannot be derived from the ensemble without assuming the level. What the two rounds bought is the exact statement of the root, the death of one proposed kill, and the knowledge that the split has one empirical face (§0).

## 10. Confirmer conditions and where each landed (v0.2)

| # | Condition | Landed |
|---|---|---|
| 1 | state the level-generic crystal definition; note the CD-commutator form is 𝕊-specific and diverges at 𝕆; cite `assoc_diag_left`; count the definition as a root | §3 DERIV-substrate-level; §2/§2a |
| 2 | triage AXIOM-1's citers for the rescope | §4a (22 + 5; 7 + 1 need a re-read) |
| 3 | relabel the AXIOM-1 edit as a rescope; put the no-edit alternative beside it, priced | §3 options A / B; §0 |
| 4 | POST-hosting's kill in hosting-§4(b) form; drop "falsifiable" | §3 POST-hosting; §0 |
| 5 | count META-2 honestly (split, not demotion); chains 7; docs + docstrings; "level below the first failure" | §2a; §4; §3 DERIV-encoding-level |
| 6 | verbatim turns committed; strike "sealed"; record Gleason | verbatim file; §6; below |

**Unverified citation, not adopted:** Gemini invoked *Gleason's theorem* for PROOF-born (turn 55 §3). Gleason is a real theorem about measures on Hilbert-space projections; it says nothing about uniqueness of a multiplicative norm on ℍ. Not in the ledger; not used by this package; recorded per MO §7.
