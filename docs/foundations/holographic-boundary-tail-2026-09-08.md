# The holographic boundary — the tail of DERIV-holographic, defined on the hosting objects (v0.3, 2026-09-09)

**Status:** definition proposal for the beekeeper, v0.3 — v0.2 after the #643 Red Team + Gemini reviews; v0.3 adds §1a (DERIV-holographic formalised; P1 reduced to hosting clause (a)) on the beekeeper's 2026-09-09 direction (item 2 of the 2026-09-08 plan; asked for on 2026-09-07: *"you're going to have to define that in a little bit more detail"*). Everything here is tagged to a source — a Lean theorem on master, a numerical script in this repo, a CTH ledger entry with its status, or a beekeeper ruling. **This document edits no ledger entry.** DERIV-holographic and its five dependents are constitutional (layer 1); §5 is a *draft* re-statement for the beekeeper's ruling, not a change. Written by qbp-oppenheimer.

**One-line summary.** The ledger's "4D gap" is now a theorem; the phrase "*is the holographic boundary*" was never given an object. On the hosting objects there are **two different boundaries** with two different ledger parents — the *holographic* boundary of one universe (candidate A below, inside an octonion containing the crystal's ℍ) and the *seam* boundary between universes (the zero-divisor locus, DERIV-sedenion) — and candidate A **reduces the ledger's pre-existing frame freedom** (which ℍ the observer sits in: 8 parameters, G₂/SO(4)) **to the choice of an encoding octonion around the crystal's ℍ_s: 4 parameters, a ℂP²** — a choice the hosting definition does not yet carry, and which has a canonical v-free home (the ℍ_s-module ℍ_s^⊥ ≅ ℍ_s³). Two premises carry that reading and are named in §3.

## 1. DERIV-holographic, sentence by sentence

Ledger text (layer 1, `derived_from` AXIOM-1, AXIOM-2): *"Observers require associativity. The largest associative subalgebra of 𝕆 is ℍ (dim 4). The 4D gap is the holographic boundary."*

| Sentence | Kind | Status on master | Witness |
|---|---|---|---|
| "Observers require associativity" | **postulate** | not proved; not provable from the algebra alone | support is *narrow*: composition of left multiplications is exactly associativity (`lMul_comp_eq_iff_assoc_forall`, PROOF-associative-composition-iff, coherent); ℓ is the unique imaginary direction with `[x, x, ℓ] = 0 ∀x` — the theorem gives `{y : [x,x,y] = 0 ∀x} = span{1, ℓ}` (`assoc_self_zero_iff`, #640). "Dynamics need associativity" was **retracted** in round 14 (flag 3, addendum §5) |
| "The largest associative subalgebra of 𝕆 is ℍ" | **theorem**, frame-relative | proved: every associative subalgebra containing a quaternion frame equals it (`span4_eq_of_associative`, PROOF-quaternion-frame-maximal, coherent) | the fully general "every associative subalgebra has dim ≤ 4" is **deferred, not blocked** (elementary Gram–Schmidt over `bil`; architecture ruling 2026-09-07) |
| "(dim 4)" / "the 4D gap" | **theorem** | proved: `quaternion_frame_codim_four` — `finrank span{1,u,v,uv} + 4 = 8` (PROOF-quaternion-frame-codim-four, coherent) | a number, with no boundary semantics in any statement |
| "…is the holographic boundary" | **interpretation** | **no object behind it** until this document | — |

So flag 3 (addendum §5, item 3) resolves into: two theorems on master, one postulate that stays a postulate, and one interpretation that needs a definition. §2 supplies the candidates.

## 1a. DERIV-holographic formalised, and what its support actually is (beekeeper direction, 2026-09-09)

**Why the Prop 16 support runs only through ℓ.** Prop 16(ii) says a crystal `s` together with `ℓ` generates a quaternion algebra. In #473 round 13 this was elevated to "the algebra's operations on any state generate only associative (H-space) substructures" (T-B); round 14 computed it instead of agreeing (transcript `473-ac1-rounds-13-15-transcript-2026-09-05.md` §1):

| Generators | Generated subalgebra (words ≤ 4) | Max associator | Associative? |
|---|---|---|---|
| `s`, `ℓ` | dim 4 — a copy of ℍ | 0 (exact) | yes |
| `s`, generic `t` | dim 10 and growing with word length | 0.34–0.40 | no; not even alternative |

The quaternion closure is a property of **ℓ**, not of the algebra's operations: `{y : [x, x, y] = 0 ∀x} = span{1, ℓ}` (`assoc_self_zero_iff`, #640). Adjoin the one distinguished direction and you get ℍ; adjoin anything else and you get a non-associative 10-dim subalgebra. So Prop 16 says "ℓ is the unique direction that associates with everything, and crystal + ℓ = ℍ" — nothing about observers.

**Why "dynamics need associativity" was retracted (round 14/15).** The round-13 claim was that autonomous dynamics require associative-ish composition, so physics could only live on ℍ. The test inverted it: the generic non-associative subalgebra *does* carry the algebra's own self-maps, and iterating them (`x ↦ x·t`, power iteration of the skew part of `R_t`, `generic_maps_check.py`) gives genuine dynamics with an attractor — the zero-divisor ridge `V = 1`. The associative case (`s` with `ℓ`) gives only finite-order maps, i.e. symmetries, and the ℓ-axis pole. On the record: **associativity ⇒ symmetries; non-associativity ⇒ motion.** Both retractions are recorded (transcript round 15 §1). "Observers require associativity" therefore cannot be read as a dynamical necessity.

**The entry, formally.** Setting: `𝕊 = CDAlg ℝ 4`; a universe `U(s)` with hosted algebra `ℍ_s` (`Hosting.lean`).

| Part | Formal content | Status |
|---|---|---|
| **T1** composition | for `A ⊆ 𝕊`: `L_x ∘ L_y = L_{xy}` for all `x, y ∈ A` **iff** `A` is associative | proved (`lMul_comp_eq_iff_assoc_forall`) |
| **T2** maximality | an associative subalgebra containing a quaternion frame equals it (dim 4) | proved, frame-relative (`span4_eq_of_associative`); global ≤ 4 deferred |
| **T3** the gap | `dim 𝕆 − dim ℍ = 4` | proved (`quaternion_frame_codim_four`) |
| **P** the postulate | an *observer* `O` in `U(s)` is a subset `A_O ⊆ 𝕊` on which `O`'s actions compose; by T1 `A_O` is associative; by T2 it lies inside one ℍ | not provable — the entire content of "observers require associativity" |
| **I** the interpretation | there is an injective map `Φ` from bulk configurations on the unit `S³ ⊂ ℍ_s` to data on the 4-dim gap inside the encoding octonion (injective by AXIOM-1) | no `Φ` on record; "holographic" is the name of `Φ`; §2–§3 |

**The hole in P.** "Observer = associative subset" is a *definition*, not a claim, unless *observer* is defined independently first. The ledger never did that. **Hosting does.** Clause (a) of the hosting definition (`substrate-hosting-definition-2026-09-07.md` §2; the frame the beekeeper ruled 2026-09-07) says an *entity* of `U(s)` is a persistent configuration on the unit sphere `S³ ⊂ ℍ_s` with a topological charge (Agda `SkyrmionCharge`: `B(hedgehog) = 1`, `π₃(S³) ≅ ℤ`). Observers are made of entities. Hence:

> **P1, reduced.** Under hosting clause (a), the observer's algebra is `ℍ_s` **by construction**, and the justification "observers require associativity" is replaced by "matter is hosted on the crystal's ℍ". What remains as an assumption is only
> **P1′:** *observers are entities in the sense of clause (a)* — i.e. an observer is a (composite of) persistent charged configuration(s) on `S³ ⊂ ℍ_s`.

P1′ is weaker than P1 and it is not the flag-3 identification any more: it does not identify `ℍ_s` with anything external; it says observers are made of the matter the universe hosts. Flag 3's remaining content is then the **postulate P**, whose only job under hosting is to say *why* entities compose (T1) — and that is what the retracted dynamics claim was trying to do. Honest status: P is a postulate with no dynamical support; P1′ is the hosting frame applied to observers.

**Pole corollary (derivable).** A pole universe hosts `ℂ = span{1, ℓ}` (`pole_hosts_complex`, master). The unit sphere of ℂ is `S¹`, and `π₃(S¹) = 0` (`S¹` is a 1-type: `isGroupoidS¹` in `cubical`), so no configuration on it carries a topological charge: **pole universes host no charged entities, hence no observers.** The pole objection to P1 (boundary note v0.2 §3; answer to the beekeeper 2026-09-09) is not an exception to be declared — it is a theorem to be filed (§6 (viii)). P2 is untouched by all of this.

## 2. What "the boundary of a universe U(s)" could be, on the objects in Lean

The objects (all on master, `Substrate/Hosting.lean`, `Foundations/CrystalHosting.lean`): a universe is a crystal `s ∈ UniverseSpace` with hosted algebra `ℍ_s = span{1, ℓ, U, ℓU}` (`universe_hosts_quaternion`), `U = loOf u`, `u` the common direction of the crystal's Cayley–Dickson components (Prop 15). **Fact that matters here:** `ℍ_s` contains `ℓ = e₈`, so it is **not** inside the Cayley–Dickson low-half octonions `𝕆 = span{e₀..e₇}` — it straddles both halves (`ℓ`, `ℓU` are in the high half). The octonions of AXIOM-2 ("the boundary encoding uses 𝕆") therefore cannot mean the CD half relative to a universe.

| Candidate | Object | Dim | Ledger parent | For | Against | Source / status |
|---|---|---|---|---|---|---|
| **A. The 4D gap inside an octonion containing ℍ_s** | `𝕆'_v := ℍ'_v ⊕ ℍ'_v·ℓ` with `ℍ'_v = span{1, u, v, uv}` for a unit imaginary octonion `v ⊥ u`; boundary `∂_v U(s) := ℍ_s^⊥ ∩ 𝕆'_v = span{V, UV, ℓV, ℓ(UV)} = ℍ_s·V` (an ℍ_s-line) | 4 | DERIV-holographic ("the 4D gap"), AXIOM-2 (an 𝕆) | literal reading of the ledger; the codimension-4 theorem is exactly this gap; `𝕆'_v` is a genuine octonion (closed, alternative) containing ℍ_s | **not canonical**: depends on the ℂ_u-line `span{v, uv}` (v and uv give the same octonion), so the encodings form a **ℂP²** (4 real parameters); for `v' ⊥ {u, v, uv}` the two gaps meet only in 0; a generic `x ⊥ ℍ_s` lies in no gap. **Completeness — that the `𝕆'_v` are *all* the octonion subalgebras of 𝕊 containing ℍ_s — is a CONJECTURE**, numerically supported (§4), not proved | numerical, asserted: `analysis/473-dirac-probe/boundary_octonion_check.py` (5 trials; closure 5e-16, alternativity 2e-14, rank 8, gap dim 4, `dim(gap_v + gap_v') = 8`, `𝕆'_{uv} = 𝕆'_v`, generic x outside, ℍ_s-module residual 1e-15, mixed-halves w not closed); Lean: **to prove** (§6) |
| **B. The seams** | the zero-divisor locus `V = 1` on the state sphere, where the algebra's own maps run (layer 3) | 11 (a single G₂-orbit in S¹⁴) | DERIV-sedenion ("inter-cell boundary structure is 𝕊; seams where information CAN be destroyed") | this is where crystallisation *starts from* under the ruled ensemble and where the generic maps go; the only place information loss is even discussed in the ledger | it is a locus in the **substrate**, not a subspace of one universe's complement; it bounds the in-flight region between universes, not U(s) | Lean: PROOF-sedenion-zero-divisor-witnesses (coherent); numerical: `generic_maps_check.py`, `aut_s3.py` (orbit dim 11) |
| **C. The whole complement of ℍ_s in 𝕊** | `ℍ_s^⊥` | 12 | Feynman's remark on #641 ("the other 12 dimensions are boundary or in-flight") | simple; contains every A; **it is a left ℍ_s-module ≅ ℍ_s³** (numerical, residual 1e-15) — the canonical v-free object the gaps are ℍ_s-lines in | contradicts "4D gap" as a *definition*: the union of all gaps `∂_v` is an 8-dim cone (4-dim fibres over the ℂP² of ℂ_u-lines) inside the 12-dim `ℍ_s^⊥`, and a generic vector of `ℍ_s^⊥` lies in no gap — there is no canonical "8 outside", only the cone's open-dense complement | rejected as *the boundary*; retained as **the ambient module** (§3) |

**Reading.** A and B are **different objects with different parents** and the ledger has been using one word for both. *Holographic boundary of a universe* = candidate A (per universe, inside an octonion, 4-dim, DERIV-holographic / AXIOM-2). *Seam boundary between universes* = candidate B (in the substrate, DERIV-sedenion, where flag 1 lives). Note a **third** use hiding in AXIOM-2: its "boundary *encoding*" is the 8-dim octonion `𝕆'_v` itself, while DERIV-holographic's "4D gap" is the 4-dim complement of ℍ_s inside it — encoding algebra ≠ gap. Proposal: adopt the three names (encoding octonion / holographic gap / seam) and never let "boundary" appear in a ledger entry or a Lean docstring without one of them.

## 3. What candidate A exposes: the frame freedom, reduced and relocated

**Two premises first** (neither forced by the objects; both must be ruled, not assumed):

- **P1 → P1′.** The crystal's hosted `ℍ_s` is the observer's ℍ. Under hosting clause (a) this holds *by construction* (§1a); the residual assumption is **P1′: observers are entities in the sense of clause (a)**. Flag 3's remaining content is the postulate P of §1a, not this identification.
- **P2.** The encoding octonion of AXIOM-2 must *contain* `ℍ_s`.

Grant both. Then the honest headline is a **reduction, not a discovery**: before hosting, nothing selected which quaternion frame `ℍ ⊂ 𝕆` the observer sat in — G₂ is transitive on frames, so that freedom was `G₂/SO(4)`, **8 parameters**. Hosting fixes the direction `u` from the crystal (Prop 15), and what remains is the choice of an encoding octonion around `ℍ_s`, i.e. a ℂ_u-line `span{v, uv}` in `u^⊥ ≅ ℝ⁶`: a **ℂP², 4 parameters**. The gap `∂_v = ℍ_s·V` depends only on that line (numerically asserted: `𝕆'_{uv} = 𝕆'_v`).

**The v-free object.** `ℍ_s^⊥` is a left `ℍ_s`-module (left multiplication by `U`, `ℓ`, `ℓU` preserves it; residual 1e-15), so `ℍ_s^⊥ ≅ ℍ_s³` canonically, and every gap is one *admissible* `ℍ_s`-line in it — admissible meaning the line is `ℍ_s·V` for a low-half `V`, which is what makes `ℍ_s ⊕ ℍ_s·V` close into an octonion (the completeness conjecture says these are the only lines that do; a mixed-halves `w` off a ℂ_u-line fails closure with residual ≥ 0.3 in every trial). So the two honest formulations of "the boundary" are:

| Formulation | Object | Datum needed |
|---|---|---|
| a line | one gap `∂_v = ℍ_s·V`, 4-dim | a point of ℂP² |
| the module with its line bundle | `ℍ_s^⊥ ≅ ℍ_s³` with the 8-dim cone of admissible lines over ℂP² | none (canonical) |

Which of these "the holographic boundary of U(s)" *is* — a chosen line, or the bundle of all of them — is the beekeeper question (§7 Q2). Consequences either way:

- `structure Universe` (`Hosting.lean`) carries no ℂP² point. If the answer is "a line", adding one is a **definition change** for #639 (a field, or a further crystallisation stage `ℂP² → point` that the rule must act on, or an observer's choice belonging with the postulate). If the answer is "the bundle", no new field — the boundary is a function of the crystal.
- The physical content of "holographic" — *the bulk physics on the unit S³ of ℍ_s is encoded on the gap* — is an **interpretation with no map** behind it. The triangle-bootstrap assessment (`qbp-triangle-bootstrap-2026-06-16.md` §5, flag 2 there) already recorded that the holographic-lock edge imports Ryu–Takayanagi-type results from AdS/CFT without a QBP-internal map; nothing here changes that.
- **Kill conditions, two levels.** *Mathematical* kills exist and are scripted: closure of `𝕆'_v` (checked, holds), the gap dimension (checked, holds), the completeness conjecture (probed, holds so far; a Lean proof or a counterexample settles it). The *physical* kill — the encoding map failing — cannot fire until a map `S³ → ∂U(s)` (or its entropy form) is written down; until then "holographic" is a name.

## 4. What is proved, provable, postulated, interpreted — under candidate A

| Claim | Kind | State |
|---|---|---|
| `ℍ_s` is a quaternion algebra, 4-dim, proper in 𝕊 | theorem | master (PROOF-crystal-hosts-quaternion) |
| composition `L_x L_y = L_{xy}` on a set ⇔ the set is associative | theorem | master (PROOF-associative-composition-iff) |
| no associative subalgebra of 𝕆 properly contains a quaternion frame; codim 4 | theorem (frame-relative) | master (PROOF-quaternion-frame-maximal, -codim-four) |
| `𝕆'_v` is an octonion subalgebra of 𝕊 containing `ℍ_s`, for every `v ⊥ u` | theorem, **to prove** | numerical, asserted (this document); Lean §6 (i) |
| `∂_v U(s)` is 4-dim; `∂_v ∩ ∂_{v'} = 0` for `v' ⊥ {u, v, uv}`; `∂_v` depends only on the ℂ_u-line of `v` | theorem, **to prove** | numerical, asserted; Lean §6 (ii)–(iii) |
| `ℍ_s^⊥` is a left `ℍ_s`-module `≅ ℍ_s³`; the union of the gaps is an 8-dim cone in it | theorem, **to prove** | numerical, asserted; Lean §6 (iv) |
| **completeness**: every octonion subalgebra of 𝕊 containing `ℍ_s` is some `𝕆'_v` | **conjecture** | numerical probe only (mixed-halves `w` fails closure); Lean §6 (v) or a counterexample |
| every associative subalgebra of 𝕆 has dim ≤ 4 (global) | theorem, deferred | Gram–Schmidt over `bil`; architecture ruling 2026-09-07 |
| P1′: observers are entities of clause (a) (then the observer's ℍ is `ℍ_s` by construction); P2: the encoding 𝕆 contains `ℍ_s` | **premises** | P1′ is the hosting frame applied to observers (§1a); P2 not forced by the objects |
| pole universes host no charged entities, hence no observers | corollary, **to file** | `pole_hosts_complex` (master) + `π₃(S¹) = 0` (Agda, §6 (viii)) |
| observers require associativity | **postulate** | unchanged; support narrow (§1) |
| the bulk physics on `S³ ⊂ ℍ_s` is encoded on `∂_v U(s)` | **interpretation** | no map; no kill condition yet |
| information can be destroyed at the seams (B) | constitutional flag 1 | DERIV-sedenion vs AXIOM-1, unreconciled (addendum §5 item 1) |

## 5. Draft re-statement of DERIV-holographic for the beekeeper (constitutional; NOT applied)

Split the one entry into three, so a citation can say which part it rests on:

| Proposed id | Text | Kind / status | Anchors |
|---|---|---|---|
| **POST-observer-associativity** | "An observer is a subset of 𝕊 on which its actions compose; by the composition theorem such a subset is associative and lies inside one ℍ. Under the hosting definition (clause (a)) the observer's ℍ is the crystal's `ℍ_s` by construction." | postulate; support narrow (composition law; ℓ unique); NOT a dynamical necessity (round-14 retraction) | PROOF-associative-composition-iff; `assoc_self_zero_iff`; PROOF-substrate-hosting-definition |
| **DERIV-holographic-theorem** | "Quaternion frames span{1,u,v,uv} are associative subalgebras of 𝕆; no associative subalgebra properly contains one (frame-relative; global dim ≤ 4 deferred); the codimension of ℍ in 𝕆 is 4." | derived, **proved** | PROOF-quaternion-frame-maximal, PROOF-quaternion-frame-codim-four |
| **INTERP-holographic-boundary** | "The holographic gap of a universe U(s) is an admissible ℍ_s-line `∂_v = ℍ_s·V` (4-dim) in the module `ℍ_s^⊥ ≅ ℍ_s³`, the complement of ℍ_s inside an encoding octonion `𝕆'_v ⊃ ℍ_s`; the encodings form a ℂP² not fixed by the landscape; the seam boundary between universes is the zero-divisor locus (DERIV-sedenion)." | interpretation, **proposed**; rests on premises P1, P2 | this document; `boundary_octonion_check.py`; Lean §6 pending |

**Re-pointing the dependents.** Five `derived_principles` list DERIV-holographic in `derived_from` (some alongside AXIOM-1/AXIOM-2, which stay), and three *anchors* chain on it through `prediction_chain` — PROOF-3gen (coherent), PRED-gw-em, PRED-revival-exact — which a split must re-point too:

| Dependent | Needs which part | Note |
|---|---|---|
| DERIV-3plus1 ("quaternion structure: 1 + 3") | POST + DERIV-theorem | the only one that needs *just* the postulate and the proved algebra |
| DERIV-observation ("EM observation accesses ℂ ⊂ ℍ; measurement projects ℍ → ℂ → ℝ") | POST + DERIV-theorem (+ `pole_hosts_complex` for ℂ as a hosted algebra) | no boundary needed |
| DERIV-pati-salam (NCG on `A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)`) | DERIV-theorem (ℍ as the finite algebra's factor) | independent of the boundary interpretation |
| DERIV-arrow ("preservation + lossy projection ⇒ irreversibility; Γ monotonic") | POST + INTERP (the loss is a projection onto the boundary) + AXIOM-1 | sits next to flag 1: if loss is at the *seams* (B) it is DERIV-sedenion's, not the holographic boundary's |
| DERIV-constants (ħ, k, c as information-per-Γ-step conversions) | POST + INTERP | the Γ-counter is DERIV-arrow's object, so the postulate is needed too (Gemini); the *scales* rest on the interpretation — weakest link |
| PROOF-3gen (anchor, coherent) | DERIV-theorem (three quaternion-type factors) | verify on the split; do not orphan |
| PRED-gw-em, PRED-revival-exact (anchors, `prediction_chain`) | POST + INTERP | predictions; re-point explicitly or they lose their chain |

## 6. Lean to write (cheap → not), all `QBP.Foundations` material, no Substrate edit

1. **(i) `𝕆'_v` is an octonion subalgebra of 𝕊 containing `ℍ_s`.** Closure of `ℍ'_v ⊕ ℍ'_v ℓ` under the sedenion product is the Cayley–Dickson doubling formula applied to the associative `ℍ'_v` (`cdLo_mul` / `cdHi_mul`); alternativity of the doubling of an associative algebra is a standard identity — moderate. Containment of `ℍ_s` is immediate from `ℓU = −Uℓ`.
2. **(ii) `dim ∂_v U(s) = 4`** — from `crystal_quatSpan_independent` and a rank count; easy given (i).
3. **(iii) Non-canonicity witness** — two explicit `v, v'` with `∂_v ∩ ∂_{v'} = 0`; easy.
4. **(iv) `ℍ_s^⊥` is a left `ℍ_s`-module** — `L_U`, `L_ℓ`, `L_{ℓU}` preserve `ℍ_s^⊥`; from the quaternion table and `bil` invariance; easy-to-moderate.
5. **(v) Completeness** — every octonion subalgebra of 𝕊 containing `ℍ_s` is some `𝕆'_v`: the real theorem behind the ℂP²; moderate-to-hard (classify `w ⊥ ℍ_s` with `ℍ_s ⊕ ℍ_s w` closed and alternative). A counterexample kills the ℂP² count.
6. **(vi) Global dim ≤ 4** — the deferred Gram–Schmidt; not needed for A.
7. **(vii) Uniqueness of `u` up to sign for a non-pole crystal** — owed from the definition doc §6; independent.
8. **(viii) Pole universes carry no topological charge** — Agda: `S¹` is a 1-type (`isGroupoidS¹`) ⇒ `π₃(S¹) ≅ 0`, wired to the `SkyrmionCharge` degree so that no configuration on the unit sphere of `span{1, ℓ}` has `B ≠ 0`; Lean side already on master (`pole_hosts_complex`). Cheap; the `agda-prover` lane.

## 7. Questions this puts to the beekeeper and to the definition conversation

1. **Two boundaries, two names** (holographic = A per universe; seam = B between universes) — adopt?
2. **Is the holographic boundary a line or the bundle?** Under P1 + P2 the freedom is a ℂP² (down from the ledger's 8-parameter frame freedom). If "a line", `Universe` gains a ℂP² point (field / later crystallisation stage the rule acts on / observer's choice belonging with the postulate). If "the bundle", the boundary is the canonical module `ℍ_s^⊥ ≅ ℍ_s³` with its cone of admissible lines and no new datum. This is doc §5 Q2, sharpened. **P2 needs a ruling before either answer means anything; P1 has been reduced to P1′ (§1a), which is the hosting frame applied to observers.**
3. **Flag-3 re-statement** (§5): rule on the split and the re-pointing, or keep the single entry with the theorem anchors attached.
4. **Flag 1 placement:** under the two-boundaries reading, "information CAN be destroyed" is a statement about B (DERIV-sedenion), not about the holographic boundary; that narrows, but does not resolve, the tension with AXIOM-1.
5. **Kill conditions:** the mathematical ones are scripted and hold (closure, dimension, module) with completeness as the open one; the physical one does not exist until an encoding map is defined — propose the conversation is asked to produce *the form* such a map must take, not the map.
