# The holographic boundary — the tail of DERIV-holographic, defined on the hosting objects (v0.1, 2026-09-08)

**Status:** definition proposal for the beekeeper (item 2 of the 2026-09-08 plan; asked for on 2026-09-07: *"you're going to have to define that in a little bit more detail"*). Everything here is tagged to a source — a Lean theorem on master, a numerical script in this repo, a CTH ledger entry with its status, or a beekeeper ruling. **This document edits no ledger entry.** DERIV-holographic and its five dependents are constitutional (layer 1); §5 is a *draft* re-statement for the beekeeper's ruling, not a change. Written by qbp-oppenheimer.

**One-line summary.** The ledger's "4D gap" is now a theorem; the phrase "*is the holographic boundary*" was never given an object. On the hosting objects there are **two different boundaries** with two different ledger parents — the *holographic* boundary of one universe (candidate A below, inside an octonion containing the crystal's ℍ) and the *seam* boundary between universes (the zero-divisor locus, DERIV-sedenion) — and candidate A exposes **a datum the hosting definition does not yet carry: which copy of 𝕆 a universe is encoded in.**

## 1. DERIV-holographic, sentence by sentence

Ledger text (layer 1, `derived_from` AXIOM-1, AXIOM-2): *"Observers require associativity. The largest associative subalgebra of 𝕆 is ℍ (dim 4). The 4D gap is the holographic boundary."*

| Sentence | Kind | Status on master | Witness |
|---|---|---|---|
| "Observers require associativity" | **postulate** | not proved; not provable from the algebra alone | support is *narrow*: composition of left multiplications is exactly associativity (`lMul_comp_eq_iff_assoc_forall`, PROOF-associative-composition-iff, coherent); ℓ is the unique element with `[x, x, ℓ] = 0 ∀x` (`assoc_self_zero_iff`, #640). "Dynamics need associativity" was **retracted** in round 14 (flag 3, addendum §5) |
| "The largest associative subalgebra of 𝕆 is ℍ" | **theorem**, frame-relative | proved: every associative subalgebra containing a quaternion frame equals it (`span4_eq_of_associative`, PROOF-quaternion-frame-maximal, coherent) | the fully general "every associative subalgebra has dim ≤ 4" is **deferred, not blocked** (elementary Gram–Schmidt over `bil`; architecture ruling 2026-09-07) |
| "(dim 4)" / "the 4D gap" | **theorem** | proved: `quaternion_frame_codim_four` — `finrank span{1,u,v,uv} + 4 = 8` (PROOF-quaternion-frame-codim-four, coherent) | a number, with no boundary semantics in any statement |
| "…is the holographic boundary" | **interpretation** | **no object behind it** until this document | — |

So flag 3 (addendum §5, item 3) resolves into: two theorems on master, one postulate that stays a postulate, and one interpretation that needs a definition. §2 supplies the candidates.

## 2. What "the boundary of a universe U(s)" could be, on the objects in Lean

The objects (all on master, `Substrate/Hosting.lean`, `Foundations/CrystalHosting.lean`): a universe is a crystal `s ∈ UniverseSpace` with hosted algebra `ℍ_s = span{1, ℓ, U, ℓU}` (`universe_hosts_quaternion`), `U = loOf u`, `u` the common direction of the crystal's Cayley–Dickson components (Prop 15). **Fact that matters here:** `ℍ_s` contains `ℓ = e₈`, so it is **not** inside the Cayley–Dickson low-half octonions `𝕆 = span{e₀..e₇}` — it straddles both halves (`ℓ`, `ℓU` are in the high half). The octonions of AXIOM-2 ("the boundary encoding uses 𝕆") therefore cannot mean the CD half relative to a universe.

| Candidate | Object | Dim | Ledger parent | For | Against | Source / status |
|---|---|---|---|---|---|---|
| **A. The 4D gap inside an octonion containing ℍ_s** | `𝕆'_v := ℍ'_v ⊕ ℍ'_v·ℓ` with `ℍ'_v = span{1, u, v, uv}` for a unit imaginary octonion `v ⊥ u`; boundary `∂_v U(s) := ℍ_s^⊥ ∩ 𝕆'_v = span{V, UV, ℓV, ℓ(UV)}` | 4 | DERIV-holographic ("the 4D gap"), AXIOM-2 (an 𝕆) | literal reading of the ledger; the codimension-4 theorem is exactly this gap; `𝕆'_v` is a genuine octonion (closed, alternative) containing ℍ_s | **not canonical**: depends on `v`; two orthogonal choices give gaps meeting only in 0; a random `x ⊥ ℍ_s` lies in no single `𝕆'_v` | numerical, exact to 1e-14: `analysis/473-dirac-probe/boundary_octonion_check.py` (5 trials; closure 5e-16, alternativity 2e-14, rank 8, gap dim 4, `dim(gap_v + gap_v') = 8`); Lean: **to prove** (§6) |
| **B. The seams** | the zero-divisor locus `V = 1` on the state sphere, where the algebra's own maps run (layer 3) | 11 (a single G₂-orbit in S¹⁴) | DERIV-sedenion ("inter-cell boundary structure is 𝕊; seams where information CAN be destroyed") | this is where crystallisation *starts from* under the ruled ensemble and where the generic maps go; the only place information loss is even discussed in the ledger | it is a locus in the **substrate**, not a subspace of one universe's complement; it bounds the in-flight region between universes, not U(s) | Lean: PROOF-sedenion-zero-divisor-witnesses (coherent); numerical: `generic_maps_check.py`, `aut_s3.py` (orbit dim 11) |
| **C. The whole complement of ℍ_s in 𝕊** | `ℍ_s^⊥` | 12 | Feynman's remark on #641 ("the other 12 dimensions are boundary or in-flight") | simple; contains every A | contradicts "4D gap"; mixes A (4 dims, in *some* `𝕆'_v`) with the 8 dims outside every `𝕆'_v` — under DERIV-sedenion those 8 are *other-cell* structure, not this universe's boundary | rejected as a definition; kept as the ambient space A lives in |

**Reading.** A and B are **different objects with different parents** and the ledger has been using one word for both. *Holographic boundary of a universe* = candidate A (per universe, inside an octonion, 4-dim, DERIV-holographic / AXIOM-2). *Seam boundary between universes* = candidate B (in the substrate, DERIV-sedenion, where flag 1 lives). Proposal: adopt both names and never let "boundary" appear in a ledger entry or a Lean docstring without one of them.

## 3. What candidate A exposes: the encoding octonion is a missing datum of a universe

Under A, a universe carries **three** data, not two: the crystal `s`, the hosted `ℍ_s` (determined by `s`), and **the encoding octonion `𝕆'_v` — i.e. the choice of `v ∈ S⁵ ⊂ Im𝕆 ∩ u^⊥` modulo the stabiliser of `ℍ'_v`.** AXIOM-2 fixes the *type* of the boundary algebra (octonions, dim 8); it does not pick the copy. Nothing in the δ-landscape, the ensemble, or the rule selects `v`, exactly as nothing selects the orientation `k = ℓu` vs `uℓ` (definition doc §6). Consequences:

- `structure Universe` (`Hosting.lean`) has no such field. Adding one is a **definition change** for #639, not a theorem, and needs the beekeeper's word — is the encoding octonion part of what a universe *is*, or a further crystallisation stage (a second symmetry breaking, `S⁵ → point`), or an observer's choice?
- If it is a further crystallisation stage, the state sphere is not the whole substrate: the substrate would be `S¹⁴ × (the fibre of encodings)`, and the hosting definition's "the substrate is the state sphere" (doc §1) is incomplete. This is the sharpest thing the tail has produced and belongs at the top of the definition conversation (doc §5 Q2).
- The physical content of "holographic" — *the bulk physics on the unit S³ of ℍ_s is encoded on `∂_v U(s)`* — is an **interpretation with no map** behind it. The triangle-bootstrap assessment (`qbp-triangle-bootstrap-2026-06-16.md` §5, flag 2 there) already recorded that the holographic-lock edge imports Ryu–Takayanagi-type results from AdS/CFT without a QBP-internal map; nothing here changes that. Until a map `S³ → ∂_v U(s)` (or its entropy version) is written down, "holographic" is a name, and no kill condition can fire.

## 4. What is proved, provable, postulated, interpreted — under candidate A

| Claim | Kind | State |
|---|---|---|
| `ℍ_s` is a quaternion algebra, 4-dim, proper in 𝕊 | theorem | master (PROOF-crystal-hosts-quaternion) |
| composition `L_x L_y = L_{xy}` on a set ⇔ the set is associative | theorem | master (PROOF-associative-composition-iff) |
| no associative subalgebra of 𝕆 properly contains a quaternion frame; codim 4 | theorem (frame-relative) | master (PROOF-quaternion-frame-maximal, -codim-four) |
| `𝕆'_v` is an octonion subalgebra of 𝕊 containing `ℍ_s`, for every `v ⊥ u` | theorem, **to prove** | numerical (this document); Lean §6 (i) |
| `∂_v U(s)` is 4-dim; `∂_v ∩ ∂_{v'} = 0` for `v' ⊥ {u, v, uv}` | theorem, **to prove** | numerical; Lean §6 (ii)–(iii) |
| every associative subalgebra of 𝕆 has dim ≤ 4 (global) | theorem, deferred | Gram–Schmidt over `bil`; architecture ruling 2026-09-07 |
| observers require associativity | **postulate** | unchanged; support narrow (§1) |
| the bulk physics on `S³ ⊂ ℍ_s` is encoded on `∂_v U(s)` | **interpretation** | no map; no kill condition yet |
| information can be destroyed at the seams (B) | constitutional flag 1 | DERIV-sedenion vs AXIOM-1, unreconciled (addendum §5 item 1) |

## 5. Draft re-statement of DERIV-holographic for the beekeeper (constitutional; NOT applied)

Split the one entry into three, so a citation can say which part it rests on:

| Proposed id | Text | Kind / status | Anchors |
|---|---|---|---|
| **POST-observer-associativity** | "Observers require associativity: physics is hosted on an associative subalgebra." | postulate; support narrow (composition law; ℓ unique) | PROOF-associative-composition-iff; `assoc_self_zero_iff` |
| **DERIV-holographic-theorem** | "Quaternion frames span{1,u,v,uv} are associative subalgebras of 𝕆; no associative subalgebra properly contains one (frame-relative; global dim ≤ 4 deferred); the codimension of ℍ in 𝕆 is 4." | derived, **proved** | PROOF-quaternion-frame-maximal, PROOF-quaternion-frame-codim-four |
| **INTERP-holographic-boundary** | "The holographic boundary of a universe U(s) is the 4-dim gap `ℍ_s^⊥ ∩ 𝕆'_v` inside an encoding octonion `𝕆'_v ⊃ ℍ_s`; the seam boundary between universes is the zero-divisor locus (DERIV-sedenion). The encoding octonion is a datum not fixed by the landscape." | interpretation, **proposed** | this document; `boundary_octonion_check.py`; Lean §6 pending |

**Re-pointing the five dependents** (each currently `derived_from: DERIV-holographic`):

| Dependent | Needs which part | Note |
|---|---|---|
| DERIV-3plus1 ("quaternion structure: 1 + 3") | POST + DERIV-theorem | the only one that needs *just* the postulate and the proved algebra |
| DERIV-observation ("EM observation accesses ℂ ⊂ ℍ; measurement projects ℍ → ℂ → ℝ") | POST + DERIV-theorem (+ `pole_hosts_complex` for ℂ as a hosted algebra) | no boundary needed |
| DERIV-pati-salam (NCG on `A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)`) | DERIV-theorem (ℍ as the finite algebra's factor) | independent of the boundary interpretation |
| DERIV-arrow ("preservation + lossy projection ⇒ irreversibility; Γ monotonic") | POST + INTERP (the loss is a projection onto the boundary) + AXIOM-1 | sits next to flag 1: if loss is at the *seams* (B) it is DERIV-sedenion's, not the holographic boundary's |
| DERIV-constants (ħ, k, c as information-per-Γ-step conversions) | INTERP | rests entirely on the interpretation; weakest link |

## 6. Lean to write (cheap → not), all `QBP.Foundations` material, no Substrate edit

1. **(i) `𝕆'_v` is an octonion subalgebra of 𝕊 containing `ℍ_s`.** Closure of `ℍ'_v ⊕ ℍ'_v ℓ` under the sedenion product is the Cayley–Dickson doubling formula applied to the associative `ℍ'_v` (`cdLo_mul` / `cdHi_mul`); alternativity of the doubling of an associative algebra is a standard identity — moderate. Containment of `ℍ_s` is immediate from `ℓU = −Uℓ`.
2. **(ii) `dim ∂_v U(s) = 4`** — from `crystal_quatSpan_independent` and a rank count; easy given (i).
3. **(iii) Non-canonicity witness** — two explicit `v, v'` with `∂_v ∩ ∂_{v'} = 0`; easy.
4. **(iv) Global dim ≤ 4** — the deferred Gram–Schmidt; not needed for A.
5. **(v) Uniqueness of `u` up to sign for a non-pole crystal** — owed from the definition doc §6; independent.

## 7. Questions this puts to the beekeeper and to the definition conversation

1. **Two boundaries, two names** (holographic = A per universe; seam = B between universes) — adopt?
2. **Is the encoding octonion a datum of a universe?** If yes, `Universe` gains a field and the substrate gains a fibre; if it is a later crystallisation stage, the rule must act on it; if it is observer-relative, it belongs with POST-observer-associativity, not with the universe. This is doc §5 Q2, sharpened.
3. **Flag-3 re-statement** (§5): rule on the split and the re-pointing, or keep the single entry with the theorem anchors attached.
4. **Flag 1 placement:** under the two-boundaries reading, "information CAN be destroyed" is a statement about B (DERIV-sedenion), not about the holographic boundary; that narrows, but does not resolve, the tension with AXIOM-1.
5. **Kill condition for "holographic":** none exists until an encoding map is defined; propose the conversation is asked to produce *the form* such a map must take, not the map.
