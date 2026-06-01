# DERIVE-OR-DIE: Does ℍ-QM force the Monogamy of Mutual Information (MMI)?

**Commissioned by:** the beekeeper (PI), over a Counter-Team recommendation to drop.
**Author role:** mathematical-physics judge. Mandate: the real answer, not a confirmation of either prior.
**Date:** 2026-05-31.

---

## TL;DR Verdict (read this first)

| | |
|---|---|
| **Question** | Does Quaternionic QM (ℍ-QM) *force* MMI (I₃ ≤ 0) for all tripartite states? |
| **Verdict** | **(c) ILL-POSED → (b) DEAD.** The question has no well-defined answer because *multipartite* ℍ-QM is not canonically definable. Every construction that *does* make tripartite ℍ-states well-defined provably reduces the joint description to **complex QM** — whose cone already **violates** MMI. So even the repaired question answers "MMI is NOT forced." |
| **Inversion hypothesis** | **Not salvaged.** Going ℂ→ℍ does *not* shrink the entropy cone. The one rigorous handle we have (McKague) shows the ℍ correlation set is strictly *larger* (super-Tsirelson), the opposite of "more constraints → smaller cone." |
| **Mechanism status** | "Algebra restricts the entropy cone" is **falsified for the ℂ→ℍ step.** Whatever is true of stabilizer/holographic cones is not produced by climbing the Cayley–Dickson tower. |

The three Counter-Team objections are not hand-waved past below — they are the load-bearing structure of the verdict. Two of them (Moretti–Oppio, the tensor-product trap) independently kill the claim; the third (McKague super-Tsirelson) corroborates the kill from the correlation-set side.

---

## 1. The inequalities, stated precisely

For a tripartite state ρ_{ABC} with reductions ρ_A, ρ_{AB}, etc., and von Neumann entropy S(ρ) = −Tr(ρ log ρ):

**Tripartite information (our sign convention, fixed once):**

> **I₃(A:B:C) ≔ S(A) + S(B) + S(C) − S(AB) − S(AC) − S(BC) + S(ABC).**

**Monogamy of Mutual Information (MMI), holographic form:**

> **I₃(A:B:C) ≤ 0**, equivalently **S(AB) + S(AC) + S(BC) ≥ S(A) + S(B) + S(C) + S(ABC).**

This is the holographic-specific inequality (Hayden–Headrick–Maloney), strictly stronger than and **not** implied by Strong Subadditivity (SSA: S(AB)+S(BC) ≥ S(B)+S(ABC)). SSA holds in all of ℂ-QM; MMI does **not**.

**Convention check (numerical, ℂ-QM).** Take the GHZ₄ state (|0000⟩+|1111⟩)/√2 and trace out the fourth party; the reduced ρ_{ABC} gives, computed directly:

```
S(A)=S(B)=S(C)=1,  S(AB)=S(AC)=S(BC)=1,  S(ABC)=1
I3 = (1+1+1) − (1+1+1) + 1 = +1  > 0   →  MMI VIOLATED
```

So the convention is anchored and the premise is confirmed: **ordinary complex QM genuinely violates MMI** (I₃ = +1 here). MMI is a property of *special* states (stabilizer, holographic), not of ℂ-QM at large. The QBP question is whether the *algebra* ℍ forces what ℂ does not.

---

## 2. Which multipartite ℍ-QM construction is being analyzed — and its (non-)canonicity

**This is the crux, per Counter-Team objection 1. There is no canonical answer, so I enumerate the live options and analyze each.**

A quaternionic Hilbert space is a **left ℍ-module** with an ℍ-valued inner product. Because ℍ is non-commutative, the naive bilinear tensor product H_A ⊗_ℍ H_B is **not** a quaternionic Hilbert space: scalar multiplication is not well-defined (left action on the first factor clashes with the requirement that the product be an ℍ-module), and as McKague notes operationally, R_i⊗I and I⊗R_j fail to commute, so "the evolution of a subsystem cannot be considered without the whole." There is **no functorial monoidal structure** on left-ℍ-modules.

The candidate repairs, and what each costs:

| # | Construction | Reference | What it actually is | Cost / verdict-relevant property |
|---|---|---|---|---|
| 1 | **Naive ⊗_ℍ over ℍ** | — | Not an ℍ-Hilbert space at all | Ill-defined. No state space, no entropy. **No I₃ to compute.** |
| 2 | **⊗ over the real center ℝ** | trivial | Real tensor of underlying real vector spaces | Loses the quaternionic (and even complex) phase structure; gives a *real* QM joint system. Not "ℍ-QM." |
| 3 | **Bimodule tensor product** | Razon–Horwitz (1991/92) | ⊗ of ℍ-bimodules with a chosen **complex projection of the scalar product** ("complex geometry"), via symplectic q = z + j z′ | **Well-defined — but the joint scalar product is complex.** This is the standard "solution." See §3. |
| 4 | **Complexification ℂ⊗_ℝℍ ≅ M₂(ℂ)** | Adler §4 | Embed in 2×2 complex matrices | Joint system lives in a **complex** Hilbert space by construction. |
| 5 | **Adler's composite-system treatment** | Adler 1995, *QQMQF* §4.4 | Adler explicitly flags the tensor-product problem and works with the **symplectic (complex) component** for multiparticle states | Adler himself routes multiparticle ℍ-QM through the complex projection. |
| 6 | **McKague operational pair** | arXiv:0911.1761 | Two parties sharing a single ℍ-state with *time-ordered local operations*; never forms a categorical ⊗ | Well-defined as a *protocol*, not as a state space. Produces super-Tsirelson correlations (§4). |

**Honest statement of non-canonicity:** options 1–2 are non-starters (no theory / wrong theory). Options 3, 4, 5 are the *only* mathematically respectable ways to get a multipartite ℍ-QM **state space with density operators and hence entropies** — and **all three are built on the complex projection**. Option 6 is the only genuinely "more quaternionic" multipartite object, and it is not a state space at all (no well-defined ρ_{ABC}, hence no I₃). 

So the analyzable constructions are **3/4/5**, and I analyze those. The verdict will turn on the fact that this choice is **not** an arbitrary technicality — it is *forced*, by two independent theorems, onto the complex sector.

---

## 3. The derivation: do constructions 3/4/5 force I₃ ≤ 0?

**Claim:** For any multipartite ℍ-QM theory in which density operators and von Neumann entropies of subsystems are well-defined (constructions 3/4/5), the entropy cone is **identical to the ℂ-QM entropy cone**. Hence I₃ ≤ 0 is **not** forced; the GHZ₄ counterexample of §1 transports verbatim.

**Argument (Horwitz–Biedenharn / Razon–Horwitz "complex geometry"):**

1. Every quaternion has the **symplectic decomposition** q = z + j z′ with z, z′ ∈ ℂ_i (the complex subfield generated by 1, i). Equivalently, ℍ ≅ ℂ_i ⊕ ℂ_i j as a left ℂ_i-module, and right-multiplication structure realizes ℍ ↪ M₂(ℂ).

   *Verified numerically:* the 2×2 complex reps i=diag(i,−i), j=[[0,1],[−1,0]] satisfy i²=j²=−1, ij=k, ji=−k.

2. An ℍ-Hilbert space of quaternion-dimension n maps, under symplectic doubling, to **ℂ^{2n}**. (Verified: a "quaternionic qubit," ℍ², ↦ ℂ⁴.)

3. To define a tensor product that is *again a module with a usable inner product*, Razon–Horwitz / Horwitz–Biedenharn require **complex geometry**: the physical scalar product is the **ℂ_i-projection** ⟨·,·⟩_ℂ ≔ (1/2)(⟨·,·⟩_ℍ − i⟨·,·⟩_ℍ i) of the quaternionic one. This is the *only* projection that is associative-compatible across factors.

4. But the ℂ_i-projected scalar product **is** the inner product of a standard complex Hilbert space ℋ_ℂ = ℂ^{2n}. On ℋ_ℂ the tensor product is the ordinary one, density operators are ordinary complex PSD trace-1 matrices, and S(ρ) is the ordinary von Neumann entropy.

5. **Therefore the set of achievable tripartite reduced-state triples {S(A),…,S(ABC)} for constructions 3/4/5 is exactly the ℂ-QM set.** Same cone. The GHZ₄ realization sits inside ℂ^{2n} (just embed the 4 qubits in the complex sector), giving **I₃ = +1 > 0**. MMI is violated within the construction's own state space.

**Conclusion of the derivation:** I do not need a bespoke "quaternionic" counterexample — the construction *is* ℂ-QM on the nose, and ℂ-QM's existing MMI violation is inherited. **I₃ ≤ 0 is NOT forced.** The extra quaternionic directions (the j z′ part) do not add *constraints*; they add *doubled (charge-conjugate-like) dimensions*, which can only enlarge or preserve the achievable entropy set, never shrink it below the complex cone.

This is the exact opposite of the inversion hypothesis. Climbing ℂ→ℍ, *to the extent the joint theory is even definable*, gives **the same cone**; and the one place where ℍ genuinely departs from ℂ (non-commuting local operations, §4) **enlarges** the correlation set.

---

## 4. Reconciliation with McKague super-Tsirelson (objection 2)

McKague (arXiv:0911.1761) builds, from the shared ℍ-state (1/√2)(|00⟩ + k|11⟩) with **time-ordered** local rotations R_i, R_j, a **perfect PR box**: x⊕y = ab with probability 1, i.e. CHSH value **4**, blowing past Tsirelson's 2√2 ≈ 2.828. The engine is exactly ij ≠ ji: the relative phase picked up depends on operation order, which is impossible in commutative ℂ-QM.

**Reconciliation — these point the same way:**

- A super-Tsirelson, indeed PR-box, correlation set is **strictly larger** than ℂ-QM's. "More algebraic structure ⇒ fewer correlations ⇒ smaller entropy cone" is therefore **false at the level of correlations**, which is the more primitive (and theorem-backed) object. The QBP mechanism predicts the wrong direction.
- McKague's construction is *not* a tensor-product state — it is the option-6 operational protocol with **no well-defined ρ_{ABC}**. So it cannot be used to compute I₃. This is consistent with §2: the genuinely-more-quaternionic object refuses to be a state space, and the moment you force it to be one (constructions 3/4/5) you fall back to ℂ.
- Net: McKague **corroborates** the verdict. Where ℍ-QM is distinctively quaternionic it is *bigger*, not smaller; where it is forced to be a state space with entropies it *is ℂ-QM*. There is no regime in which it is "smaller than ℂ" — which is what "forcing MMI" would require.

---

## 5. Reconciliation with Moretti–Oppio (objection 3) — the decisive theorem

Moretti–Oppio (arXiv:1709.09246, *Ann. Henri Poincaré*): for an elementary relativistic system (locally-faithful irreducible strongly-continuous unitary rep of Poincaré in an ℍ-Hilbert space) with **non-negative squared mass**, there exists a **unique-up-to-sign, Poincaré-invariant complex structure J commuting with all observables**, giving a physically equivalent reformulation in a **complex** Hilbert space. Their own stated payoff: in that complex formulation "all self-adjoint operators are observables, Noether's theorem holds, **and composite systems may be given in terms of tensor product.**"

That last clause is the whole ballgame. The tensor product — the very thing needed to *define* tripartite states — exists **only after** the reduction to ℂ. Read against §3:

- The Horwitz–Biedenharn complex structure (the symplectic j-projection) and the Moretti–Oppio J are the **same object arrived at two ways**: one from the algebra of composition, one from spacetime symmetry. Two independent derivations, one conclusion: *the definable joint theory is complex.*
- **Evasion would require giving up the hypotheses:** non-negative m², or Poincaré symmetry, or irreducibility. A theory that abandons non-negative m² (tachyonic), or Poincaré invariance, or that is reducible, *might* host a genuinely-quaternionic composite structure — but (i) that is no longer "physically reasonable QM," and (ii) nobody has exhibited such a construction with well-defined subsystem entropies, let alone shown its cone is *smaller*. McKague suggests the opposite would happen (correlations grow).

So Moretti–Oppio independently forces: **no distinct ℍ-QM entropy cone exists for physically reasonable theories — it is the ℂ-QM cone, which violates MMI.**

---

## 6. Why "ILL-POSED → DEAD," not merely "DEAD"

The cleanest honest statement is verdict **(c)**: *the question as posed is ill-defined*, because "all tripartite ℍ-QM states" presupposes a canonical multipartite ℍ-QM, which does not exist (objection 1, the tensor-product trap). 

But (c) does not let the hypothesis off the hook, so it collapses into **(b) DEAD**: every repair that *creates* a tripartite state space (constructions 3/4/5) is provably the complex theory (§3), corroborated by Moretti–Oppio (§5); and the only genuinely-quaternionic multipartite object (§4) is not a state space and is *bigger* not smaller. There is no reading of the question under which ℍ forces I₃ ≤ 0.

**The "algebra restricts the entropy cone" mechanism is therefore not salvaged by the ℂ→ℍ step.** If QBP wants a cone-shrinking mechanism, ℍ-QM is the wrong vehicle: the Cayley–Dickson step ℂ→ℍ either (a) does nothing to the cone (it stays complex) or (b) enlarges the correlation set. Stabilizer/holographic MMI comes from *state-class restrictions* (graph/stabilizer structure, RT geometry), **not** from changing the scalar field.

---

## 7. ESCALATE items for the theory teams

These are the only ways the verdict could move, and each is itself an open research question — flagged honestly so the PI can decide whether any is worth a separate sprint:

1. **ESCALATE-1 (non-Poincaré / non-relativistic ℍ-QM).** Moretti–Oppio's reduction uses Poincaré + m²≥0. *Is there a physically motivated **non-relativistic** ℍ-QM with a genuinely quaternionic, well-defined multipartite state space (density operators, entropies) that does NOT reduce to ℂ?* If yes, its entropy cone must be computed directly. Prior on outcome: low value — the tensor-product trap (objection 1) is algebraic, not relativistic, and bites independently of Poincaré. But this is the one logically open door.

2. **ESCALATE-2 (octonionic step, ℍ→𝕆).** The QBP tower premise is ℂ→ℍ→𝕆→𝕊. This report kills the ℂ→ℍ step. *Does the ℍ→𝕆 (non-associative) step do something categorically different to the correlation/entropy structure?* Non-associativity breaks even more than non-commutativity — almost certainly makes a state space *harder* to define, not easier, so the cone-shrinking intuition is likely worse, not better. Recommend the theory team not bank on it without a definability result first.

3. **ESCALATE-3 (right-cone analogy).** If the real target is "an algebraic principle that yields stabilizer-like / holographic MMI," the literature route is **state-class** restrictions (stabilizer formalism, RT/holographic constraints, hypergraph states), not field changes. Recommend redirecting the "algebra restricts the cone" research energy there. This is a *positive* redirection, not a dead end.

---

## 8. Sources

- McKague, *Quaternionic quantum mechanics allows non-local boxes*, arXiv:0911.1761 — [abs](https://arxiv.org/abs/0911.1761), [ar5iv](https://ar5iv.labs.arxiv.org/html/0911.1761). (Perfect PR-box / CHSH=4 from ij≠ji; tensor product ill-defined; R_i⊗I, I⊗R_j non-commuting.)
- Moretti & Oppio, *Quantum theory in quaternionic Hilbert space: How Poincaré symmetry reduces the theory to the standard complex one*, arXiv:1709.09246, Ann. Henri Poincaré — [abs](https://arxiv.org/abs/1709.09246). (Unique complex structure from Poincaré + m²≥0; tensor product / composite systems only well-defined after complex reduction.)
- Razon & Horwitz, *Tensor product of quaternion Hilbert modules*, Acta Appl. Math. — [Springer](https://link.springer.com/article/10.1007/BF00046890); *Projection operators and states…* — [Springer](https://link.springer.com/article/10.1007/BF00046891). (Tensor product via complex projection / "complex geometry"; symplectic q = z + j z′.)
- Horwitz & Biedenharn, *Quaternion quantum mechanics: Second quantization and gauge fields*, Ann. Phys. / [ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/000349168490068X). (Complex geometry permits the single-particle tensor product.)
- Adler, *Quaternionic Quantum Mechanics and Quantum Fields* (Oxford, 1995) — [ref](https://books.google.com/books/about/Quaternionic_Quantum_Mechanics_and_Quant.html?id=WYYemAEACAAJ). (Composite systems routed through the symplectic/complex component.)
- Hayden, Headrick, Maloney, *Holographic Mutual Information is Monogamous* (orig. MMI / I₃≤0 statement) — standard reference for the inequality.

---

## Appendix: numerical checks performed

- **I₃ convention + ℂ-QM violation:** GHZ₄ → trace 4th party → ρ_{ABC}; all 1-, 2-, 3-party entropies = 1 bit; **I₃ = +1 > 0**. Confirms MMI is violated in plain ℂ-QM, so the premise of the task is sound.
- **Quaternion algebra rep:** i=diag(i,−i), j=[[0,1],[−1,0]] ⇒ i²=j²=−1, ij=k, ji=−k. Confirms non-commutativity (the McKague engine).
- **Symplectic doubling:** ℍⁿ ↦ ℂ^{2ⁿ}; "quaternionic qubit" ℍ² ↦ ℂ⁴. Confirms the construction-3/4/5 reduction is dimensionally the complex theory plus a doubled (j-direction) sector that the complex-geometry projection discards.
