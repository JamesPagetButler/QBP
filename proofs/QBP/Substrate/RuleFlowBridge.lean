import QBP.Substrate.RuleFlow
import QBP.Foundations.InFlightAlgebra

/-!
# QBP.Substrate.RuleFlowBridge — the Foundations closed form IS the rule's gradient (#690)

**Substrate-layer discipline** (beekeeper's lift, 2026-09-07,
#473 `issuecomment-5574256922`).  *What this file hosts:* the **identification**
of the Foundations closed-form gradient
(`QBP.Foundations.InFlightAlgebra.gradVof`, a verbatim copy of the closed form
that `RuleFlow.cdLo_gradV` / `RuleFlow.cdHi_gradV` prove) with the rule's own
gradient `QBP.Substrate.RuleFlow.gradV`, and the two memberships that this
identification transports from Foundations into the Substrate layer.
*What this file does NOT derive:* the rule (still a POSTULATE, #635), the
**existence** or uniqueness of integral curves of the rule field (`FLAG-rule-flow-open`),
**invariance** of the host algebra `𝕆_s` along a trajectory, the reverse
inclusion `ker Δ(s) ⊆ 𝕆_s` (that `𝕆_s` is the FULL kernel), the leaf space
`G₂/SO(4)`, the anneal, or the endpoint.  Nothing dynamical is proved or
upgraded here.

## What the bridge is for

`QBP/Foundations/InFlightAlgebra.lean` §9 proves the algebraic core
`gradVof s ∈ 𝕆_s` (`gradVof_mem_kernelAlgebra`), where `𝕆_s = H_s ⊕ H_s·ℓ` is
the Cayley–Dickson double of the host quaternion algebra
`H_s = span_ℝ{1, a, c, a·c}`, `a = cdLo s`, `c = Im (cdHi s)`.  But Foundations
may not import Substrate (`scripts/check_layer_imports.py` rule 1), so
`gradVof` there is a *re-declaration* of the right-hand sides of
`RuleFlow.cdLo_gradV` / `RuleFlow.cdHi_gradV` rather than `RuleFlow.gradV`
itself.  Until this file, the identity `gradVof = RuleFlow.gradV` was verified
only **textually** (issue #688 Lean interlude; the NOT-claimed clause of ledger
anchor `PROOF-gradient-lies-in-host-kernel-algebra`, cited as "#683 → #690").

This module states and proves it in Lean, in the Substrate layer where both
sides are in scope:

* `gradVlo_eq_cdLo_gradV`, `gradVhi_eq_cdHi_gradV` — the two component
  identities asserted in the Foundations header (l.546–548);
* `gradVof_eq_gradV` — the packaged sedenion-level identity;
* `gradV_mem_kernelAlgebra` — hence `RuleFlow.gradV s ∈ 𝕆_s` for the **rule's**
  gradient, for every sedenion `s` (no hypothesis: this is an identity of the
  closed form, not a statement on the state sphere);
* `smul_self_add_smul_gradV_mem_kernelAlgebra` — hence
  `α • s + β • RuleFlow.gradV s ∈ 𝕆_s` for all `α β : ℝ`.

That closes the "#683 → #690" NOT-claimed clause of the ledger anchor
`PROOF-gradient-lies-in-host-kernel-algebra`: the identity, and with it the
pointwise containment `RuleFlow.gradV s ∈ 𝕆_s`, are now claimed as proved.

## What is still OPEN after this file (do not over-read)

The containment proved here is **pointwise in `s`**: at each state, the rule's
gradient direction lies in the CD double of that state's host quaternion
algebra.  It says nothing about a *trajectory*.  Whether `s ↦ 𝕆_s` is constant
along an integral curve — leaf invariance, the first-integral claim — needs the
derivative of `s ↦ H_s` and the existence of the curve in the first place;
both remain OPEN under `FLAG-rule-flow-open` (#635).  `RuleFlow`'s own scope
statement is unchanged by this module: the rule is a POSTULATE and no flow is
constructed.

Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`;
`#print axioms` audit in §2.
-/

namespace QBP.Substrate.RuleFlowBridge

open QBP.Foundations QBP.Foundations.CDAlg

/-! ## 1. The bridge -/

/-- **Low component.**  The Foundations copy `gradVlo` is the low Cayley–Dickson
    component of the rule's gradient: `gradVlo s = cdLo (∇V s)`.  This is the
    identity asserted (textually) in the `InFlightAlgebra` header; both sides are
    `2 • (C·b̄ − b̄·C)` with `C = [a, b]`, so it is `RuleFlow.cdLo_gradV` plus the
    definitional identity `InFlightAlgebra.cdComm = RuleFlow.comm`. -/
theorem gradVlo_eq_cdLo_gradV (s : CDAlg ℝ 4) :
    QBP.Foundations.InFlightAlgebra.gradVlo s = cdLo (RuleFlow.gradV s) := by
  rw [RuleFlow.cdLo_gradV, InFlightAlgebra.gradVlo_def, InFlightAlgebra.cdComm_def,
    RuleFlow.comm]

/-- **High component.**  `gradVhi s = cdHi (∇V s)`; both sides are
    `2 • (ā·C − C·ā)`. -/
theorem gradVhi_eq_cdHi_gradV (s : CDAlg ℝ 4) :
    QBP.Foundations.InFlightAlgebra.gradVhi s = cdHi (RuleFlow.gradV s) := by
  rw [RuleFlow.cdHi_gradV, InFlightAlgebra.gradVhi_def, InFlightAlgebra.cdComm_def,
    RuleFlow.comm]

/-- **The bridge lemma (#690).**  The Foundations closed-form gradient equals the
    rule's gradient as sedenions: `gradVof s = RuleFlow.gradV s` for every
    `s : 𝕊 = CDAlg ℝ 4`.  No hypothesis on `s`.

    With this, every §9 statement of `QBP.Foundations.InFlightAlgebra` about
    `gradVof` becomes a statement about the *rule's* gradient — see
    `gradV_mem_kernelAlgebra` below.  It does **not** make any of them a
    statement about the *flow*: existence, uniqueness and leaf invariance stay
    OPEN (`FLAG-rule-flow-open`). -/
theorem gradVof_eq_gradV (s : CDAlg ℝ 4) :
    QBP.Foundations.InFlightAlgebra.gradVof s = RuleFlow.gradV s := by
  rw [InFlightAlgebra.gradVof, gradVlo_eq_cdLo_gradV, gradVhi_eq_cdHi_gradV,
    RuleFlow.cdLo_gradV, RuleFlow.cdHi_gradV, RuleFlow.gradV]

/-! ## 1b. The memberships, transported to the rule's gradient -/

/-- **`∇V(s) ∈ 𝕆_s` for the rule's gradient.**  For every sedenion `s = a + b·ℓ`,
    writing `c = Im b` and `H_s = span_ℝ{1, a, c, a·c} ⊆ 𝕆`, both Cayley–Dickson
    components of `RuleFlow.gradV s` lie in `H_s`, i.e. `RuleFlow.gradV s` lies in
    the CD double `𝕆_s = H_s ⊕ H_s·ℓ`.  Obtained from the Foundations algebraic
    core `InFlightAlgebra.gradVof_mem_kernelAlgebra` by rewriting along the bridge
    `gradVof_eq_gradV`.

    **Scope.**  Pointwise in `s`; no hypothesis (in particular not `s.coord 0 = 0`
    nor `N s = 1`).  This is NOT flow invariance of `𝕆_s`, which remains an OPEN
    ODE statement (`FLAG-rule-flow-open`). -/
theorem gradV_mem_kernelAlgebra (s : CDAlg ℝ 4) :
    InFlightAlgebra.InKernelAlgebra s (RuleFlow.gradV s) := by
  rw [← gradVof_eq_gradV]
  exact InFlightAlgebra.gradVof_mem_kernelAlgebra s

/-- **`α • s + β • ∇V(s) ∈ 𝕆_s`** for the rule's gradient and all `α β : ℝ`:
    the state and the rule's gradient direction at that state span a real plane
    inside the single CD double `𝕆_s`.  Foundations counterpart:
    `InFlightAlgebra.smul_self_add_smul_gradV_mem_kernelAlgebra` (stated for
    `gradVof`), transported along `gradVof_eq_gradV`.

    **Scope.**  Still pointwise: this is the statement that an explicit Euler-type
    combination at a *fixed* `s` stays in `𝕆_s`, not that a trajectory does. -/
theorem smul_self_add_smul_gradV_mem_kernelAlgebra (s : CDAlg ℝ 4) (α β : ℝ) :
    InFlightAlgebra.InKernelAlgebra s (α • s + β • RuleFlow.gradV s) := by
  rw [← gradVof_eq_gradV]
  exact InFlightAlgebra.smul_self_add_smul_gradV_mem_kernelAlgebra s α β

/-! ## 2. Completeness audit — `#print axioms` -/

#print axioms gradVlo_eq_cdLo_gradV
#print axioms gradVhi_eq_cdHi_gradV
#print axioms gradVof_eq_gradV
#print axioms gradV_mem_kernelAlgebra
#print axioms smul_self_add_smul_gradV_mem_kernelAlgebra

end QBP.Substrate.RuleFlowBridge
