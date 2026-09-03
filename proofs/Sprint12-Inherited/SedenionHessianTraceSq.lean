/-
  SedenionHessianTraceSq — the ONE `native_decide` theorem of the sedenion corpus,
  isolated out of `Sedenion.lean` (#613 / FAULT-S4-005).

  `hessian_traceSq_1152_universal` (a₄ = Tr(H²) = 1152 at all 42 zero divisors) is
  the only theorem in the Sprint12-Inherited corpus that retains `native_decide`
  after the #482 native_decide→kernel-`decide` migration (kernel `decide` is
  impractical: squaring the 16×16 Hessian for each of the 42 ZDs reduces
  pathologically — >3.5 min + >5 GB without converging; kernel-migration tracked
  #582). It carries `Lean.ofReduceBool` in its axiom set → compiler-computed, NOT
  kernel-clean.

  It is split into its own file so that `Sedenion.lean` is native_decide-FREE and
  its genuinely kernel-clean theorems (e.g. `zero_divisor_count_42`, the anchor
  behind `PROOF-42zd`) live in a clean file, anchorable under the C3-FULL evidence
  bar's file-level source scan. This is the CTH anchor source for the
  `internal-compute` anchor `PROOF-hessian`. Theorem-level `#print axioms`
  precision (which would make the split unnecessary) is tracked as #618.
-/
import Sedenion

/-- T6. The Hessian trace Tr(H²) = 1152 at ALL 42 zero divisors.
    This is the spectral invariant a₄ = 1152.

    #482 EXCEPTION (documented, tracked #582): this retains `native_decide`
    (kernel `decide` impractical — see the file header). Consequence: this theorem
    carries `Lean.ofReduceBool` in its axiom set (compiler-computed, not
    kernel-clean). Backs the `internal-compute` anchor `PROOF-hessian`. -/
theorem hessian_traceSq_1152_universal : checkAllHessianTracesSq1152 = true := by
  native_decide
