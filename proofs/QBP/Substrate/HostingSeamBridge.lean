import QBP.Substrate.Hosting
import QBP.Foundations.SeamSpectrum

/-!
# QBP.Substrate.HostingSeamBridge — `Hosting.potential` IS `SeamSpectrum.potV` (#683 AC6)

**Substrate-layer discipline** (beekeeper's lift, 2026-09-07,
#473 `issuecomment-5574256922`).  *What this file hosts:* a single definitional
identification — the Substrate landscape potential
`QBP.Substrate.Hosting.potential` and the Foundations attack-2 potential
`QBP.Foundations.SeamSpectrum.potV` are the same function on `CDAlg ℝ 4`, both
`s ↦ N (cdLo s * cdHi s - cdHi s * cdLo s)`.
*What this file does NOT derive:* any new mathematical or physical content.  It
adds no theorem about either potential beyond their equality, transports no
result, and attaches no substrate reading to `SeamSpectrum.potV` (whose file
explicitly disclaims one).  Beekeeper ruling (2026-11-01): this bridge rides as
housekeeping under Tier-3 review because it adds no content.

## Why a bridge is needed

Foundations may not import Substrate (`scripts/check_layer_imports.py` rule 1),
so `SeamSpectrum.lean` re-declares the potential as `potV` rather than reusing
`Hosting.potential`.  Red Team #682 finding N5 asked that the identity of the two
be *checked by the kernel* rather than asserted by inspection; QBP#683 AC6 tracks
it.  Both directions of the import constraint are respected here: this file is
in Substrate and imports both layers.

The proofs are `rfl`: the two bodies are syntactically identical after name
resolution, so the kernel closes the goal by definitional unfolding.  Audit in §2.
-/

namespace QBP.Substrate.HostingSeamBridge

open QBP.Foundations
open QBP.Foundations.CDAlg

/-! ## 1. The identification -/

/-- **QBP#683 AC6 (RT #682 N5).**  The Substrate landscape potential equals the
    Foundations attack-2 potential pointwise:
    `Hosting.potential s = SeamSpectrum.potV s` for every `s : CDAlg ℝ 4`.
    Definitional (`rfl`). -/
theorem potential_eq_potV (s : CDAlg ℝ 4) :
    QBP.Substrate.Hosting.potential s = QBP.Foundations.SeamSpectrum.potV s := rfl

/-- **QBP#683 AC6 (RT #682 N5), function-level form.**
    `Hosting.potential = SeamSpectrum.potV` as functions `CDAlg ℝ 4 → ℝ`.
    Definitional (`rfl`). -/
theorem potential_eq_potV_fun :
    QBP.Substrate.Hosting.potential = QBP.Foundations.SeamSpectrum.potV := rfl

/-! ## 2. Completeness audit — `#print axioms` -/

#print axioms potential_eq_potV
#print axioms potential_eq_potV_fun

end QBP.Substrate.HostingSeamBridge
