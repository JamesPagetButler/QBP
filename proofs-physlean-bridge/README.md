# PhysLean ↔ QBP differential-test bridge (#490)

A toolchain-skew-immune differential test: it checks that **PhysLean's**
QuantumInfo Born-rule machinery and **QBP's** quaternion formalism independently
agree on the spin-1/2 angle-dependent measurement law (`cos²(θ/2)`), at the
JSON boundary.

## Why a separate project

This project deliberately does **not** share QBP's Lean toolchain:

| | QBP `proofs/` | this bridge |
|---|---|---|
| Lean | `v4.30.0` | `v4.29.1` (PhysLean's pin) |
| Mathlib | QBP's pin | PhysLean's `v4.29.1` (transitive) |
| Source | QBP foundations | `require physlib` from git |

Integration happens only through `tests/oracle_predictions.json`. The toolchain
skew is by design — neither side has to track the other's Lean version. **Do not
unify the pins.**

## Independence — what makes the match meaningful

`PhysleanBridge/SpinMeasurement.lean` derives, from PhysLean's *own* primitives:

* `spinKet θ` — the prepared state, a `Ket (Fin 2)` with amplitudes
  `(cos(θ/2), sin(θ/2))` (normalization proven).
* `zBasisPOVM` — the z-basis projective measurement `{ |0⟩⟨0|, |1⟩⟨1| }` as a
  PhysLean `POVM` (PSD + sum-to-identity proven).
* `probUp_eq : (zBasisPOVM.measure (MState.pure (spinKet θ))) 0 = cos²(θ/2)`
  — PhysLean's Born rule `⟪P₀, |ψ⟩⟨ψ|⟫ = Re Tr(diag(1,0)·|ψ⟩⟨ψ|)`, reduced to
  `cos²(θ/2)`. The `cos²` *emerges from the trace*; no QBP formula is copied.
* `probDown_eq` (`sin²(θ/2)`), `expectation_eq` (`cos θ`), `probUp_add_probDown`.

All six declarations are kernel-checked to depend only on
`{propext, Classical.choice, Quot.sound}` (`#print axioms` at the file's end).

## The noncomputability boundary (honest framing)

PhysLean's `POVM.measure` / `MState` / `HermitianMat` stack is `noncomputable`
(it lives over ℝ/ℂ). It **cannot be run** as compiled code, and running it would
be the `#eval`/`native_decide` trusted-compiler hole the federation Lean standard
forbids. So the executable does **not** evaluate PhysLean's measurement numerically.

Instead the independence lives in the **proofs**. The `physlean_oracle` executable
evaluates the *proven closed form* (`cos²(θ/2)` etc.) at the five angles using
`Float`, clearly labeled as an unverified numeric transcription of the proven law.
We never present `Float`/`#eval` output as a proof of a proposition — the
propositions are proved in `SpinMeasurement.lean`.

## Build & run

```bash
# from this directory; PhysLean's Mathlib comes from the Azure cache (lake update
# already fetched it). Only QuantumInfo compiles from source (~25 min first time).
lake update            # resolves physlib + its Mathlib; cache-gets Mathlib oleans
lake build PhysleanBridge.SpinMeasurement   # the proofs (axiom-audited)
lake build physlean_oracle                  # the JSON emitter
.lake/build/bin/physlean_oracle > /tmp/physlean_oracle.json

# differential test (green):
python3 diff_oracle.py --physlean /tmp/physlean_oracle.json \
  --qbp ../tests/oracle_predictions.json

# harness self-test (must report RED — proves the harness can fail):
python3 diff_oracle.py --physlean /tmp/physlean_oracle.json \
  --qbp ../tests/oracle_predictions.json \
  --corrupt "angle_dep_45.000000deg:prob_up:0.01"
```

## Files

* `PhysleanBridge/SpinMeasurement.lean` — the independent Born-rule proofs.
* `PhysleanBridge/Oracle.lean` — `physlean_oracle` exe; emits QBP-schema JSON.
* `PhysleanBridge/Probe.lean` — import smoke-test for the PhysLean API.
* `diff_oracle.py` — the differential test + AC-T4 self-test (TOL = 1e-6).
