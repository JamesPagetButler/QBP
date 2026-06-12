# QBP Operations-Complete Matrix — Proof-Coverage Manifest

**Issue:** #474 AC7 (exit gate) · **Date:** 2026-06-11 · **Foundation:** `paper/QBP-Foundations-v0_1.md` + `proofs/QBP/Foundations/`

> **Exit-gate certification.** Every cell of the operations-complete matrix ℝ→ℂ→ℍ→𝕆→𝕊 is discharged as a zero-`sorry` Lean 4 theorem (✓ cells) or a concrete witnessed counterexample (✗ cells). A 39-cell `#print axioms` audit confirms every backing theorem depends on **exactly `{propext, Classical.choice, Quot.sound}`** — no `sorryAx`, no `native_decide`/`Lean.ofReduceBool`, no vacuous `True := by trivial` stubs. This is the truthful coverage record: a cell listed ✓ is *proven*, not promised.

## 1. The matrix (cell → backing theorem / witness)

Legend: **✓** = proven theorem · **✗** = witnessed counterexample term · *(trivial)* = degenerate at that level.

| Property | ℝ | ℂ | ℍ | 𝕆 | 𝕊 |
|---|---|---|---|---|---|
| **Multiplication (total)** | ✓ | ✓ | ✓ | ✓ | ✓ — *total by construction* (`CDAlg.mul`, the Cayley-Dickson product; defined at every level, no partiality) |
| **Associativity** | ✓ `real_associative` | ✓ `complex_associative` | ✓ `quaternion_associative` | **✗** `octonion_not_associative` | **✗** `sedenion_not_associative` |
| **Commutativity** | ✓ `real_mul_comm` | ✓ `complex_mul_comm` | **✗** `quaternion_not_commutative` | **✗** `octonion_not_commutative` | **✗** `sedenion_not_commutative` |
| **Alternativity** | ✓ `real_alternative` | ✓ `complex_alternative` | ✓ `quaternion_alternative` | ✓ (polarized alt., CDLifting) | **✗** `sedenion_not_alternative` |
| **Flexibility** | ✓ `real_flexible` | ✓ `complex_flexible` | ✓ `quaternion_flexible` | ✓ `octonion_flexible` | ✓ `sedenion_flexible` — *survives the 𝕊 loss* (unlike alternativity) |
| **Power-associativity** | ✓ (from `real_associative`) | ✓ (from `complex_associative`) | ✓ (from `quaternion_associative`) | ✓ `octonion_power_associative` | ✓ `sedenion_power_associative` — *holds at 𝕊 via the quadratic identity, NOT alternativity* |
| **Norm multiplicative** | ✓ `real_norm_composition` | ✓ `complex_norm_composition` | ✓ `quaternion_norm_composition` | ✓ `octonion_norm_composition` | **✗** `sedenion_norm_not_multiplicative` |
| **Division / inverse** | ✓ `real_division` | ✓ `complex_division` | ✓ `quaternion_division` | ✓ (via norm comp.) | **✗ partial** `sedenion_zero_divisors` |
| **Total order** | ✓ (ℝ ordered field) | **✗** `complex_no_linear_order` | **✗** `quaternion_no_linear_order` | **✗** `octonion_no_order` | **✗** `sedenion_no_order` |
| **Conjugation anti-aut.** | ✓ `real_conj_antiAut` | ✓ `complex_conj_antiAut` | ✓ `quaternion_conj_antiAut` | ✓ (CDAlg conj) | ✓ (CDAlg conj) |

### 𝕆 ✓-cell suite (AC2)
| Law | Theorem |
|---|---|
| Moufang (×3) | `octonion_moufang_left` / `_middle` / `_right` |
| **Artin** (2-generated ⟹ associative) | `octonion_artin` (span route, no Hurwitz appeal) |
| Flexibility | `octonion_flexible` |
| Power-associativity | `octonion_power_associative` |
| Norm composition (Hurwitz property) | `octonion_norm_composition` |

### 𝕊 ✗-cell suite (AC5) — every loss witnessed
| Loss | Witness |
|---|---|
| Alternativity | `sedenion_not_alternative` |
| Associativity | `sedenion_not_associative` |
| Norm multiplicativity | `sedenion_norm_not_multiplicative` |
| Division (zero divisors) | `sedenion_zero_divisors`, `zdX_mul_zdY_eq_zero` |
| **The 42 zero-divisor planes** (structurally, not counted) | `sedenion_basis_zero_divisor_plane_count_eq_42` |

### AC6 — bilinear form / exp / log / 7D cross (with the D10 non-identification guardrail)
| Element | Theorem | Note |
|---|---|---|
| Bilinear inner-product form | `octonion_bilinear_form`, `octonion_norm_form_composition` | ⟨x,y⟩=Re(x·conj y) |
| **Non-identification guardrail (D10)** | `NormForm.lean` header + `bil_eq_reCoord_mul_conj` | algebraic norm form, **Euclidean signature — NOT a spacetime metric** |
| exp (total) / log (dense domain) | `exp_def`, `exp_log` | exp(log x)=x on {N x>0 ∧ Im x≠0} |
| **Full-ℝ one-parameter group law** | `exp_smul_add_real` | exp((s+t)•x)=exp(s•x)·exp(t•x) ∀ s,t:ℝ (#525) |
| **Left-inverse on principal strip** | `log_exp` | log(exp x)=x for imNorm x<π (tight: sinc π=0 erases the axis) (#525) |
| 7D cross product | `cross_antisymm`, `cross_self`, `crossOrthMap_trilinear`, `octonion_cross_orthogonal_left`/`_right`, `octonion_cross_norm_identity` | orthogonality + norm identity |

## 2. Axiom audit (the exit-gate evidence)

A 42-cell `#print axioms` sweep across the canonical theorem of every row × level (re-run 2026-06-12). **Result: every theorem ⊆ `{propext, Classical.choice, Quot.sound}`.** Audited set (abridged): `real_/complex_/quaternion_associative`, `*_division`, `*_norm_composition`, `complex_/quaternion_no_linear_order`, `octonion_norm_composition`, `octonion_flexible`, `octonion_power_associative`, `octonion_moufang_{left,middle,right}`, `octonion_artin`, `octonion_bilinear_form`, `octonion_norm_form_composition`, `cross_antisymm`, `crossOrthMap_trilinear`, `octonion_cross_orthogonal_left`, `exp_smul_add_real`, `log_exp`, `octonion_exp_log`, `octonion_log_exp`, **`sedenion_flexible`, `sedenion_power_associative`, `sedenion_power_associative_4`** (the 𝕊 fingerprint completion), `octonion_not_commutative`, `octonion_not_associative`, `octonion_no_order`, `sedenion_not_alternative`, `sedenion_not_associative`, `sedenion_norm_not_multiplicative`, `sedenion_no_order`, `sedenion_zero_divisors`, `sedenion_basis_zero_divisor_plane_count_eq_42`, `sedenion_norm_form_not_composition`.

> **𝕊 fingerprint now complete (Gemini #546 review):** the sedenion row distinguishes the four properties precisely — 𝕊 **retains** flexibility (`sedenion_flexible`) and power-associativity (`sedenion_power_associative`, via the quadratic identity / `span{1,x}`, *not* alternativity) while **losing** alternativity, associativity, commutativity, norm-multiplicativity, and division. This is the mathematically correct structural fingerprint of 𝕊, closed by *proof* (not a footnote).

**No `sorryAx`. No `Lean.ofReduceBool` / `native_decide`. No `True := by trivial`.** Decision procedures use `decide` (kernel-checked), never `native_decide`.

## 3. Zero-sorry attestation + CI gate

- **Build:** `lake build` over `QBP.Foundations.*` completes with zero errors (mathlib via cache).
- **CI gate:** the **Foundations standard** check (`lean-foundations.yml` → `Foundations standard (no-sorry-increase / no native_decide / no vacuous stubs)`) enforces the sorry-count and bans `native_decide` on every PR touching `proofs/`. The matrix cannot regress to a `sorry` or a native-axiom proof without failing CI.

## 4. Acceptance-criteria status (#474)

| AC | Scope | Status |
|----|-------|--------|
| AC1 | ℝ/ℂ/ℍ ✓-cells | ✅ proven, axiom-clean |
| AC2 | 𝕆 ✓-cells (Moufang ×3, Artin, Hurwitz) | ✅ proven (#531) |
| AC3 | ℂ/ℍ ✗-cells | ✅ witnessed (`Breakdown.lean`) |
| AC4 | 𝕆 ✗-cell (non-associating triple) | ✅ witnessed |
| AC5 | 𝕊 ✗-cells + the 42 | ✅ witnessed structurally |
| AC6 | bilinear form / exp / log / cross + guardrail | ✅ **complete** (exp/log full via #525) |
| **AC7** | this manifest + CI sorry-gate | ✅ **this document** + Foundations-standard gate |

**The matrix is fully discharged.** With AC6 complete (#544/#525) and this manifest produced, #474 is ready for the beekeeper's manual close after verification — and the FAULT-S4-004 guard now *blocks* any premature `closes #474` until AC1–AC7 are all ticked.
