/-
TOOLCHECK T11 — building a non-associative algebra on the Mathlib hierarchy:
a coordinate `structure` with `@[ext]`, hand-written `Add`/`Zero`/`Neg`/`SMul`/`Mul`
instances, `AddCommGroup` (with `nsmulRec`/`zsmulRec`), `Module`,
`NonUnitalNonAssocRing`, `IsScalarTower` / `SMulCommClass`, and a constructed,
kernel-`decide`d non-associativity witness (the ✗ cell pattern).

Feature: QBP's octonions/sedenions are not in Mathlib, so `QBP/Foundations/CDAlg.lean`
builds `CDAlg R n` exactly this way and `ArtinSpan.lean` registers
`NonUnitalNonAssocRing` + the scalar-tower classes to use `NonUnitalAlgebra.adjoin`
(standard §9: target `NonUnitalNonAssocRing`, never `Ring`). The test algebra here is
ℤ³ with the cross product — a Lie algebra, so non-associative — small enough to
`decide`.

Used by (QBP, 2026-11-20 grep): `QBP/Foundations/CDAlg.lean` (structure + instances,
`AddCommGroup`/`Module`), `ArtinSpan.lean` (`NonUnitalNonAssocRing`, `IsScalarTower`,
`SMulCommClass`, import `Mathlib.Algebra.Algebra.NonUnitalSubalgebra`), `CDLifting.lean`,
`Alternator.lean`, `Breakdown.lean` (✗-cell witnesses).

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace QBPToolcheck.T11

/-- ℤ³ as a coordinate structure (QBP's `CDAlg R n` shape, fixed to `Fin 3`, `R = ℤ`). -/
structure V3 where
  /-- The coordinate vector. -/
  c : Fin 3 → ℤ

@[ext] theorem V3.ext' (x y : V3) (h : ∀ i, x.c i = y.c i) : x = y := by
  cases x; cases y; simp only [V3.mk.injEq]; funext i; exact h i

instance : DecidableEq V3 := fun x y =>
  decidable_of_iff (x.c = y.c) ⟨fun h => by cases x; cases y; simp_all, fun h => by rw [h]⟩

instance : Add V3 := ⟨fun x y => ⟨fun i => x.c i + y.c i⟩⟩
instance : Zero V3 := ⟨⟨fun _ => 0⟩⟩
instance : Neg V3 := ⟨fun x => ⟨fun i => -x.c i⟩⟩
instance : SMul ℤ V3 := ⟨fun r x => ⟨fun i => r * x.c i⟩⟩

/-- The cross product (non-associative, anti-commutative). -/
instance : Mul V3 := ⟨fun x y => ⟨![x.c 1 * y.c 2 - x.c 2 * y.c 1,
                                     x.c 2 * y.c 0 - x.c 0 * y.c 2,
                                     x.c 0 * y.c 1 - x.c 1 * y.c 0]⟩⟩

/-- Coordinates of the cross product (the simp entry point for the ring-axiom proofs). -/
@[simp] theorem mul_c (x y : V3) :
    (x * y).c = ![x.c 1 * y.c 2 - x.c 2 * y.c 1,
                  x.c 2 * y.c 0 - x.c 0 * y.c 2,
                  x.c 0 * y.c 1 - x.c 1 * y.c 0] := rfl

@[simp] theorem add_c (x y : V3) (i) : (x + y).c i = x.c i + y.c i := rfl
@[simp] theorem zero_c (i) : (0 : V3).c i = 0 := rfl
@[simp] theorem neg_c (x : V3) (i) : (-x).c i = -x.c i := rfl
@[simp] theorem smul_c (r : ℤ) (x : V3) (i) : (r • x).c i = r * x.c i := rfl

instance : AddCommGroup V3 where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  neg_add_cancel a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℤ V3 where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- `NonUnitalNonAssocRing`: distributivity + absorbing zero, NO associativity. -/
instance : NonUnitalNonAssocRing V3 where
  left_distrib a b c := by
    ext i; fin_cases i <;> simp <;> ring
  right_distrib a b c := by
    ext i; fin_cases i <;> simp <;> ring
  zero_mul a := by ext i; fin_cases i <;> simp
  mul_zero a := by ext i; fin_cases i <;> simp

instance : IsScalarTower ℤ V3 V3 where
  smul_assoc r x y := by
    ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

instance : SMulCommClass ℤ V3 V3 where
  smul_comm r x y := by
    ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- Basis vectors. -/
def e (k : Fin 3) : V3 := ⟨fun i => if i = k then 1 else 0⟩

/-- The ✗ cell, constructed: `(e₀ × e₀) × e₁ ≠ e₀ × (e₀ × e₁)` — a concrete
non-associating triple, kernel-checked by `decide` through the `DecidableEq` instance. -/
theorem cross_not_assoc : (e 0 * e 0) * e 1 ≠ e 0 * (e 0 * e 1) := by
  decide

/-- The witness is genuinely non-zero: the associator is `e₁`. -/
theorem associator_eq : e 0 * (e 0 * e 1) - (e 0 * e 0) * e 1 = -(e 1) := by
  decide

/-- A generic `NonUnitalNonAssocRing` lemma applied to the instance (hierarchy reuse). -/
theorem distrib_use (a b c : V3) : (a + b) * c = a * c + b * c := add_mul a b c

end QBPToolcheck.T11

#print axioms QBPToolcheck.T11.cross_not_assoc
#print axioms QBPToolcheck.T11.associator_eq
#print axioms QBPToolcheck.T11.distrib_use
