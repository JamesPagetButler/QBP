/- Fixture (PR #829 Red Team r8, probe G7): the statement's SORT sits behind an `@[irreducible]`
   alias of `Prop`. `Meta.isProp` (whnfD) answers "not a proposition"; the `.all` sort fallback must
   still make `vac` and `vac2` candidates, and both are vacuous. -/
namespace AuditFixture.VacIrredSort

@[irreducible] def MyProp : Type := Prop

unseal MyProp in
def T : MyProp := True

unseal MyProp in
theorem vac : T := trivial

unseal MyProp in
def T2 : MyProp := ∀ _ : Nat, True ∧ True

unseal MyProp in
theorem vac2 : T2 := fun _ => ⟨trivial, trivial⟩

end AuditFixture.VacIrredSort
