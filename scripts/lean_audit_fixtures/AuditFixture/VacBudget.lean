/- Fixture (PR #829 Gemini r5 / Red Team r7 finding 6): an exponential ∧-chain. Default budget:
   flagged vacuous. A tiny budget (QBP_AUDIT_VACUITY_HEARTBEATS): UNDECIDED, which fails. -/
namespace AuditFixture.VacBudget

def P0 : Prop := True
def P1 : Prop := P0 ∧ P0
def P2 : Prop := P1 ∧ P1
def P3 : Prop := P2 ∧ P2
def P4 : Prop := P3 ∧ P3
def P5 : Prop := P4 ∧ P4
def P6 : Prop := P5 ∧ P5
def P7 : Prop := P6 ∧ P6
def P8 : Prop := P7 ∧ P7
def P9 : Prop := P8 ∧ P8
def P10 : Prop := P9 ∧ P9
def P11 : Prop := P10 ∧ P10
def P12 : Prop := P11 ∧ P11

theorem big : P12 := by
  have h0 : P0 := trivial
  have h1 : P1 := ⟨h0, h0⟩
  have h2 : P2 := ⟨h1, h1⟩
  have h3 : P3 := ⟨h2, h2⟩
  have h4 : P4 := ⟨h3, h3⟩
  have h5 : P5 := ⟨h4, h4⟩
  have h6 : P6 := ⟨h5, h5⟩
  have h7 : P7 := ⟨h6, h6⟩
  have h8 : P8 := ⟨h7, h7⟩
  have h9 : P9 := ⟨h8, h8⟩
  have h10 : P10 := ⟨h9, h9⟩
  have h11 : P11 := ⟨h10, h10⟩
  have h12 : P12 := ⟨h11, h11⟩
  exact h12

end AuditFixture.VacBudget
