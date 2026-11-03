import MCore.HodgeReduction

namespace MCore

/-!
# Concrete Hodge terminal law

This file uses the repository's existing semantic interface. It does not
construct the missing algebraic cycle payload; it proves the exact logical
relationship between the global conjecture and one obstructing Hodge class.
-/

def HodgeTerminalCertifies (D : HodgeSemanticData) : Prop :=
  RationalHodgeConjecture D

def HodgeTerminalRefutes (D : HodgeSemanticData) : Prop :=
  ∃ (X : D.Variety), D.isSmoothProjective X ∧
    ∃ α : D.Class X, D.isRationalHodgeClass α ∧
      ¬ D.rationalSpanOfCycles α

theorem hodge_terminal_certifies_iff_pointwise (D : HodgeSemanticData) :
    HodgeTerminalCertifies D ↔ PointwiseHodgeAlgebraicity D := by
  exact rationalHodge_iff_pointwise D

theorem not_hodge_terminal_certifies_iff_refutes (D : HodgeSemanticData) :
    ¬ HodgeTerminalCertifies D ↔ HodgeTerminalRefutes D := by
  classical
  simp [HodgeTerminalCertifies, HodgeTerminalRefutes, RationalHodgeConjecture]

theorem hodge_terminal_refute_is_material_obstruction
    {D : HodgeSemanticData}
    (h : HodgeTerminalRefutes D) :
    ∃ (X : D.Variety) (α : D.Class X),
      D.isSmoothProjective X ∧
      D.isRationalHodgeClass α ∧
      ¬ AlgebraicityAt D α := by
  rcases h with ⟨X, hX, α, hα, hnot⟩
  exact ⟨X, α, hX, hα, hnot⟩

theorem hodge_terminal_cert_refute_disjoint (D : HodgeSemanticData) :
    ¬ (HodgeTerminalCertifies D ∧ HodgeTerminalRefutes D) := by
  rintro ⟨hcert, href⟩
  exact (not_hodge_terminal_certifies_iff_refutes D).2 href hcert

#print axioms MCore.hodge_terminal_certifies_iff_pointwise
#print axioms MCore.not_hodge_terminal_certifies_iff_refutes
#print axioms MCore.hodge_terminal_refute_is_material_obstruction
#print axioms MCore.hodge_terminal_cert_refute_disjoint

end MCore
