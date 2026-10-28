import MCore.Hodge

namespace MCore

/--
Counter-audit: the abstract semantic interface alone cannot imply the rational
Hodge conjecture.  There is a legitimate inhabitant of HodgeSemanticData whose
Hodge predicate is true for a class while rationalSpanOfCycles is false.

This does NOT refute the Hodge conjecture.  It proves that a concrete geometry
realization is part of the producer and cannot be skipped.
-/
def toyHodgeSemanticData : HodgeSemanticData where
  Variety := Unit
  Class := fun _ => Unit
  AlgebraicCycle := fun _ => Empty
  isSmoothProjective := fun _ => True
  isRationalHodgeClass := fun _ => True
  cycleClass := fun {X} z => Empty.elim z
  rationalSpanOfCycles := fun _ => False

theorem toyHodgeSemanticData_not_rationalHodge :
    ¬ RationalHodgeConjecture toyHodgeSemanticData := by
  intro h
  have hf : False := h () trivial () trivial
  exact hf

theorem semantic_interface_does_not_force_hodge :
    ¬ (∀ D : HodgeSemanticData, RationalHodgeConjecture D) := by
  intro h
  exact toyHodgeSemanticData_not_rationalHodge (h toyHodgeSemanticData)

#print axioms MCore.toyHodgeSemanticData_not_rationalHodge
#print axioms MCore.semantic_interface_does_not_force_hodge

end MCore
