import MCore.Hodge

namespace MCore.BackwardAudit

/-- Local Hodge closure obligation for one smooth projective variety and one
    rational Hodge class. -/
def HodgeInstanceClosed
    (D : MCore.HodgeSemanticData)
    (X : D.Variety)
    (α : D.Class X) : Prop :=
  D.rationalSpanOfCycles α

/-- The real global constructor required to close the Hodge endpoint. -/
structure HodgeWitnessConstructor (D : MCore.HodgeSemanticData) : Prop where
  construct :
    ∀ (X : D.Variety), D.isSmoothProjective X →
      ∀ α : D.Class X, D.isRationalHodgeClass α →
        HodgeInstanceClosed D X α

theorem constructor_implies_rational_hodge
    {D : MCore.HodgeSemanticData}
    (W : HodgeWitnessConstructor D) :
    MCore.RationalHodgeConjecture D := by
  intro X hX α hα
  exact W.construct X hX α hα

theorem rational_hodge_implies_constructor
    {D : MCore.HodgeSemanticData}
    (h : MCore.RationalHodgeConjecture D) :
    HodgeWitnessConstructor D :=
  ⟨fun X hX α hα => h X hX α hα⟩

theorem hodge_constructor_iff_endpoint
    {D : MCore.HodgeSemanticData} :
    HodgeWitnessConstructor D ↔ MCore.RationalHodgeConjecture D :=
  ⟨constructor_implies_rational_hodge, rational_hodge_implies_constructor⟩

/-- Structural compression is closed. The unresolved mathematics is exactly
    construction of this term from established geometry, not the implication
    from the constructor to the endpoint. -/
def hodgeWitnessConstructorBuilt : Bool := false

theorem hodge_witness_constructor_still_open :
    hodgeWitnessConstructorBuilt = false := by rfl

#print axioms constructor_implies_rational_hodge
#print axioms rational_hodge_implies_constructor
#print axioms hodge_constructor_iff_endpoint
#print axioms hodge_witness_constructor_still_open

end MCore.BackwardAudit
