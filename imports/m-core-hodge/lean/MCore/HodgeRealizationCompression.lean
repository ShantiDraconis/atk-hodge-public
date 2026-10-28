import MCore.HodgeExactRemaining
import MCore.K25

namespace MCore

/-!
# Realization adapter compression

K24 already proves the semantic span predicate equivalent to the concrete
finite-cycle span once an OperationFaithfulConcreteModelObligation is supplied.
Therefore CycleSpanAdapter is not an independent terminal obligation.
-/

def cycleSpanAdapterOfK24
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (model : OperationFaithfulConcreteModelObligation G M) :
    CycleSpanAdapter G M :=
  {
    span_iff := by
      intro X p α
      exact k24_span_equivalence model α
  }

def cycleSpanAdapterOfK25
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (model : RealizedConcreteModelObligation G M) :
    CycleSpanAdapter G M :=
  cycleSpanAdapterOfK24 model.mechanics

/-- Final realization bundle after removing the redundant span-adapter input. -/
structure HodgeConcreteRealization
    (D : HodgeSemanticData)
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  semantic : GradedSemanticAdapter D G
  model : RealizedConcreteModelObligation G M

def HodgeConcreteRealization.toAdapters
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : HodgeConcreteRealization D G M) :
    HodgeRealizationAdapters D G M :=
  {
    semantic := R.semantic
    span := cycleSpanAdapterOfK25 R.model
  }

theorem HodgeConstructiveMaterial.toTerminalOfConcreteRealization
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : HodgeConcreteRealization D G M)
    (H : HodgeConstructiveMaterial G M) :
    HodgeTerminalCertifies D :=
  H.toTerminal R.toAdapters

#print axioms MCore.cycleSpanAdapterOfK24
#print axioms MCore.cycleSpanAdapterOfK25
#print axioms MCore.HodgeConcreteRealization.toAdapters
#print axioms MCore.HodgeConstructiveMaterial.toTerminalOfConcreteRealization

end MCore
