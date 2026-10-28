import MCore.HodgeGeometricBackends

namespace MCore.HodgeGeometricBackendsAudit

open MCore

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : CodimZeroComponentBackend G M) :
    CodimZeroCycleProducer G M :=
  B.toCycleProducer

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : Lefschetz11DivisorBackend G M) :
    CodimOneCycleProducer G M :=
  B.toCycleProducer

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HigherGeometricBackend G M) :
    HigherMaterialProducer G M :=
  B.toMaterialProducer

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeGeometricBackend G M) :
    HodgeConcreteInhabitant G M :=
  B.toConcreteInhabitant

example
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : FullyAnchoredHodgeBackend D G M) :
    HodgeTerminalCertifies D :=
  B.certifies

#print axioms MCore.CodimZeroComponentBackend.toCycleProducer
#print axioms MCore.codimZeroPayload_of_componentBackend
#print axioms MCore.abstract_core_does_not_force_codimZeroPayload
#print axioms MCore.abstract_core_does_not_force_codimZeroProducer
#print axioms MCore.Lefschetz11DivisorBackend.toCycleProducer
#print axioms MCore.Lefschetz11DivisorBackend.toConcreteLaw
#print axioms MCore.HigherGeometricBackend.toMaterialProducer
#print axioms MCore.HodgeGeometricBackend.toConcreteInhabitant
#print axioms MCore.HodgeGeometricBackend.toConcretePayload
#print axioms MCore.FullyAnchoredHodgeBackend.toAnchoredInhabitant
#print axioms MCore.FullyAnchoredHodgeBackend.certifies

end MCore.HodgeGeometricBackendsAudit
