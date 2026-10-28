import MCore.HodgeMaterialInhabitant

namespace MCore.HodgeMaterialConstructionAudit

open MCore

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : CodimZeroCycleProducer G M) :
    CodimZeroConcretePayload M :=
  codimZeroCycleProducer_closes P

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : CodimOneCycleProducer G M) :
    BackwardAudit.Lefschetz11ConcreteLaw M :=
  P.toLefschetz11ConcreteLaw

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HigherMaterialProducer G M) :
    HigherCodimConcretePayload M :=
  higherMaterialProducer_closes P

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConcreteInhabitant G M) :
    ConcreteAlgebraicityPayload M :=
  H.toConcretePayload

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : HodgeConcreteInhabitant G M) :
    GradedRationalHodgeConjecture G :=
  H.toGradedHodge A

example
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : AnchoredHodgeInhabitant D G M) :
    HodgeTerminalCertifies D :=
  H.certifies

#print axioms MCore.codimZeroCycleProducer_closes
#print axioms MCore.CodimOneCycleProducer.toLefschetz11ConcreteLaw
#print axioms MCore.higherMaterialRun_yields_concreteSpan
#print axioms MCore.higherMaterialProducer_closes
#print axioms MCore.HodgeConcreteInhabitant.toConcretePayload
#print axioms MCore.HodgeConcreteInhabitant.toGradedHodge
#print axioms MCore.HodgeConcreteInhabitant.toTerminalCertifies
#print axioms MCore.AnchoredHodgeInhabitant.certifies

end MCore.HodgeMaterialConstructionAudit
