import MCore.HodgeCanonicalSemanticModel
import MCore.HodgeExactRemaining
import MCore.HodgeGeometricBackends

namespace P05.Hodge

open MCore

/--
Forward-only construction target for P05-HODGE.

This file deliberately does not define a fake `hodgeInhabitant`.
An actual promotion must eventually construct `ConcreteAlgebraicityPayload M`
without adding an equivalent endpoint hypothesis.
-/
structure ConcreteInhabitantSkeleton
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  codimZero : CodimZeroComponentBackend G M
  codimOne : Lefschetz11DivisorBackend G M
  higherSpread : HigherSpreadProducer G
  higherQbar : HigherQbarPointProducer higherSpread
  higherFiber : HigherFiberCycleProducer M higherSpread higherQbar
  higherTransport : HigherTransportProducer M higherSpread

def ConcreteInhabitantSkeleton.toConstructiveMaterial
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (S : ConcreteInhabitantSkeleton G M) :
    HodgeConstructiveMaterial G M :=
  {
    p0 := S.codimZero
    p1 := S.codimOne
    higherSpread := S.higherSpread
    higherQbar := S.higherQbar
    higherR2 := S.higherFiber
    higherR3 := S.higherTransport
  }

theorem ConcreteInhabitantSkeleton.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (S : ConcreteInhabitantSkeleton G M) :
    ConcreteAlgebraicityPayload M :=
  S.toConstructiveMaterial.toConcretePayload

#check CodimZeroComponentBackend
#check Lefschetz11DivisorBackend
#check HigherSpreadProducer
#check HigherQbarPointProducer
#check HigherFiberCycleProducer
#check HigherTransportProducer
#check canonicalTerminal_iff_concretePayload

#print axioms P05.Hodge.ConcreteInhabitantSkeleton.toConcretePayload

end P05.Hodge
