import MCore.HodgeMaterialFrontier
import MCore.HodgeTerminalLaw

namespace MCore.HodgeMaterialAudit

open MCore

example
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    ConcreteAlgebraicityPayload M ↔
      CodimZeroConcretePayload M ∧
      CodimOneConcretePayload M ∧
      HigherCodimConcretePayload M :=
  concretePayload_iff_materialSplit M

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : BackwardAudit.Lefschetz11ConcreteLaw M) :
    CodimOneConcretePayload M :=
  codimOnePayload_of_lefschetz11 L

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (P0 : CodimZeroH01Producer G M)
    (L : BackwardAudit.Lefschetz11ConcreteLaw M)
    (P2 : HigherH01Producer G M) :
    ConcreteAlgebraicityPayload M :=
  concretePayload_of_h01_split A P0 L P2

#print axioms MCore.concretePayload_iff_materialSplit
#print axioms MCore.codimOnePayload_of_lefschetz11
#print axioms MCore.codimZeroPayload_of_h01
#print axioms MCore.higherPayload_of_h01
#print axioms MCore.concretePayload_of_materialProducers
#print axioms MCore.concretePayload_of_h01_split

end MCore.HodgeMaterialAudit
