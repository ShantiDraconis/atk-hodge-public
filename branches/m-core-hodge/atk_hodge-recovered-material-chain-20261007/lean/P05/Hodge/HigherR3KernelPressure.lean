import MCore.BackwardAudit.R3StandardBackend

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/--
No new Hodge endpoint is introduced here.
The existing standard backend already proves all transport bookkeeping once
the two genuinely geometric operations are supplied inside
CycleSpecializationGeometry.
-/
example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : PathGroupoidLaws S)
    (L : ParallelTransportLinearLaws M S)
    (C : CycleSpecializationGeometry M (reverseTransportOfPathGroupoid P)) :
    Nonempty (R3TransportContract M S) :=
  r3_transport_of_standard_backend P L C

#check CycleSpecializationGeometry.specializeCycle
#check CycleSpecializationGeometry.cycleClass_compat
#print axioms MCore.BackwardAudit.r3_transport_of_standard_backend

end P05.Hodge
