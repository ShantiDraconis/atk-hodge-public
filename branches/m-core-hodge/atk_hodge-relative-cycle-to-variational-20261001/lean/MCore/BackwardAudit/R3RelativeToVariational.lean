import MCore.BackwardAudit.R3RelativeCycleCut
import MCore.BackwardAudit.R3CombinationMinimal

namespace MCore.BackwardAudit

/--
Direct bridge from the geometric relative-cycle backend to the exact minimal
R3 variational-algebraicity payload.

No new Hodge assumption is introduced here.  The hypotheses are exactly the
already-audited geometric inputs:
* path-groupoid inversion;
* linear parallel transport;
* genuine relative-cycle extension;
* cycle-class compatibility under back transport.
-/
theorem variational_algebraicity_of_relative_cycle_backend
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
    (B : RelativeCycleBackend M (reverseTransportOfPathGroupoid P)) :
    R3VariationalAlgebraicityPayload M S := by
  have hR3 : Nonempty (R3TransportContract M S) :=
    r3_transport_of_relative_cycle_backend P L B
  exact
    (r3_contract_iff_variational_algebraicity).1 hR3

/--
Combination-level form of the same bridge.  Useful when a downstream consumer
works with explicit finite cycle combinations instead of the proposition-level
span predicate.
-/
theorem combination_payload_of_relative_cycle_backend
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
    (B : RelativeCycleBackend M (reverseTransportOfPathGroupoid P)) :
    R3CombinationPayload M S :=
  (combination_payload_iff_variational_algebraicity).2
    (variational_algebraicity_of_relative_cycle_backend P L B)

/--
Exact dependency compression for R3 on one spread: after standard local-system
laws, the only geometric backend required by this route is RelativeCycleBackend.
-/
theorem relative_cycle_backend_closes_r3
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : PathGroupoidLaws S)
    (L : ParallelTransportLinearLaws M S) :
    RelativeCycleBackend M (reverseTransportOfPathGroupoid P) →
      R3VariationalAlgebraicityPayload M S :=
  fun B => variational_algebraicity_of_relative_cycle_backend P L B

#print axioms MCore.BackwardAudit.variational_algebraicity_of_relative_cycle_backend
#print axioms MCore.BackwardAudit.combination_payload_of_relative_cycle_backend
#print axioms MCore.BackwardAudit.relative_cycle_backend_closes_r3

end MCore.BackwardAudit
