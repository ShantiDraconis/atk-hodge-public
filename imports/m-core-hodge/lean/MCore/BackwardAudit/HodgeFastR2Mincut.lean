import MCore.BackwardAudit.R2HardCore
import MCore.BackwardAudit.R3TrivialQbar

namespace MCore.BackwardAudit

/--
Fast exact Hodge min-cut on the constant Qbar regression route.

R1d is inhabited by trivialQbarDescent.
R3 is inhabited by r3TransportTrivialQbar.
The only remaining mathematical obligation on this route is the R2 fiber
algebraicity target, and its universal payload is endpoint-equivalent to
ConcreteAlgebraicityPayload.
-/
def HodgeFastR2OpenMath
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  TrivialQbarR2Payload M

theorem hodge_fast_r2_iff_concrete_payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeFastR2OpenMath M ↔ ConcreteAlgebraicityPayload M :=
  trivial_qbar_r2_payload_iff_concrete_payload M

theorem hodge_fast_r1d_closed
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    Nonempty
      (R1DescentPointContract
        (trivialSpreadQbar G X p α hX hα)) :=
  ⟨trivialQbarDescent⟩

theorem hodge_fast_r3_closed
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    Nonempty
      (R3TransportContract M
        (trivialSpreadQbar G X p α hX hα)) :=
  r3_trivial_qbar_nonempty

theorem hodge_fast_r2_pointwise_sufficient
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (R2 :
      R2PointProductionContract M
        (trivialSpreadQbar G X p α hX hα)
        (trivialQbarDescent
          (G := G) (X := X) (p := p)
          (α := α) (hX := hX) (hα := hα))) :
    InConcreteCycleSpan M α :=
  trivial_qbar_r2_is_sufficient R2

#print axioms MCore.BackwardAudit.hodge_fast_r2_iff_concrete_payload
#print axioms MCore.BackwardAudit.hodge_fast_r1d_closed
#print axioms MCore.BackwardAudit.hodge_fast_r3_closed
#print axioms MCore.BackwardAudit.hodge_fast_r2_pointwise_sufficient

end MCore.BackwardAudit
