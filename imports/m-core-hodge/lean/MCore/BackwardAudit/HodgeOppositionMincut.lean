import MCore.BackwardAudit.HodgeOppositionCriterion

namespace MCore.BackwardAudit

/--
Pointwise opposition package for one Hodge class.  The package is useful only
if its obstruction data are built independently of the target span witness.
-/
structure PointwiseHodgeOppositionBridge
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    (α : G.CohomologyQ X (2 * p)) where
  A : Type
  O : OppositionSpace A
  obstruction : A
  collapse : SelfOppositionCollapses O
  selfOpposed : SelfOpposed O obstruction
  vanishing_implies_span :
    Vanishes O obstruction → InConcreteCycleSpan M α

theorem pointwise_opposition_bridge_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (B : PointwiseHodgeOppositionBridge M α) :
    InConcreteCycleSpan M α :=
  B.vanishing_implies_span (B.collapse B.obstruction B.selfOpposed)

/--
Conversely, once span membership is already known, a trivial opposition
package can always be manufactured.  This is the circularity firewall.
-/
def pointwise_opposition_bridge_of_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (h : InConcreteCycleSpan M α) :
    PointwiseHodgeOppositionBridge M α :=
  {
    A := Unit
    O := {
      zero := ()
      opp := id
      opp_involutive := by intro x; cases x; rfl
    }
    obstruction := ()
    collapse := by
      intro x hx
      cases x
      rfl
    selfOpposed := rfl
    vanishing_implies_span := by
      intro _
      exact h
  }

theorem pointwise_opposition_iff_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)} :
    Nonempty (PointwiseHodgeOppositionBridge M α) ↔
      InConcreteCycleSpan M α := by
  constructor
  · rintro ⟨B⟩
    exact pointwise_opposition_bridge_closes B
  · intro h
    exact ⟨pointwise_opposition_bridge_of_span h⟩

def HodgeOppositionPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p)),
    G.isSmoothProjective X →
    G.isTypePP p α →
    Nonempty (PointwiseHodgeOppositionBridge M α)

theorem hodge_opposition_payload_iff_concrete_payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeOppositionPayload M ↔ ConcreteAlgebraicityPayload M := by
  constructor
  · intro h X p α hX hα
    exact (pointwise_opposition_iff_span (M := M) (α := α)).1
      (h X p α hX hα)
  · intro h X p α hX hα
    exact (pointwise_opposition_iff_span (M := M) (α := α)).2
      (h X p α hX hα)

theorem hodge_opposition_payload_iff_last_bit
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeOppositionPayload M ↔ HodgeLastBit M := by
  exact (hodge_opposition_payload_iff_concrete_payload M).trans
    (hodge_last_bit_iff_concrete_payload M).symm

#print axioms MCore.BackwardAudit.pointwise_opposition_bridge_closes
#print axioms MCore.BackwardAudit.pointwise_opposition_iff_span
#print axioms MCore.BackwardAudit.hodge_opposition_payload_iff_concrete_payload
#print axioms MCore.BackwardAudit.hodge_opposition_payload_iff_last_bit

end MCore.BackwardAudit
