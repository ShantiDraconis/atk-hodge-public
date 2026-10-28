import MCore.K15
import MCore.BackwardAudit.HypotheticalClosureOracle

namespace MCore.BackwardAudit

def TargetWitness
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    (α : G.CohomologyQ X (2 * p)) : Prop :=
  InConcreteCycleSpan M α

theorem targetWitness_unfold
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    (α : G.CohomologyQ X (2 * p)) :
    TargetWitness M α ↔
      ∃ c : CycleCombination G M X p, c.eval M = α := by
  rfl

theorem withOracle_extracts_targetWitness
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : HypotheticalClosure G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) :
    TargetWitness M α :=
  hypothetical_concrete_witness A H X p α hX hα

#print axioms MCore.BackwardAudit.targetWitness_unfold
#print axioms MCore.BackwardAudit.withOracle_extracts_targetWitness

end MCore.BackwardAudit
