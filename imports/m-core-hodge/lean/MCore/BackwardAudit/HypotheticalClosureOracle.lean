import MCore.K16

namespace MCore.BackwardAudit

/-- Specification-only oracle: exactly the final graded rational Hodge
    statement, supplied as an explicit hypothesis. -/
def HypotheticalClosure (G : GradedRationalHodgeData) : Prop :=
  GradedRationalHodgeConjecture G

theorem hypothetical_pointwise
    {G : GradedRationalHodgeData}
    (H : HypotheticalClosure G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) :
    G.inCycleClassSpan p α :=
  H X hX p α hα

theorem hypothetical_concrete_witness
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : HypotheticalClosure G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) :
    InConcreteCycleSpan M α :=
  (A.span_iff α).1 (hypothetical_pointwise H X p α hX hα)

def specificationOracleOnly : Bool := true

theorem specification_oracle_only : specificationOracleOnly = true := by
  rfl

#print axioms MCore.BackwardAudit.hypothetical_pointwise
#print axioms MCore.BackwardAudit.hypothetical_concrete_witness
#print axioms MCore.BackwardAudit.specification_oracle_only

end MCore.BackwardAudit
