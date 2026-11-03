import MCore.BackwardAudit.R3Contract

namespace HodgeR3Audit

open MCore
open MCore.BackwardAudit

/-- Exact logical content of the frozen R3 contract. -/
def R3ExactResidue
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  AlgebraicPointData M S → InConcreteCycleSpan M α

theorem r3_contract_iff_exact_residue
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα} :
    R3TransportContract M S ↔ R3ExactResidue M S := by
  constructor
  · intro R3
    exact R3.transport
  · intro h
    exact ⟨h⟩

/-- Circularity direction: if the original K15 target is already known, R3 is
    immediate by ignoring the fiber witness. Any R3 proof using this direction
    is therefore non-reductive. -/
theorem original_target_implies_r3
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (hTarget : InConcreteCycleSpan M α) :
    R3TransportContract M S :=
  ⟨fun _ => hTarget⟩

/-- Once R2 has supplied one actual algebraic-point witness, R3 is equivalent
    to the original concrete K15 target. This is the exact circularity cut. -/
theorem r3_iff_original_target_given_point
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : AlgebraicPointData M S) :
    R3TransportContract M S ↔ InConcreteCycleSpan M α := by
  constructor
  · intro R3
    exact R3.transport P
  · intro hTarget
    exact original_target_implies_r3 hTarget

/-- With the already-existing K15 adapter, the same equivalence reaches the
    semantic span conclusion at the original input. -/
theorem r3_iff_semantic_span_given_point
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : AlgebraicPointData M S) :
    R3TransportContract M S ↔ G.inCycleClassSpan p α := by
  exact
    (r3_iff_original_target_given_point P).trans
      (A.span_iff α).symm

#print axioms HodgeR3Audit.r3_contract_iff_exact_residue
#print axioms HodgeR3Audit.original_target_implies_r3
#print axioms HodgeR3Audit.r3_iff_original_target_given_point
#print axioms HodgeR3Audit.r3_iff_semantic_span_given_point

end HodgeR3Audit
