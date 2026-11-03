import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR2Audit

open MCore
open MCore.BackwardAudit

/-- R2 is definitionally the concrete finite-cycle-span obligation for the
    transported class at the R1d-selected fiber. -/
theorem r2_data_iff_concrete_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (Q : QbarHodgePointData S) :
    Nonempty (R2FiberCycleData M S Q) ↔
      InConcreteCycleSpan M (S.transportedAlpha Q.path) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.combination, C.combination_class⟩
  · rintro ⟨c, hc⟩
    exact ⟨{
      combination := c
      combination_class := hc
    }⟩

/-- Once the already-existing K15 adapter is supplied, R2 is also exactly the
    semantic inCycleClassSpan conclusion for the transported class. -/
theorem r2_data_iff_semantic_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (Q : QbarHodgePointData S) :
    Nonempty (R2FiberCycleData M S Q) ↔
      G.inCycleClassSpan p (S.transportedAlpha Q.path) := by
  exact
    (r2_data_iff_concrete_span (M := M) Q).trans
      (A.span_iff (S.transportedAlpha Q.path)).symm

/-- R1d contributes the Hodge-type premise at y, but it does not manufacture
    the R2 algebraicity conclusion. -/
theorem r1d_supplies_hodge_not_cycle_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) :
    G.isTypePP p (S.transportedAlpha D.point.path) :=
  D.point.y_is_hodge

/-- Exact open R2 proposition after R1d. This is not an axiom; it is an alias
    for the witness type already frozen at the U-REF. -/
def R2ExactResidue
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) : Prop :=
  InConcreteCycleSpan M (S.transportedAlpha D.point.path)

theorem r2_contract_is_exact_residue
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) :
    Nonempty (R2FiberCycleData M S D.point) ↔
      R2ExactResidue M D := by
  exact r2_data_iff_concrete_span (M := M) D.point

#print axioms HodgeR2Audit.r2_data_iff_concrete_span
#print axioms HodgeR2Audit.r2_data_iff_semantic_span
#print axioms HodgeR2Audit.r1d_supplies_hodge_not_cycle_span
#print axioms HodgeR2Audit.r2_contract_is_exact_residue

end HodgeR2Audit
