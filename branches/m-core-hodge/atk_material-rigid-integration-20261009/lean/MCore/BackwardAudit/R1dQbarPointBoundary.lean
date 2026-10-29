import MCore.BackwardAudit.R1DescentBoundary

namespace MCore.BackwardAudit

/-!
# R1d exact Qbar Hodge-point boundary

This file removes the final wrapper ambiguity in R1d.  It does not prove that
such a point exists.  It proves that the R1d contract is exactly the existence
of a pathwise Hodge point defined over Qbar for the specific spread attached to
the specific endpoint input (X,p,alpha).
-/

/-- Literal geometric endpoint for R1d at one typed spread. -/
def R1dQbarHodgePointTarget
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ (y : S.Base) (γ : S.Path S.basepoint y),
    S.isHodgeAlong γ ∧
    S.fieldOfDefinition.isDefinedOverQbar y

/-- The existing QbarHodgePointData wrapper is exactly the literal target. -/
theorem qbarHodgePointData_iff_target
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (QbarHodgePointData S) ↔
      R1dQbarHodgePointTarget S := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.y, Q.path, Q.y_is_hodge, Q.y_is_defined_over_Qbar⟩
  · rintro ⟨y, γ, hHodge, hQbar⟩
    exact ⟨{
      y := y
      path := γ
      y_is_hodge := hHodge
      y_is_defined_over_Qbar := hQbar
    }⟩

/-- The R1DescentPointContract adds no mathematics beyond the same point. -/
theorem r1d_contract_iff_target
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (R1DescentPointContract S) ↔
      R1dQbarHodgePointTarget S := by
  constructor
  · rintro ⟨D⟩
    exact (qbarHodgePointData_iff_target S).1 ⟨D.point⟩
  · intro h
    rcases (qbarHodgePointData_iff_target S).2 h with ⟨Q⟩
    exact ⟨{ point := Q }⟩

inductive R1dBoundaryStatus where
  | exactReductionProved
  | openMathematics
  deriving Repr, DecidableEq

structure R1dExactFrontier where
  wrapperReduction : R1dBoundaryStatus
  qbarHodgePointExistence : R1dBoundaryStatus

def r1dExactFrontier : R1dExactFrontier :=
  {
    wrapperReduction := .exactReductionProved
    qbarHodgePointExistence := .openMathematics
  }

theorem r1d_wrapper_reduction_closed :
    r1dExactFrontier.wrapperReduction = .exactReductionProved := rfl

theorem r1d_qbar_hodge_point_still_open :
    r1dExactFrontier.qbarHodgePointExistence = .openMathematics := rfl

#print axioms MCore.BackwardAudit.qbarHodgePointData_iff_target
#print axioms MCore.BackwardAudit.r1d_contract_iff_target
#print axioms MCore.BackwardAudit.r1d_wrapper_reduction_closed
#print axioms MCore.BackwardAudit.r1d_qbar_hodge_point_still_open

end MCore.BackwardAudit
