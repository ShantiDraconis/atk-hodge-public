import MCore.BackwardAudit.R2AfterR3

namespace MCore.BackwardAudit

/-!
# R2 fiber algebraicity boundary

R1d has already chosen a Qbar Hodge point Q on the spread.  This file proves
that R2 contains no further logical packaging: existence of an R2 production
contract is exactly concrete algebraicity of the transported class in that
single selected fiber.
-/

/-- Exact R2 endpoint at the selected R1d point. -/
def R2FiberAlgebraicityTarget
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

/-- R2 production is definitionally equivalent, up to the witness wrapper, to
    the concrete cycle-span statement at the fixed Qbar Hodge fiber. -/
theorem r2_contract_iff_fiber_algebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) :
    Nonempty (R2PointProductionContract M S D) ↔
      R2FiberAlgebraicityTarget M D := by
  constructor
  · rintro ⟨R2⟩
    exact ⟨
      R2.produceCycle.combination,
      R2.produceCycle.combination_class
    ⟩
  · rintro ⟨C, hC⟩
    exact ⟨
      {
        produceCycle := {
          combination := C
          combination_class := hC
        }
      }
    ⟩

/-- At the propositional certification level, exact fiber algebraicity is
    sufficient to certify existence of an R2 production contract.  We return
    Nonempty rather than extracting a Type-valued witness from a Prop; this
    deliberately avoids Classical.choice. -/
theorem r2_nonempty_of_fiber_algebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S)
    (h : R2FiberAlgebraicityTarget M D) :
    Nonempty (R2PointProductionContract M S D) :=
  (r2_contract_iff_fiber_algebraicity D).2 h

/-- Conversely, an R2 witness gives precisely the target and nothing stronger. -/
theorem r2ProductionYieldsFiberAlgebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (R2 : R2PointProductionContract M S D) :
    R2FiberAlgebraicityTarget M D :=
  (r2_contract_iff_fiber_algebraicity D).1 ⟨R2⟩

inductive R2BoundaryStatus where
  | exactReductionProved
  | openMathematics
  deriving Repr, DecidableEq

structure R2FiberFrontier where
  wrapperReduction : R2BoundaryStatus
  fiberAlgebraicity : R2BoundaryStatus

def r2FiberFrontier : R2FiberFrontier :=
  {
    wrapperReduction := .exactReductionProved
    fiberAlgebraicity := .openMathematics
  }

theorem r2_wrapper_reduction_closed :
    r2FiberFrontier.wrapperReduction = .exactReductionProved := rfl

theorem r2_fiber_algebraicity_still_open :
    r2FiberFrontier.fiberAlgebraicity = .openMathematics := rfl

#print axioms MCore.BackwardAudit.r2_contract_iff_fiber_algebraicity
#print axioms MCore.BackwardAudit.r2_nonempty_of_fiber_algebraicity
#print axioms MCore.BackwardAudit.r2ProductionYieldsFiberAlgebraicity
#print axioms MCore.BackwardAudit.r2_wrapper_reduction_closed
#print axioms MCore.BackwardAudit.r2_fiber_algebraicity_still_open

end MCore.BackwardAudit
