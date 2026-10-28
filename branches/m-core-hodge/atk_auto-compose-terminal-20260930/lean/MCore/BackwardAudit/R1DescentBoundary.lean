import MCore.BackwardAudit.TypedVariationalGeometry

namespace MCore.BackwardAudit

/-- Exact typed boundary for R1d: a point of THIS alpha-Hodge locus together
    with the repository's field-of-definition predicate. No cycle is included. -/
structure QbarHodgePointData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  y : S.Base
  path : S.Path S.basepoint y
  y_is_hodge : S.isHodgeAlong path
  y_is_defined_over_Qbar : S.fieldOfDefinition.isDefinedOverQbar y

/-- R1d closure contract. Constructing this term is the descent/Qbar-point
    obligation; the definition itself proves nothing about its existence. -/
structure R1DescentPointContract
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  point : QbarHodgePointData S

/-- R2 proper: after R1d has fixed a Qbar Hodge point, produce a finite
    rational cycle combination representing the transported class there. -/
structure R2FiberCycleData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  combination : CycleCombination G M (S.Family Q.y) p
  combination_class :
    combination.eval M = S.transportedAlpha Q.path

/-- Mechanical assembly into the earlier combined witness. -/
def assembleAlgebraicPointData
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (Q : QbarHodgePointData S)
    (C : R2FiberCycleData M S Q) :
    AlgebraicPointData M S :=
  {
    y := Q.y
    path := Q.path
    y_is_hodge := Q.y_is_hodge
    y_is_defined_over_Qbar := Q.y_is_defined_over_Qbar
    combination := C.combination
    combination_class := C.combination_class
  }

/-- A deliberately weak constant spread showing that merely inhabiting
    SpreadData does not imply R1d. Its field-of-definition predicate is empty.
    This is a type-audit countermodel, not geometry. -/
def trivialSpreadNoQbar
    (G : GradedRationalHodgeData)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) :
    SpreadData G X p α hX hα :=
  {
    Base := Unit
    basepoint := ()
    Family := fun _ => X
    fiberAtBasepoint := rfl
    Path := fun _ _ => Unit
    pathRefl := fun _ => ()
    pathComp := fun _ _ => ()
    parallelTransport := fun _ β => β
    parallelTransport_refl := by
      intro b β
      rfl
    parallelTransport_comp := by
      intro b0 b1 b2 γ01 γ12 β
      rfl
    fieldOfDefinition :=
      { isDefinedOverQbar := fun _ => False }
  }

/-- Therefore SpreadData existence alone cannot close R1d. -/
theorem trivial_spread_has_no_qbar_hodge_point
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    ¬ Nonempty
      (QbarHodgePointData
        (trivialSpreadNoQbar G X p α hX hα)) := by
  intro h
  rcases h with ⟨Q⟩
  exact Q.y_is_defined_over_Qbar

/-- R1d and R2 remain mathematically distinct after the interface is typed. -/
def r1DescentPointClosed : Bool := false
def r2FiberCycleClosed : Bool := false

theorem r1_descent_point_still_open :
    r1DescentPointClosed = false := by
  rfl

theorem r2_fiber_cycle_still_open :
    r2FiberCycleClosed = false := by
  rfl

#print axioms MCore.BackwardAudit.assembleAlgebraicPointData
#print axioms MCore.BackwardAudit.trivial_spread_has_no_qbar_hodge_point
#print axioms MCore.BackwardAudit.r1_descent_point_still_open
#print axioms MCore.BackwardAudit.r2_fiber_cycle_still_open

end MCore.BackwardAudit
