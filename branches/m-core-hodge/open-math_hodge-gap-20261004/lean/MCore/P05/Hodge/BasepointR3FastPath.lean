import MCore.P05.Hodge.R3CombinationMincut

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-- Pure cycle transport across equality of the variety index. -/
def castCycle
    (G : GradedRationalHodgeData)
    {X Y : G.Variety} {p : Nat}
    (h : X = Y) :
    G.CycleQ X p → G.CycleQ Y p := by
  cases h
  exact id

/-- The canonical Qbar-Hodge point at a Qbar basepoint. -/
def basepointQbarPoint
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    QbarHodgePointData S :=
  {
    y := S.basepoint
    path := S.pathRefl S.basepoint
    y_is_hodge :=
      basepoint_isHodgeAlong (canonicalTypePPCastCompatibility G) S
    y_is_defined_over_Qbar := hQbar
  }

/-- Equality transport on cohomology cancels with transport along the inverse equality. -/
theorem castCohomology_cancel
    {G : GradedRationalHodgeData}
    {X Y : G.Variety}
    {n : Nat}
    (h : X = Y)
    (β : G.CohomologyQ X n) :
    castCohomology G h.symm (castCohomology G h β) = β := by
  cases h
  rfl

/-- Equality transport preserves the evaluation of a finite cycle combination. -/
theorem castCombination_eval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X Y : G.Variety}
    {p : Nat}
    (h : X = Y)
    (c : CycleCombination G M X p) :
    (⟨c.terms.map (fun t => (t.1, castCycle G h t.2))⟩ :
      CycleCombination G M Y p).eval M =
      castCohomology G h (c.eval M) := by
  cases h
  rfl

/--
At the distinguished basepoint, R3 is only equality transport:
Family basepoint = X. No specialization theorem is needed.
-/
def basepointR3Action
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    R3CombinationSpecialization M (basepointQbarPoint S hQbar) :=
  {
    specializeCycle := castCycle G S.fiberAtBasepoint
    specializeClass := castCohomology G S.fiberAtBasepoint
    combination_compat := by
      intro c
      exact castCombination_eval S.fiberAtBasepoint c
    recover_transported := by
      rw [transportedAlpha_pathRefl_eq S]
      unfold TypedVariationalGeometry.alphaAtBasepoint
      exact castCohomology_cancel S.fiberAtBasepoint.symm α
  }

/--
Basepoint-Qbar route closes R3 mechanically for every algebraic point whose
selected point/path are exactly the distinguished basepoint/reflexive path.
-/
theorem basepointR3_closes_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint)
    (c : CycleCombination G M (S.Family S.basepoint) p)
    (hc : c.eval M =
      S.transportedAlpha (S.pathRefl S.basepoint)) :
    InConcreteCycleSpan M α := by
  let Q := basepointQbarPoint S hQbar
  let P : AlgebraicPointData M S :=
    {
      y := S.basepoint
      path := S.pathRefl S.basepoint
      y_is_hodge := Q.y_is_hodge
      y_is_defined_over_Qbar := hQbar
      combination := c
      combination_class := hc
    }
  exact R3CombinationSpecialization.closes_span
    P (basepointR3Action M S hQbar)

/--
Basepoint-Qbar route closes R3 mechanically for every algebraic point whose
selected point/path are exactly the distinguished basepoint/reflexive path.
-/
theorem basepointR3_closes_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint)
    (c : CycleCombination G M (S.Family S.basepoint) p)
    (hc : c.eval M =
      S.transportedAlpha (S.pathRefl S.basepoint)) :
    InConcreteCycleSpan M α := by
  let Q := basepointQbarPoint S hQbar
  let P : AlgebraicPointData M S :=
    {
      y := S.basepoint
      path := S.pathRefl S.basepoint
      y_is_hodge := Q.y_is_hodge
      y_is_defined_over_Qbar := hQbar
      combination := c
      combination_class := hc
    }
  exact R3CombinationSpecialization.closes_span
    P (basepointR3Action M S hQbar)

/--
For the basepoint route the material higher-codimension frontier is therefore
R2 only: once a cycle combination hits alpha on the basepoint fiber, R3 is
pure transport.
-/
inductive BasepointRouteGap where
  | correspondenceAction
  | targetHit
  deriving Repr, DecidableEq

def basepointRouteGaps : List BasepointRouteGap :=
  [.correspondenceAction, .targetHit]

theorem basepointRouteGaps_count :
    basepointRouteGaps.length = 2 := by decide

#print axioms P05.Hodge.castCycle
#print axioms P05.Hodge.basepointQbarPoint
#print axioms P05.Hodge.basepointR3Action
#print axioms P05.Hodge.basepointR3_closes_span
#print axioms P05.Hodge.basepointRouteGaps_count

end P05.Hodge
