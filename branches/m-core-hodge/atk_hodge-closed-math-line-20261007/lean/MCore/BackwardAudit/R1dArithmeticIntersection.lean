import MCore.BackwardAudit.R1dBasepointFastPath

namespace MCore.BackwardAudit

/-!
# R1d arithmetic-intersection cut

R1d is exactly the assertion that the pathwise Hodge locus for the given class
intersects the repository's Qbar-defined locus.  Mere nonemptiness of the Hodge
locus is strictly weaker, as witnessed by the existing trivialSpreadNoQbar.
-/

def QbarIntersectsHodgeLocus
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ y : S.Base,
    S.hodgeLocusForAlpha y ∧
    S.fieldOfDefinition.isDefinedOverQbar y

theorem r1d_target_iff_qbar_intersection
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    R1dQbarHodgePointTarget S ↔
      QbarIntersectsHodgeLocus S := by
  constructor
  · rintro ⟨y, γ, hHodge, hQbar⟩
    exact ⟨y, ⟨γ, hHodge⟩, hQbar⟩
  · rintro ⟨y, ⟨γ, hHodge⟩, hQbar⟩
    exact ⟨y, γ, hHodge, hQbar⟩

theorem r1d_contract_iff_qbar_intersection
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (R1DescentPointContract S) ↔
      QbarIntersectsHodgeLocus S :=
  (r1d_contract_iff_target S).trans
    (r1d_target_iff_qbar_intersection S)

/-- With the minimal cast-semantics law, the Hodge locus is automatically
    nonempty because it contains the distinguished basepoint.  This still says
    nothing about a Qbar point. -/
theorem hodgeLocus_nonempty_of_castCompatibility
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (K : TypePPCastCompatibility G)
    (S : SpreadData G X p α hX hα) :
    ∃ y : S.Base, S.hodgeLocusForAlpha y := by
  exact ⟨S.basepoint, S.pathRefl S.basepoint, basepoint_isHodgeAlong K S⟩


/-- Therefore every typed spread has a nonempty pathwise Hodge locus: the
    distinguished basepoint belongs to it.  The genuinely open R1d content is
    arithmetic intersection with the Qbar-defined locus, not Hodge-locus
    nonemptiness. -/
theorem hodgeLocus_nonempty
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    ∃ y : S.Base, S.hodgeLocusForAlpha y :=
  hodgeLocus_nonempty_of_castCompatibility
    (canonicalTypePPCastCompatibility G) S

/-- Concrete fail-closed countermodel: the pathwise Hodge locus can be
    nonempty while no Qbar Hodge point exists. -/
theorem trivialSpreadNoQbar_hodgeLocus_nonempty
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    ∃ y : (trivialSpreadNoQbar G X p α hX hα).Base,
      (trivialSpreadNoQbar G X p α hX hα).hodgeLocusForAlpha y := by
  refine ⟨(), (), ?_⟩
  exact hα

theorem trivialSpreadNoQbar_no_qbar_intersection
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    ¬ QbarIntersectsHodgeLocus
      (trivialSpreadNoQbar G X p α hX hα) := by
  rintro ⟨y, hHodge, hQbar⟩
  exact hQbar

inductive R1dArithmeticStatus where
  | exactIntersectionCut
  | nonemptinessInsufficient
  | arithmeticIntersectionOpen
  deriving Repr, DecidableEq

structure R1dArithmeticFrontier where
  reduction : R1dArithmeticStatus
  nonemptyHodgeLocus : R1dArithmeticStatus
  qbarIntersection : R1dArithmeticStatus

def r1dArithmeticFrontier : R1dArithmeticFrontier :=
  {
    reduction := .exactIntersectionCut
    nonemptyHodgeLocus := .nonemptinessInsufficient
    qbarIntersection := .arithmeticIntersectionOpen
  }

theorem r1d_arithmetic_cut_exact :
    r1dArithmeticFrontier.reduction = .exactIntersectionCut := rfl

theorem r1d_qbar_intersection_still_open :
    r1dArithmeticFrontier.qbarIntersection = .arithmeticIntersectionOpen := rfl

#print axioms MCore.BackwardAudit.r1d_target_iff_qbar_intersection
#print axioms MCore.BackwardAudit.r1d_contract_iff_qbar_intersection
#print axioms MCore.BackwardAudit.hodgeLocus_nonempty_of_castCompatibility
#print axioms MCore.BackwardAudit.hodgeLocus_nonempty
#print axioms MCore.BackwardAudit.trivialSpreadNoQbar_hodgeLocus_nonempty
#print axioms MCore.BackwardAudit.trivialSpreadNoQbar_no_qbar_intersection
#print axioms MCore.BackwardAudit.r1d_arithmetic_cut_exact
#print axioms MCore.BackwardAudit.r1d_qbar_intersection_still_open

end MCore.BackwardAudit
