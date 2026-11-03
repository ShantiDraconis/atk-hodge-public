import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR1dFieldBridgeAudit

open MCore
open MCore.BackwardAudit

/-- A component candidate inside the already-frozen Hodge-locus predicate.
    Field-of-definition and finite-type facts remain explicit hypotheses. -/
structure HodgeLocusComponentData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  carrier : S.Base → Prop
  containedInHodgeLocus :
    ∀ y, carrier y → S.hodgeLocusForAlpha y
  nonempty : ∃ y, carrier y

/-- Arithmetic/geometric properties required before the standard
    Qbar-point existence argument can be invoked.  These are theorem
    hypotheses, not declarations or hidden axioms. -/
structure QbarComponentModel
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (C : HodgeLocusComponentData S) where
  isFiniteType : Prop
  isDefinedOverQbar : Prop

/-- Exact external theorem interface needed after a genuine finite-type
    Qbar model has been matched.  It is passed as an explicit argument. -/
def QbarPointExistencePrinciple
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∀ (C : HodgeLocusComponentData S)
    (Mdl : QbarComponentModel C),
    Mdl.isFiniteType →
    Mdl.isDefinedOverQbar →
    ∃ y, C.carrier y ∧
      S.fieldOfDefinition.isDefinedOverQbar y

/-- Minimal R1d target, written locally so this audit file depends only on
    frozen MCore modules. -/
def HasQbarPointOnRelevantHodgeLocus
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

/-- Component defined over Qbar + finite type + the explicit classical
    Qbar-point principle gives exactly the point required by R1d. -/
theorem component_model_gives_qbar_hodge_point
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (C : HodgeLocusComponentData S)
    (Mdl : QbarComponentModel C)
    (hFinite : Mdl.isFiniteType)
    (hDefined : Mdl.isDefinedOverQbar)
    (hPoint : QbarPointExistencePrinciple S) :
    HasQbarPointOnRelevantHodgeLocus S := by
  rcases hPoint C Mdl hFinite hDefined with ⟨y, hyC, hyQbar⟩
  exact ⟨y, C.containedInHodgeLocus y hyC, hyQbar⟩

/-- The field-of-definition bridge reaches the frozen R1d contract without
    introducing any cycle witness. -/
theorem field_of_definition_bridge_closes_r1d
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (C : HodgeLocusComponentData S)
    (Mdl : QbarComponentModel C)
    (hFinite : Mdl.isFiniteType)
    (hDefined : Mdl.isDefinedOverQbar)
    (hPoint : QbarPointExistencePrinciple S) :
    Nonempty (R1DescentPointContract S) := by
  rcases component_model_gives_qbar_hodge_point
      S C Mdl hFinite hDefined hPoint with
    ⟨y, ⟨γ, hHodge⟩, hQbar⟩
  exact ⟨{
    point := {
      y := y
      path := γ
      y_is_hodge := hHodge
      y_is_defined_over_Qbar := hQbar
    }
  }⟩

/-- Current status: the bridge is typed, but the frozen corpus does not yet
    supply the finite-type Qbar component model. -/
def fieldOfDefinitionSemanticMatchComplete : Bool := false

theorem field_of_definition_semantic_match_still_open :
    fieldOfDefinitionSemanticMatchComplete = false := by
  rfl

#print axioms HodgeR1dFieldBridgeAudit.component_model_gives_qbar_hodge_point
#print axioms HodgeR1dFieldBridgeAudit.field_of_definition_bridge_closes_r1d
#print axioms HodgeR1dFieldBridgeAudit.field_of_definition_semantic_match_still_open

end HodgeR1dFieldBridgeAudit
