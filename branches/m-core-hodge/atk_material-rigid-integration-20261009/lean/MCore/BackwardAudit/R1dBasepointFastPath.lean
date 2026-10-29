import MCore.BackwardAudit.R1dQbarPointBoundary

namespace MCore.BackwardAudit

/-!
# R1d basepoint fast path

For an input whose distinguished fiber/basepoint is already defined over Qbar,
R1d closes without CDK or a density argument: the original class is Hodge by
the endpoint hypothesis, reflexive transport preserves it, and the basepoint
itself is the required Qbar Hodge point.
-/

theorem transportedAlpha_pathRefl_eq
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    S.transportedAlpha (S.pathRefl S.basepoint) = S.alphaAtBasepoint := by
  exact S.parallelTransport_refl S.basepoint S.alphaAtBasepoint

/-- Minimal semantic law missing from the abstract core: Hodge type must
    be invariant under transport across equality of the variety index.  This is
    not an axiom; a concrete Hodge model must provide the proof. -/
structure TypePPCastCompatibility (G : GradedRationalHodgeData) : Prop where
  cast_typePP :
    ∀ {X Y : G.Variety} {p : Nat}
      {β : G.CohomologyQ X (2 * p)}
      (h : X = Y),
      G.isTypePP p β →
      G.isTypePP p (castCohomology G h β)


/-- Equality transport preserves any dependent predicate by reflexivity; this
    closes the cast-semantics bookkeeping for every abstract Hodge datum. -/
def canonicalTypePPCastCompatibility
    (G : GradedRationalHodgeData) :
    TypePPCastCompatibility G :=
  {
    cast_typePP := by
      intro X Y p β h hβ
      cases h
      exact hβ
  }

theorem basepoint_isHodgeAlong
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (K : TypePPCastCompatibility G)
    (S : SpreadData G X p α hX hα) :
    S.isHodgeAlong (S.pathRefl S.basepoint) := by
  unfold TypedVariationalGeometry.isHodgeAlong
  rw [transportedAlpha_pathRefl_eq]
  unfold TypedVariationalGeometry.alphaAtBasepoint
  exact K.cast_typePP S.fiberAtBasepoint.symm hα

theorem r1d_target_of_basepoint_qbar
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (K : TypePPCastCompatibility G)
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    R1dQbarHodgePointTarget S := by
  exact ⟨S.basepoint, S.pathRefl S.basepoint, basepoint_isHodgeAlong K S, hQbar⟩

theorem r1d_contract_of_basepoint_qbar
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (K : TypePPCastCompatibility G)
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    Nonempty (R1DescentPointContract S) :=
  (r1d_contract_iff_target S).2 (r1d_target_of_basepoint_qbar K S hQbar)


/-- Fully internal basepoint fast path: equality-cast compatibility is
    canonical, so the only hypothesis is that the distinguished point itself
    is defined over Qbar. -/
theorem r1d_contract_of_qbar_basepoint
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    Nonempty (R1DescentPointContract S) :=
  r1d_contract_of_basepoint_qbar
    (canonicalTypePPCastCompatibility G) S hQbar

inductive R1dFastPathStatus where
  | proved
  | generalCaseOpen
  deriving Repr, DecidableEq

def r1dBasepointFastPath : R1dFastPathStatus := .proved

def r1dGeneralDescentStatus : R1dFastPathStatus := .generalCaseOpen

theorem r1d_basepoint_fast_path_proved :
    r1dBasepointFastPath = .proved := rfl

theorem r1d_general_descent_still_open :
    r1dGeneralDescentStatus = .generalCaseOpen := rfl

#print axioms MCore.BackwardAudit.transportedAlpha_pathRefl_eq
#print axioms MCore.BackwardAudit.TypePPCastCompatibility
#print axioms MCore.BackwardAudit.canonicalTypePPCastCompatibility
#print axioms MCore.BackwardAudit.basepoint_isHodgeAlong
#print axioms MCore.BackwardAudit.r1d_target_of_basepoint_qbar
#print axioms MCore.BackwardAudit.r1d_contract_of_basepoint_qbar
#print axioms MCore.BackwardAudit.r1d_contract_of_qbar_basepoint
#print axioms MCore.BackwardAudit.r1d_basepoint_fast_path_proved
#print axioms MCore.BackwardAudit.r1d_general_descent_still_open

end MCore.BackwardAudit
