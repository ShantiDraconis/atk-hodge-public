import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR3TransportReturnAudit

open MCore
open MCore.BackwardAudit

/-- A minimal reverse-path extension of the frozen path interface.
    It does not assume global path independence or monodromy triviality:
    only that the chosen path Q.path has a chosen right inverse. -/
structure ReversePathData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  reversePath : S.Path Q.y S.basepoint
  rightInverse :
    S.pathComp Q.path reversePath =
      S.pathRefl S.basepoint

/-- Equality transport along h followed by transport along h.symm is the
    identity.  This is pure dependent-type bookkeeping. -/
theorem castCohomology_roundtrip
    {G : GradedRationalHodgeData}
    {X Y : G.Variety}
    {n : Nat}
    (h : X = Y)
    (β : G.CohomologyQ Y n) :
    castCohomology G h
      (castCohomology G h.symm β) = β := by
  cases h
  rfl

/-- Groupoid completion of the frozen path carrier.  Only inverse-path
    structure and the right-cancellation law are needed for the selected
    transport-return argument. -/
structure PathGroupoidExtension
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  inversePath :
    {a b : S.Base} → S.Path a b → S.Path b a
  comp_inverse_right :
    ∀ {a b : S.Base} (γ : S.Path a b),
      S.pathComp γ (inversePath γ) = S.pathRefl a

/-- A genuine path-groupoid implementation supplies the chosen reverse path
    needed for the selected Qbar point. -/
def reversePathDataOfGroupoid
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (P : PathGroupoidExtension S) :
    ReversePathData S Q :=
  {
    reversePath := P.inversePath Q.path
    rightInverse := P.comp_inverse_right Q.path
  }

/-- Return cohomology from the selected fiber by parallel-transporting along
    the chosen inverse path, then identifying the base fiber with X. -/
def returnCohomologyOfReversePath
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : ReversePathData S Q) :
    G.CohomologyQ (S.Family Q.y) (2 * p) →
    G.CohomologyQ X (2 * p) :=
  fun β =>
    castCohomology G S.fiberAtBasepoint
      (S.parallelTransport D.reversePath β)

/-- Transporting alpha out along Q.path and back along its chosen inverse
    recovers the original input alpha.  No path-independence or final
    algebraicity target is assumed. -/
theorem reverse_path_returns_transported_alpha
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : ReversePathData S Q) :
    returnCohomologyOfReversePath D
      (S.transportedAlpha Q.path) = α := by
  unfold returnCohomologyOfReversePath
  unfold TypedVariationalGeometry.transportedAlpha
  rw [← S.parallelTransport_comp
    Q.path D.reversePath S.alphaAtBasepoint]
  rw [D.rightInverse]
  rw [S.parallelTransport_refl]
  exact castCohomology_roundtrip
    S.fiberAtBasepoint α

/-- Exact remaining formal obligation for the frozen path carrier: provide a
    reverse path with the cancellation law for the selected Q.path. -/
def HasChosenReversePath
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) : Prop :=
  Nonempty (ReversePathData S Q)

/-- The frozen TypedVariationalGeometry does not include reversePath, so this
    witness must come from the genuine path/local-system semantic adapter. -/
inductive TransportReturnRequirementStatus where
  | provedInternal
  | semanticAdapterResidue
  deriving Repr, DecidableEq

structure TransportReturnRequirement where
  name : String
  status : TransportReturnRequirementStatus
  note : String
  deriving Repr

def transportReturnRequirements : List TransportReturnRequirement :=
  [
    ⟨"RETURN_MAP_FROM_REVERSE_PATH", .provedInternal,
      "returnCohomologyOfReversePath is constructed from frozen parallelTransport."⟩,
    ⟨"RETURN_TRANSPORTED_ALPHA_EQUALS_ALPHA", .provedInternal,
      "reverse_path_returns_transported_alpha follows from path composition, cancellation, and reflexive transport."⟩,
    ⟨"CHOSEN_REVERSE_PATH_WITH_CANCELLATION", .semanticAdapterResidue,
      "Frozen Path has refl/comp but no reverse operation; a PathGroupoidExtension from genuine path semantics supplies it."⟩
  ]

#print axioms HodgeR3TransportReturnAudit.castCohomology_roundtrip
#print axioms HodgeR3TransportReturnAudit.reversePathDataOfGroupoid
#print axioms HodgeR3TransportReturnAudit.returnCohomologyOfReversePath
#print axioms HodgeR3TransportReturnAudit.reverse_path_returns_transported_alpha

end HodgeR3TransportReturnAudit
