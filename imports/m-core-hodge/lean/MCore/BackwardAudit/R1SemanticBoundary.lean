import MCore.BackwardAudit.R1DescentBoundary

namespace MCore.BackwardAudit

/-- Audit-only classification of the gap between the now-typed dependent
    interface and the actual geometric hypotheses required by the classical
    Gauss--Manin/CDK route. -/
inductive SemanticMatchStatus where
  | representedInternally
  | missingSemanticType
  | externalPendingMatch
  deriving Repr, DecidableEq

structure SemanticRequirementRecord where
  name : String
  status : SemanticMatchStatus
  note : String
  deriving Repr

/-- The current corpus does not contain native types for these geometric
    notions.  This is metadata about source coverage, not a mathematical axiom. -/
def r1SemanticRequirements : List SemanticRequirementRecord :=
  [
    ⟨"COMPLEX_ALGEBRAIC_BASE", .missingSemanticType,
      "Base is currently a Type; no complex algebraic variety/scheme structure is represented."⟩,
    ⟨"SMOOTH_PROJECTIVE_MORPHISM", .missingSemanticType,
      "Family is currently a dependent family of varieties; no smooth/projective morphism structure is represented."⟩,
    ⟨"POLARIZABLE_VHS", .missingSemanticType,
      "No polarizable variation-of-Hodge-structure type is present in the current corpus."⟩,
    ⟨"RATIONAL_LOCAL_SYSTEM_MATCH", .missingSemanticType,
      "Path transport is typed, but no theorem identifies it with the classical rational cohomology local system."⟩,
    ⟨"GAUSS_MANIN_HYPOTHESIS_MATCH", .externalPendingMatch,
      "Classical theorem may be used only after the missing geometric types are represented and matched."⟩,
    ⟨"CDK_HYPOTHESIS_MATCH", .externalPendingMatch,
      "CDK may be used only after the algebraic-base and polarizable-VHS hypotheses are represented and matched."⟩
  ]

/-- Pure interface existence is trivial once hX and hAlpha are supplied.
    Therefore it must not be confused with existence of a genuine smooth
    projective spread suitable for Gauss--Manin/CDK. -/
theorem spread_interface_inhabited
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) :
    Nonempty (SpreadData G X p α hX hα) :=
  ⟨trivialSpreadNoQbar G X p α hX hα⟩

/-- R1a at the bare dependent-interface level is closed internally. -/
def r1aTypedFamilyInterfaceClosed : Bool := true

/-- Matching that interface to genuine complex algebraic family/VHS semantics
    is not yet represented in the repository. -/
def r1SemanticAdapterComplete : Bool := false

/-- Consequently Gauss--Manin is not yet EXTERNAL_CLASSICAL_EXACT in this
    formal corpus; it remains external pending hypothesis match. -/
def r1bGaussManinExactMatch : Bool := false

/-- Likewise CDK is not yet EXTERNAL_CLASSICAL_EXACT in this formal corpus. -/
def r1cCDKExactMatch : Bool := false

theorem r1a_typed_family_interface_closed :
    r1aTypedFamilyInterfaceClosed = true := by
  rfl

theorem r1_semantic_adapter_still_open :
    r1SemanticAdapterComplete = false := by
  rfl

theorem r1b_gauss_manin_match_pending :
    r1bGaussManinExactMatch = false := by
  rfl

theorem r1c_cdk_match_pending :
    r1cCDKExactMatch = false := by
  rfl

#print axioms MCore.BackwardAudit.spread_interface_inhabited
#print axioms MCore.BackwardAudit.r1a_typed_family_interface_closed
#print axioms MCore.BackwardAudit.r1_semantic_adapter_still_open
#print axioms MCore.BackwardAudit.r1b_gauss_manin_match_pending
#print axioms MCore.BackwardAudit.r1c_cdk_match_pending

end MCore.BackwardAudit
