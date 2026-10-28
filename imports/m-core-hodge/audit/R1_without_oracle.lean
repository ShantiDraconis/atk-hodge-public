import MCore.BackwardAudit.R1SemanticBoundary

namespace MCore.BackwardAuditR1

open MCore
open MCore.BackwardAudit

/-- The variational/local-system interface is now represented by an actual
    dependent type. No mathematical existence theorem is claimed. -/
def r1TypeInterfaceResidueCount : Nat := 0
def r1SemanticAdapterResidueCount : Nat := 1
def r1ExternalPendingMatchCount : Nat := 2
def r1ProvedInternalCount : Nat := 2
def r1OpenMathematicsCount : Nat := 1
def r1RouteDependentCount : Nat := 1
def r1MathematicalClosure : Bool := false

theorem r1_interface_is_typed :
    typeInterfaceConstructed = true :=
  type_interface_constructed

theorem r1_quantifiers_are_typed :
    typedR2QuantifierMatch = true ∧ typedR3QuantifierMatch = true := by
  exact ⟨typed_r2_quantifier_match, typed_r3_quantifier_match⟩

theorem r1_counts_are_explicit :
    r1TypeInterfaceResidueCount = 0 ∧
    r1SemanticAdapterResidueCount = 1 ∧
    r1ExternalPendingMatchCount = 2 ∧
    r1ProvedInternalCount = 2 ∧
    r1OpenMathematicsCount = 1 ∧
    r1RouteDependentCount = 1 := by
  decide

theorem r1a_interface_closed :
    r1aTypedFamilyInterfaceClosed = true :=
  r1a_typed_family_interface_closed

theorem r1_semantic_match_still_open :
    r1SemanticAdapterComplete = false :=
  r1_semantic_adapter_still_open

theorem r1_not_closed : r1MathematicalClosure = false := by
  rfl

#print axioms MCore.BackwardAuditR1.r1_interface_is_typed
#print axioms MCore.BackwardAuditR1.r1_quantifiers_are_typed
#print axioms MCore.BackwardAuditR1.r1a_interface_closed
#print axioms MCore.BackwardAuditR1.r1_semantic_match_still_open
#print axioms MCore.BackwardAuditR1.r1_counts_are_explicit
#print axioms MCore.BackwardAuditR1.r1_not_closed
#print axioms MCore.BackwardAudit.TypedVariationalGeometry.hodgeLocusForAlpha

end MCore.BackwardAuditR1
