import MCore.HodgeReduction
import MCore.HodgeBoundary

namespace MCore.Audit8x5

inductive AxisState where
  | matched
  | blocking
  | refuted
  | external
  | pending
  deriving DecidableEq, Repr

structure Sigma5 where
  HC : AxisState
  Q : AxisState
  S : AxisState
  K : AxisState
  A : AxisState
  deriving Repr

/-- L3 literal endpoint relative to the same semantic datum D. -/
def Endpoint (D : HodgeSemanticData) : Prop :=
  RationalHodgeConjecture D

/-- L4 compression reuses the exact pointwise reduction already proved. -/
theorem endpoint_iff_pointwise (D : HodgeSemanticData) :
    Endpoint D ↔ PointwiseHodgeAlgebraicity D :=
  rationalHodge_iff_pointwise D

/--
Q is exact: no quantifier is introduced, removed, or reordered by the
global-to-pointwise reduction; the propositions are definitionally equal.
-/
def QuantifierMatch : Prop :=
  ∀ D : HodgeSemanticData,
    Endpoint D ↔ PointwiseHodgeAlgebraicity D

theorem quantifier_match : QuantifierMatch := by
  intro D
  exact endpoint_iff_pointwise D

/--
HC remains blocking in the current source catalog: the payload itself is
explicitly classified openBridge. This is an epistemic source status, not a
proof of the negation of Hodge.
-/
theorem pointwise_payload_remains_open :
    pointwise_algebraicity_payload_status = .openBridge :=
  pointwise_payload_open

def sigmaReviewed : Sigma5 :=
  {
    HC := .blocking
    Q := .matched
    S := .pending
    K := .pending
    A := .pending
  }

theorem HC_axis_blocking : sigmaReviewed.HC = .blocking := rfl
theorem Q_axis_matched : sigmaReviewed.Q = .matched := rfl
theorem S_axis_pending : sigmaReviewed.S = .pending := rfl
theorem K_axis_pending : sigmaReviewed.K = .pending := rfl
theorem A_axis_pending : sigmaReviewed.A = .pending := rfl

#print axioms endpoint_iff_pointwise
#print axioms quantifier_match
#print axioms pointwise_payload_remains_open

end MCore.Audit8x5
