import MCore.BackwardAudit.HodgeFastR2Mincut
import MCore.CodimZeroGeometry

namespace MCore.BackwardAudit

/--
A candidate R2 principle over the fail-closed abstract countermodel.
This is a search filter: genuine candidates must contain enough geometry to
fail on the model with no codimension-zero cycles.
-/
def R2StructuralCandidate : Type 1 :=
  CycleSpanMechanics codimZeroCounterexampleG → Prop

def ForcesFastR2 (P : R2StructuralCandidate) : Prop :=
  ∀ M : CycleSpanMechanics codimZeroCounterexampleG,
    P M → HodgeFastR2OpenMath M

/--
Any purported universal R2 principle that already holds in the fail-closed
countermodel cannot force the fast R2 endpoint.
-/
theorem candidate_holding_on_counterexample_cannot_force_fast_r2
    (P : R2StructuralCandidate)
    (hP : P codimZeroCounterexampleM) :
    ¬ ForcesFastR2 P := by
  intro hForce
  have hR2 : HodgeFastR2OpenMath codimZeroCounterexampleM :=
    hForce codimZeroCounterexampleM hP
  have hConcrete : ConcreteAlgebraicityPayload codimZeroCounterexampleM :=
    (hodge_fast_r2_iff_concrete_payload codimZeroCounterexampleM).1 hR2
  have h0 : CodimZeroConcretePayload codimZeroCounterexampleM := by
    intro X α hX hα
    exact hConcrete X 0 α hX hα
  exact abstract_core_does_not_force_codimZeroPayload h0

/--
Corollary: a geometry-free candidate that is true for every mechanics object
is automatically rejected as an R2 closure principle.
-/
theorem universally_true_candidate_cannot_force_fast_r2
    (P : R2StructuralCandidate)
    (hAll : ∀ M, P M) :
    ¬ ForcesFastR2 P :=
  candidate_holding_on_counterexample_cannot_force_fast_r2
    P (hAll codimZeroCounterexampleM)

#print axioms MCore.BackwardAudit.candidate_holding_on_counterexample_cannot_force_fast_r2
#print axioms MCore.BackwardAudit.universally_true_candidate_cannot_force_fast_r2

end MCore.BackwardAudit
