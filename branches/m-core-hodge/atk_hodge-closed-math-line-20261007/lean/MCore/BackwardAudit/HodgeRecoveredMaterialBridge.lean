import MCore.BackwardAudit.HodgeProducerFirst
import MCore.BackwardAudit.HodgeHabitantConstructors
import MCore.HodgeCanonicalSemanticModel
import MCore.HodgeMaterialInhabitant

namespace MCore.BackwardAudit

open MCore

/-!
Recovered forward chain from historical Hodge work.

This file does not add a terminal hypothesis. It connects the recovered
Type-valued realization producer to the current concrete endpoint and canonical
terminal theorem.
-/

/-- Historical universal H01 data yields the concrete endpoint through an
actual HodgeHabitant realization term. -/
theorem recovered_universalForward_closes_concrete
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : ∀ (X : G.Variety) (p : Nat)
      (alpha : G.CohomologyQ X (2 * p)),
      H01MinimalForwardPayload G M X p alpha) :
    ConcreteAlgebraicityPayload M := by
  exact concretePayload_of_habitant (hodgeHabitantOfUniversalForward P)

/-- The same recovered chain closes the canonical semantic terminal. -/
theorem recovered_universalForward_closes_terminal
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : ∀ (X : G.Variety) (p : Nat)
      (alpha : G.CohomologyQ X (2 * p)),
      H01MinimalForwardPayload G M X p alpha) :
    HodgeTerminalCertifies (canonicalHodgeSemanticData G M) := by
  exact (canonicalTerminal_iff_concretePayload G M).2
    (recovered_universalForward_closes_concrete P)

/-- Explicit inventory of the genuine recovered partial constructors. -/
theorem recovered_zero_constructor
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat) :
    ∃ Z : CycleCombination G M X p,
      Z.eval M = (M.zeroClass : G.CohomologyQ X (2 * p)) :=
  realize_zeroClass M X p

#print axioms MCore.BackwardAudit.realize_zeroClass
#print axioms MCore.BackwardAudit.realize_smul_cycleClass
#print axioms MCore.BackwardAudit.hodgeExactLocalProducer
#print axioms MCore.BackwardAudit.hodgeHabitantOfUniversalForward
#print axioms MCore.BackwardAudit.recovered_universalForward_closes_concrete
#print axioms MCore.BackwardAudit.recovered_universalForward_closes_terminal

end MCore.BackwardAudit
