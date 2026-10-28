import MCore.BackwardAudit.HodgeTerminalCycle
import MCore.CodimZeroGeometry

namespace MCore.BackwardAudit

/--
Decisive fail-closed test for the terminal-wheel interpretation.

The already-certified abstract countermodel admits the complete terminal cycle
of equivalences while its concrete algebraicity endpoint is false. Therefore
the existence of the terminal wheel, by itself, cannot inhabit the endpoint.
-/
theorem countermodel_endpoint_false :
    ¬ HodgeTerminalSemantics codimZeroCounterexampleM .endpoint := by
  intro h
  have h0 : CodimZeroConcretePayload codimZeroCounterexampleM := by
    intro X α hX hα
    exact h X 0 α hX hα
  exact abstract_core_does_not_force_codimZeroPayload h0

theorem countermodel_terminal_cycle_exists :
    (HodgeTerminalSemantics codimZeroCounterexampleM .endpoint ↔
      HodgeTerminalSemantics codimZeroCounterexampleM .gap) ∧
    (HodgeTerminalSemantics codimZeroCounterexampleM .gap ↔
      HodgeTerminalSemantics codimZeroCounterexampleM .habitant) ∧
    (HodgeTerminalSemantics codimZeroCounterexampleM .habitant ↔
      HodgeTerminalSemantics codimZeroCounterexampleM .inhabitant) ∧
    (HodgeTerminalSemantics codimZeroCounterexampleM .inhabitant ↔
      HodgeTerminalSemantics codimZeroCounterexampleM .endpoint) :=
  hodge_terminal_cycle codimZeroCounterexampleM

theorem terminal_cycle_does_not_imply_endpoint :
    ¬ (
      ((HodgeTerminalSemantics codimZeroCounterexampleM .endpoint ↔
        HodgeTerminalSemantics codimZeroCounterexampleM .gap) ∧
       (HodgeTerminalSemantics codimZeroCounterexampleM .gap ↔
        HodgeTerminalSemantics codimZeroCounterexampleM .habitant) ∧
       (HodgeTerminalSemantics codimZeroCounterexampleM .habitant ↔
        HodgeTerminalSemantics codimZeroCounterexampleM .inhabitant) ∧
       (HodgeTerminalSemantics codimZeroCounterexampleM .inhabitant ↔
        HodgeTerminalSemantics codimZeroCounterexampleM .endpoint))
      →
      HodgeTerminalSemantics codimZeroCounterexampleM .endpoint
    ) := by
  intro h
  exact countermodel_endpoint_false (h countermodel_terminal_cycle_exists)

#print axioms MCore.BackwardAudit.countermodel_endpoint_false
#print axioms MCore.BackwardAudit.countermodel_terminal_cycle_exists
#print axioms MCore.BackwardAudit.terminal_cycle_does_not_imply_endpoint

end MCore.BackwardAudit
