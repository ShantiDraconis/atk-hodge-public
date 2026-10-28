import MCore.Material.Closure
import MCore.BackwardAudit.HodgeTerminalCycle
namespace MCore.Material
theorem terminal_inhabitant_is_sufficient {G : MCore.GradedRationalHodgeData} (M : MCore.CycleSpanMechanics G) (n : MCore.BackwardAudit.HodgeTerminalNode) (h : MCore.BackwardAudit.HodgeTerminalSemantics M n) : MCore.ConcreteAlgebraicityPayload M := MCore.BackwardAudit.any_terminal_inhabitant_closes_endpoint M n h
end MCore.Material
