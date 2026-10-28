import MCore.Hodge
import MCore.Boundary

namespace MCore

/-- Hodge-specific stages. This prevents the generic M-Core boundary language
    from being mistaken for geometric content. -/
inductive HodgeStage where
  | semanticInterface
  | cycleClassDirection
  | algebraicityBridge
  | rationalHodgeConjecture
  deriving DecidableEq, Repr

structure HodgeFrontier where
  stage : HodgeStage
  status : SignatureStatus
  note : String

def hodge_semantic_frontier : HodgeFrontier :=
  { stage := .semanticInterface,
    status := .definitionInterface,
    note := "Typed interface only; concrete algebraic geometry remains to be instantiated." }

def hodge_cycle_direction_frontier : HodgeFrontier :=
  { stage := .cycleClassDirection,
    status := .definitionInterface,
    note := "Interface for the standard algebraic-cycle to Hodge-class direction." }

def hodge_open_frontier : HodgeFrontier :=
  { stage := .algebraicityBridge,
    status := .openBridge,
    note := "Global rational Hodge class to rational span of algebraic cycles; unresolved in general." }

theorem hodge_open_frontier_status : hodge_open_frontier.status = .openBridge := rfl

/-- There is intentionally no constructor here that converts `openBridge`
    into `provedProperty`. Any future promotion must arrive with a concrete
    proof in the geometry layer. -/
structure HodgePromotionEvidence (D : HodgeSemanticData) : Prop where
  proof : RationalHodgeConjecture D

end MCore
