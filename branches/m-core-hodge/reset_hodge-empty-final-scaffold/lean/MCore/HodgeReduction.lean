import MCore.Hodge
namespace MCore
structure HodgeReductionWorkspace where
  localReduction : Option String := none
  pointwiseReduction : Option String := none
  globalReduction : Option String := none
  algebraicityTarget : Option String := none
  surjectivityTarget : Option String := none
  reductionProof : Option String := none
def hodgeReductionWorkspace : HodgeReductionWorkspace := {}
end MCore
