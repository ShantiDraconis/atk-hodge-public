import MCore.Hodge
namespace MCore
structure HodgeBoundaryWorkspace where
  degeneration : Option String := none
  specialization : Option String := none
  limitClasses : Option String := none
  singularFibres : Option String := none
  rationalIntegralMismatch : Option String := none
  extensionProblem : Option String := none
  adversarialTests : Option String := none
def hodgeBoundaryWorkspace : HodgeBoundaryWorkspace := {}
end MCore
