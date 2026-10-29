import MCore.K6
namespace MCore
structure HodgeWorkspace where
  officialStatement : Option String := none
  scope : Option String := none
  varieties : Option String := none
  cohomology : Option String := none
  hodgeClasses : Option String := none
  algebraicCycles : Option String := none
  cycleClassMap : Option String := none
  rationality : Option String := none
  codimension : Option String := none
  hypotheses : Option String := none
  definitions : Option String := none
  lemmas : Option String := none
  bridges : Option String := none
  openMath : Option String := none
def hodgeWorkspace : HodgeWorkspace := {}
end MCore
