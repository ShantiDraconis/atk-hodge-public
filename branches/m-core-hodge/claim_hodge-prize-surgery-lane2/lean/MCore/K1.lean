import MCore.K0
namespace MCore
structure EmptyStageSlot where
  id : String
  content : Option String := none
def k1Topic : EmptyStageSlot := { id := "K1", content := none }
theorem k1Topic_is_empty : k1Topic.content = none := rfl
end MCore
