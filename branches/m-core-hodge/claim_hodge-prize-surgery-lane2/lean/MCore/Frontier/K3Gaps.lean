import MCore.K3
namespace MCore
def k3Frontier : EmptyStageSlot := { id := "K3_FRONTIER", content := none }
theorem k3Frontier_is_empty : k3Frontier.content = none := rfl
end MCore
