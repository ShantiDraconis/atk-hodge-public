import MCore.K3
namespace MCore
def k3AttackSlot : EmptyStageSlot := { id := "K3_ATTACK", content := none }
theorem k3AttackSlot_is_empty : k3AttackSlot.content = none := rfl
end MCore
