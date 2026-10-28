import MCore
namespace MCore.Material
structure HodgeClosure (HodgeClass AlgebraicCycle : Type) where
  realize : HodgeClass → AlgebraicCycle
  algebraicityLaw : Prop
  gluingLaw : Prop
  algebraicity_proof : algebraicityLaw
  gluing_proof : gluingLaw

def ConcreteAlgebraicityPayload (HodgeClass AlgebraicCycle : Type) : Prop :=
  Nonempty (HodgeClosure HodgeClass AlgebraicCycle)
end MCore.Material
