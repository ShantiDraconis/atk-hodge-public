import MCore.HodgeReduction

namespace MCore.OpenMath.Hodge

def FirstRealOpenMath (D : MCore.HodgeSemanticData) : Prop :=
  MCore.PointwiseHodgeAlgebraicity D

theorem close_hodge_from_first_real_open_math
    {D : MCore.HodgeSemanticData}
    (h : FirstRealOpenMath D) :
    MCore.RationalHodgeConjecture D :=
  MCore.pointwise_closes_hodge h

#print axioms MCore.OpenMath.Hodge.close_hodge_from_first_real_open_math

end MCore.OpenMath.Hodge
