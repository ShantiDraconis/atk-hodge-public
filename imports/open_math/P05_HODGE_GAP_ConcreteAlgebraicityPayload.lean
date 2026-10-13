import MCore.HodgeCanonicalSemanticModel
import MCore.HodgeExactRemaining

namespace MCore.OpenMath

/--
P05-HODGE terminal OPEN_MATH.

This is the exact endpoint-equivalent material cut certified by
`canonicalTerminal_iff_concretePayload`.

No inhabitant is asserted here.
-/
abbrev P05_HODGE_GAP
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ConcreteAlgebraicityPayload M

#check MCore.canonicalTerminal_iff_concretePayload
#check MCore.HodgeConstructiveMaterial.toConcretePayload
#check MCore.exact_r1d_cut
#check MCore.exact_r2_cut
#check MCore.exact_r3_cut

end MCore.OpenMath
