import MCore.HodgeExactRemaining

namespace MCore.HodgeExactRemainingAudit

open MCore

example
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : HodgeRealizationAdapters D G M)
    (H : HodgeConstructiveMaterial G M) :
    HodgeTerminalCertifies D :=
  H.toTerminal A

example
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConstructiveMaterial G M) :
    ConcreteAlgebraicityPayload M :=
  H.toConcretePayload

#print axioms MCore.HodgeConstructiveMaterial.toGeometricBackend
#print axioms MCore.HodgeConstructiveMaterial.toConcretePayload
#print axioms MCore.HodgeConstructiveMaterial.toGradedHodge
#print axioms MCore.HodgeConstructiveMaterial.toTerminal
#print axioms MCore.higher_exact_material_closes
#print axioms MCore.exact_r1d_cut
#print axioms MCore.exact_r2_cut
#print axioms MCore.exact_r3_cut

end MCore.HodgeExactRemainingAudit
