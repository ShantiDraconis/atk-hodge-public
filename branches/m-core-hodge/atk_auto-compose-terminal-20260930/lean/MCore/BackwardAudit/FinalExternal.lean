import MCore.BackwardAudit.HodgeUnifiedTerminalProducer

namespace MCore.BackwardAudit
namespace Final

structure FinalExternalCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) where
  boundary : HodgeCertificationBoundary G M
  producer : HodgePositiveTerminalProducer M

def FINAL_ROOT (G : GradedRationalHodgeData) : Prop :=
  GradedRationalHodgeConjecture G

theorem finalExternal_to_FINAL_ROOT
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (E : FinalExternalCertificate M) :
    FINAL_ROOT G :=
  E.producer.createTheorem E.boundary

end Final
end MCore.BackwardAudit
