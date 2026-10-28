import MCore.BackwardAudit.R2AfterR3

namespace MCore.BackwardAuditR2Repro

open MCore
open MCore.BackwardAudit

#check SpreadData
#check QbarHodgePointData
#check R1DescentPointContract
#check R2FiberCycleData
#check R2PointProductionContract
#check PointwiseTypedPipeline
#check r1d_r2_r3_yields_concrete_witness
#check typed_pipeline_closes_pointwise
#check per_input_spread_suffices

example : r2CandidateQuantifierMatch = true :=
  r2_quantifier_match

example : r2PointProductionClosed = false :=
  r2_point_production_still_open

example : r1CanonicalSpreadRequired = false :=
  r1_canonical_spread_not_required

#print axioms MCore.BackwardAudit.r1d_then_r2_algebraic_point
#print axioms MCore.BackwardAudit.r1d_r2_r3_yields_concrete_witness
#print axioms MCore.BackwardAudit.r1d_r2_r3_yields_span
#print axioms MCore.BackwardAudit.typed_pipeline_closes_pointwise
#print axioms MCore.BackwardAudit.per_input_spread_suffices
#print axioms MCore.BackwardAudit.r2_quantifier_match
#print axioms MCore.BackwardAudit.r2_point_production_still_open
#print axioms MCore.BackwardAudit.r1_canonical_spread_not_required

end MCore.BackwardAuditR2Repro
