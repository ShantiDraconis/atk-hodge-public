import MCore.BackwardAudit.R1DescentBoundary
import MCore.BackwardAudit.R3Contract

namespace MCore.BackwardAudit

/-- R2 proper, after R1d has already selected a Qbar Hodge point for THIS
    spread. R2 now has exactly one job: manufacture the finite rational cycle
    combination representing the transported class at that fixed point. -/
structure R2PointProductionContract
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (D : R1DescentPointContract S) where
  produceCycle : R2FiberCycleData M S D.point

/-- R1d + R2 assemble the combined algebraic-point witness consumed by R3. -/
def r1d_then_r2_algebraic_point
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S)
    (R2 : R2PointProductionContract M S D) :
    AlgebraicPointData M S :=
  assembleAlgebraicPointData D.point R2.produceCycle

/-- R1d + R2 + R3 gives the exact concrete K15 witness at the original class. -/
theorem r1d_r2_r3_yields_concrete_witness
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S)
    (R2 : R2PointProductionContract M S D)
    (R3 : R3TransportContract M S) :
    InConcreteCycleSpan M α :=
  R3.transport (r1d_then_r2_algebraic_point D R2)

/-- Exact K13 semantic target after applying the already-existing K15 adapter. -/
theorem r1d_r2_r3_yields_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : CycleSpanAdapter G M)
    (D : R1DescentPointContract S)
    (R2 : R2PointProductionContract M S D)
    (R3 : R3TransportContract M S) :
    G.inCycleClassSpan p α :=
  (A.span_iff α).2 (r1d_r2_r3_yields_concrete_witness D R2 R3)

/-- Package R2's data witness together with the propositional R3 contract. -/
structure TypedR2R3Package
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (D : R1DescentPointContract S) where
  r2 : R2PointProductionContract M S D
  r3 : R3TransportContract M S

/-- Full pointwise pipeline with R1d explicit.  The spread may depend on the
    exact input; no uniqueness or canonical-choice hypothesis is required. -/
structure PointwiseTypedPipeline
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p)) where
  run :
    ∀ (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      Σ S : SpreadData G X p α hX hα,
        Σ D : R1DescentPointContract S,
          TypedR2R3Package M S D

/-- If the complete typed pipeline is supplied, K13 closes pointwise.
    No oracle and no canonical-spread uniqueness assumption occurs. -/
theorem typed_pipeline_closes_pointwise
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (P : PointwiseTypedPipeline G M X p α) :
    GradedAlgebraicityAt G X p α := by
  intro hX hα
  rcases P.run hX hα with ⟨S, D, W⟩
  exact (A.span_iff α).2
    (r1d_r2_r3_yields_concrete_witness D W.r2 W.r3)

/-- This theorem makes the quantifier result explicit: arbitrary per-input
    spreads suffice for the endpoint if R1d/R2/R3 are discharged. Canonicity
    or uniqueness of the spread is not a logical requirement of K13. -/
theorem per_input_spread_suffices
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (P : PointwiseTypedPipeline G M X p α) :
    GradedAlgebraicityAt G X p α :=
  typed_pipeline_closes_pointwise A P

/-- Quantifier matching is enforced by the dependent types. -/
def r2CandidateQuantifierMatch : Bool := true

/-- R2 mathematical point/cycle production itself remains open. -/
def r2PointProductionClosed : Bool := false

/-- Strong canonicity/uniqueness of SpreadData is not required by K13. -/
def r1CanonicalSpreadRequired : Bool := false

theorem r2_quantifier_match :
    r2CandidateQuantifierMatch = true := by
  rfl

theorem r2_point_production_still_open :
    r2PointProductionClosed = false := by
  rfl

theorem r1_canonical_spread_not_required :
    r1CanonicalSpreadRequired = false := by
  rfl

#print axioms MCore.BackwardAudit.r1d_then_r2_algebraic_point
#print axioms MCore.BackwardAudit.r1d_r2_r3_yields_concrete_witness
#print axioms MCore.BackwardAudit.r1d_r2_r3_yields_span
#print axioms MCore.BackwardAudit.typed_pipeline_closes_pointwise
#print axioms MCore.BackwardAudit.per_input_spread_suffices
#print axioms MCore.BackwardAudit.r2_quantifier_match
#print axioms MCore.BackwardAudit.r2_point_production_still_open
#print axioms MCore.BackwardAudit.r1_canonical_spread_not_required

end MCore.BackwardAudit
