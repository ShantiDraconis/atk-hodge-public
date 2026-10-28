import MCore.BackwardAudit.H01MinimalForwardPayload

namespace MCore.BackwardAudit

/-!
# H01 public-domain reuse compression

This file is a fail-closed classification layer.  It records which parts of the
Hodge attack are standard/public mathematics or public formalization
infrastructure and proves only the bookkeeping reduction.  It does NOT turn
external literature into a Lean theorem and does NOT inhabit the remaining
H01 payload.
-/

inductive PublicReuseState where
  | reusablePublic
  | formalizationAdapter
  | openResearch
  deriving Repr, DecidableEq

inductive H01PublicSubgate where
  | schemeSmoothness
  | projectiveSchemeInfrastructure
  | algebraicCycleCarrier
  | hodgeLocusAlgebraicity
  | absoluteHodgeTransport
  | qbarHodgePointExistence
  | fiberAlgebraicity
  | variationalAlgebraicity
  deriving Repr, DecidableEq

def publicReuseState : H01PublicSubgate → PublicReuseState
  | .schemeSmoothness => .reusablePublic
  | .projectiveSchemeInfrastructure => .reusablePublic
  | .algebraicCycleCarrier => .reusablePublic
  | .hodgeLocusAlgebraicity => .formalizationAdapter
  | .absoluteHodgeTransport => .formalizationAdapter
  | .qbarHodgePointExistence => .openResearch
  | .fiberAlgebraicity => .openResearch
  | .variationalAlgebraicity => .openResearch

/-- Publicly known/formalized infrastructure is not counted as new Hodge
mathematics in the ATK research budget. -/
def countsAsNewResearch (g : H01PublicSubgate) : Bool :=
  match publicReuseState g with
  | .openResearch => true
  | _ => false

def allPublicSubgates : List H01PublicSubgate :=
  [
    .schemeSmoothness,
    .projectiveSchemeInfrastructure,
    .algebraicCycleCarrier,
    .hodgeLocusAlgebraicity,
    .absoluteHodgeTransport,
    .qbarHodgePointExistence,
    .fiberAlgebraicity,
    .variationalAlgebraicity
  ]

def remainingResearchSubgates : List H01PublicSubgate :=
  allPublicSubgates.filter countsAsNewResearch

theorem remainingResearchSubgates_exact :
    remainingResearchSubgates =
      [
        .qbarHodgePointExistence,
        .fiberAlgebraicity,
        .variationalAlgebraicity
      ] := by
  rfl

theorem remainingResearchSubgates_count :
    remainingResearchSubgates.length = 3 := by
  rfl

/-- Even after public reuse, the exact forward producer remains the existing
H01 payload. This theorem intentionally only re-exports the already certified
closure theorem; it does not synthesize the payload. -/
theorem public_reuse_plus_H01_payload_closes_pointwise
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (P : H01MinimalForwardPayload G M X p α) :
    GradedAlgebraicityAt G X p α :=
  h01_minimal_forward_payload_closes_pointwise A P

#print axioms MCore.BackwardAudit.remainingResearchSubgates_exact
#print axioms MCore.BackwardAudit.public_reuse_plus_H01_payload_closes_pointwise

end MCore.BackwardAudit
