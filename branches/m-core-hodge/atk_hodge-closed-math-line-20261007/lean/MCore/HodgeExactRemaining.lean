import MCore.HodgeGeometricBackends
import MCore.K26
import MCore.BackwardAudit.R1dArithmeticIntersection
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3CombinationMinimal

namespace MCore

/-!
# Hodge terminal cut and constructive material route

The unique exact terminal mathematical cut is ConcreteAlgebraicityPayload.
This file also records one forward-only constructive route whose inhabitants
are sufficient to produce that exact endpoint.  The constructive route is not
claimed equivalent to the endpoint: it chooses explicit Spread/R1d/R2/R3 data.

The four material obligations are:
1. codimension-zero component decomposition;
2. codimension-one divisor decomposition;
3. higher-codimension Qbar/fibre-cycle/transport data;
4. concrete semantic realization adapters.

The higher-codimension item is itself split into R1/R1d/R2/R3 producers.
-/

/-- All non-terminal formalization adapters. -/
structure HodgeRealizationAdapters
    (D : HodgeSemanticData)
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  semantic : GradedSemanticAdapter D G
  span : CycleSpanAdapter G M

/-- A sufficient constructive material package.
It is intentionally stronger than merely assuming ConcreteAlgebraicityPayload:
every field constructs lower-level geometric witnesses. -/
structure HodgeConstructiveMaterial
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  p0 : CodimZeroComponentBackend G M
  p1 : Lefschetz11DivisorBackend G M
  higherSpread : HigherSpreadProducer G
  higherQbar : HigherQbarPointProducer higherSpread
  higherR2 : HigherFiberCycleProducer M higherSpread higherQbar
  higherR3 : HigherTransportProducer M higherSpread

def HodgeConstructiveMaterial.toGeometricBackend
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConstructiveMaterial G M) :
    HodgeGeometricBackend G M :=
  {
    codimZero := H.p0
    codimOne := H.p1
    higher := {
      spreads := H.higherSpread
      qbarPoints := H.higherQbar
      fiberCycles := H.higherR2
      transports := H.higherR3
    }
  }

theorem HodgeConstructiveMaterial.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConstructiveMaterial G M) :
    ConcreteAlgebraicityPayload M :=
  H.toGeometricBackend.toConcretePayload

theorem HodgeConstructiveMaterial.toGradedHodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : HodgeConstructiveMaterial G M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload A).2 H.toConcretePayload

theorem HodgeConstructiveMaterial.toTerminal
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : HodgeRealizationAdapters D G M)
    (H : HodgeConstructiveMaterial G M) :
    HodgeTerminalCertifies D :=
  A.semantic.gradedToOld (H.toGradedHodge A.span)

/-- The exact p>=2 data imply the already-existing H01-style material endpoint
without introducing an H01 inhabitant as a premise. -/
theorem higher_exact_material_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (S : HigherSpreadProducer G)
    (Q : HigherQbarPointProducer S)
    (R2 : HigherFiberCycleProducer M S Q)
    (R3 : HigherTransportProducer M S) :
    HigherCodimConcretePayload M :=
  higherMaterialProducer_closes
    ({
      run := by
        intro X p α hp hX hα
        exact {
          spread := S.spread X p α hp hX hα
          descent := Q.point X p α hp hX hα
          package := {
            r2 := R2.cycle X p α hp hX hα
            r3 := R3.transport X p α hp hX hα
          }
        }
    } : HigherMaterialProducer G M)

/-- R2 has no hidden content beyond algebraicity of the transported class. -/
theorem exact_r2_cut
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : BackwardAudit.SpreadData G X p α hX hα}
    (D : BackwardAudit.R1DescentPointContract S) :
    Nonempty (BackwardAudit.R2PointProductionContract M S D) ↔
      BackwardAudit.R2FiberAlgebraicityTarget M D :=
  BackwardAudit.r2_contract_iff_fiber_algebraicity D

/-- R3 has no hidden content beyond exact variational algebraicity. -/
theorem exact_r3_cut
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : BackwardAudit.SpreadData G X p α hX hα} :
    Nonempty (BackwardAudit.R3TransportContract M S) ↔
      BackwardAudit.R3VariationalAlgebraicityPayload M S :=
  BackwardAudit.r3_contract_iff_variational_algebraicity

/-- R1d has no hidden content beyond intersection of the pathwise Hodge locus
with the Qbar-defined locus. -/
theorem exact_r1d_cut
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : BackwardAudit.SpreadData G X p α hX hα) :
    Nonempty (BackwardAudit.R1DescentPointContract S) ↔
      BackwardAudit.QbarIntersectsHodgeLocus S :=
  BackwardAudit.r1d_contract_iff_qbar_intersection S

#print axioms MCore.HodgeConstructiveMaterial.toGeometricBackend
#print axioms MCore.HodgeConstructiveMaterial.toConcretePayload
#print axioms MCore.HodgeConstructiveMaterial.toGradedHodge
#print axioms MCore.HodgeConstructiveMaterial.toTerminal
#print axioms MCore.higher_exact_material_closes
#print axioms MCore.exact_r1d_cut
#print axioms MCore.exact_r2_cut
#print axioms MCore.exact_r3_cut

end MCore
