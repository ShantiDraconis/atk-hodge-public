import MCore.HodgeExactRemaining
import P05.Hodge.HodgeTheoryComplete

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-!
# Recovered Hodge material chain

This module consolidates the historical Hodge branches into one forward-only,
kernel-checkable chain over the current types.

Recovered historical decomposition:
p = 0  -> CodimZeroComponentBackend
p = 1  -> Lefschetz11DivisorBackend
p >= 2 -> HigherSpreadProducer
          -> HigherQbarPointProducer
          -> HigherFiberCycleProducer
          -> HigherTransportProducer

No endpoint-equivalent proposition is accepted as an input.
-/

structure RecoveredMaterialChain
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  codimZero : CodimZeroComponentBackend G M
  codimOne : Lefschetz11DivisorBackend G M
  spread : HigherSpreadProducer G
  qbar : HigherQbarPointProducer spread
  fiber : HigherFiberCycleProducer M spread qbar
  transport : HigherTransportProducer M spread

def RecoveredMaterialChain.toConstructiveMaterial
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : RecoveredMaterialChain G M) :
    HodgeConstructiveMaterial G M :=
  {
    p0 := R.codimZero
    p1 := R.codimOne
    higherSpread := R.spread
    higherQbar := R.qbar
    higherR2 := R.fiber
    higherR3 := R.transport
  }

def RecoveredMaterialChain.toTheoryMincut
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : RecoveredMaterialChain G M) :
    HodgeMaterialMincut G M :=
  {
    codimZero := R.codimZero
    codimOne := R.codimOne
    higherSpread := R.spread
    higherQbar := R.qbar
    higherFiber := R.fiber
    higherTransport := R.transport
  }

theorem RecoveredMaterialChain.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (R : RecoveredMaterialChain G M) :
    ConcreteAlgebraicityPayload M :=
  R.toConstructiveMaterial.toConcretePayload

theorem RecoveredMaterialChain.toGradedHodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (R : RecoveredMaterialChain G M) :
    GradedRationalHodgeConjecture G :=
  R.toConstructiveMaterial.toGradedHodge A

/-- Historical R1d residue recovered exactly. -/
theorem recovered_r1d_exact
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    (S : SpreadData G X p alpha hX hAlpha) :
    Nonempty (R1DescentPointContract S) ↔
      QbarIntersectsHodgeLocus S :=
  r1d_contract_iff_qbar_intersection S

/-- Historical R2 residue recovered exactly. -/
theorem recovered_r2_exact
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    {S : SpreadData G X p alpha hX hAlpha}
    (D : R1DescentPointContract S) :
    Nonempty (R2PointProductionContract M S D) ↔
      R2FiberAlgebraicityTarget M D :=
  r2_contract_iff_fiber_algebraicity D

/-- Historical R3 residue recovered exactly. -/
theorem recovered_r3_exact
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    {S : SpreadData G X p alpha hX hAlpha} :
    Nonempty (R3TransportContract M S) ↔
      R3VariationalAlgebraicityPayload M S :=
  r3_contract_iff_variational_algebraicity

/-- Exact recovered frontier: after the spread is fixed, the three historical
mathematical residues are precisely R1d, R2 and R3. -/
structure RecoveredHigherResidues
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hAlpha : G.isTypePP p alpha}
    (S : SpreadData G X p alpha hX hAlpha) where
  qbarIntersection : QbarIntersectsHodgeLocus S
  fiberAlgebraicity :
    ∀ D : R1DescentPointContract S, R2FiberAlgebraicityTarget M D
  variationalTransport : R3VariationalAlgebraicityPayload M S

#print axioms P05.Hodge.RecoveredMaterialChain.toConcretePayload
#print axioms P05.Hodge.RecoveredMaterialChain.toGradedHodge
#print axioms P05.Hodge.recovered_r1d_exact
#print axioms P05.Hodge.recovered_r2_exact
#print axioms P05.Hodge.recovered_r3_exact

end P05.Hodge
