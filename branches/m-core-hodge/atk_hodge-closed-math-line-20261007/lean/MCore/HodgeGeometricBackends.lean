import MCore.CodimZeroGeometry
import MCore.HodgeMaterialInhabitant
import MCore.BackwardAudit.R1DescentBoundary
import MCore.BackwardAudit.R2AfterR3
import MCore.BackwardAudit.R3Contract

namespace MCore

/-!
# Constructive geometric backends for p=1 and p>=2

This module exposes the exact data producers needed to inhabit the remaining
Hodge construction without assuming an endpoint proposition.
-/

/-! ## Codimension one: explicit divisor-cycle combinations -/

structure CodimOneDivisorTerm
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety) where
  coefficient : M.Coeff
  divisorCycle : G.CycleQ X 1

structure CodimOneDivisorDecomposition
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (α : G.CohomologyQ X (2 * 1)) where
  divisors : List (CodimOneDivisorTerm M X)
  reconstruct :
    (divisors.map (fun t => (t.coefficient, t.divisorCycle)) :
      List (M.Coeff × G.CycleQ X 1)).foldr
        (fun t acc =>
          M.addClass (M.smul t.1 (M.cycleClass 1 t.2)) acc)
        M.zeroClass = α

/-- Constructive Lefschetz (1,1) backend.

A concrete complex-geometry implementation should derive this from line
bundles/divisors and the first Chern class theorem. -/
structure Lefschetz11DivisorBackend
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  decompose :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 1))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP 1 α),
      CodimOneDivisorDecomposition M X α

def Lefschetz11DivisorBackend.toCycleProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : Lefschetz11DivisorBackend G M) :
    CodimOneCycleProducer G M :=
  {
    combination := by
      intro X α hX hα
      let D := B.decompose X α hX hα
      exact ⟨D.divisors.map (fun t => (t.coefficient, t.divisorCycle))⟩
    realizes := by
      intro X α hX hα
      let D := B.decompose X α hX hα
      change
        (D.divisors.map (fun t => (t.coefficient, t.divisorCycle))).foldr
          (fun t acc =>
            M.addClass (M.smul t.1 (M.cycleClass 1 t.2)) acc)
          M.zeroClass = α
      exact D.reconstruct
  }

def Lefschetz11DivisorBackend.toConcreteLaw
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : Lefschetz11DivisorBackend G M) :
    BackwardAudit.Lefschetz11ConcreteLaw M :=
  B.toCycleProducer.toLefschetz11ConcreteLaw

/-! ## Higher codimension: producer decomposition -/

/-- R1: construct one typed spread for the exact endpoint input. -/
structure HigherSpreadProducer
    (G : GradedRationalHodgeData) where
  spread :
    ∀ (X : G.Variety)
      (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hp : 2 ≤ p)
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      BackwardAudit.SpreadData G X p α hX hα

/-- R1d: construct a Qbar Hodge point in every produced spread. -/
structure HigherQbarPointProducer
    {G : GradedRationalHodgeData}
    (S : HigherSpreadProducer G) where
  point :
    ∀ (X : G.Variety)
      (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hp : 2 ≤ p)
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      BackwardAudit.R1DescentPointContract
        (S.spread X p α hp hX hα)

/-- R2: produce an explicit finite algebraic-cycle combination on the selected
Qbar Hodge fibre. -/
structure HigherFiberCycleProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (S : HigherSpreadProducer G)
    (Q : HigherQbarPointProducer S) where
  cycle :
    ∀ (X : G.Variety)
      (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hp : 2 ≤ p)
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      BackwardAudit.R2PointProductionContract M
        (S.spread X p α hp hX hα)
        (Q.point X p α hp hX hα)

/-- R3: transport algebraicity from the selected fibre back to the original
class. This is the exact specialization/variational-algebraicity producer. -/
structure HigherTransportProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (S : HigherSpreadProducer G) where
  transport :
    ∀ (X : G.Variety)
      (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hp : 2 ≤ p)
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      BackwardAudit.R3TransportContract M
        (S.spread X p α hp hX hα)

/-- Complete higher-codimension geometric backend with all material stages
separated. -/
structure HigherGeometricBackend
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  spreads : HigherSpreadProducer G
  qbarPoints : HigherQbarPointProducer spreads
  fiberCycles : HigherFiberCycleProducer M spreads qbarPoints
  transports : HigherTransportProducer M spreads

/-- Assemble the four independent geometric producers into the already checked
higher material producer. -/
def HigherGeometricBackend.toMaterialProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HigherGeometricBackend G M) :
    HigherMaterialProducer G M :=
  {
    run := by
      intro X p α hp hX hα
      exact {
        spread := B.spreads.spread X p α hp hX hα
        descent := B.qbarPoints.point X p α hp hX hα
        package := {
          r2 := B.fiberCycles.cycle X p α hp hX hα
          r3 := B.transports.transport X p α hp hX hα
        }
      }
  }

/-- Full geometric source package for all codimensions.

This is intentionally lower-level than `HodgeConcreteInhabitant`: each field
describes geometric witness production rather than asserting Hodge. -/
structure HodgeGeometricBackend
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  codimZero : CodimZeroComponentBackend G M
  codimOne : Lefschetz11DivisorBackend G M
  higher : HigherGeometricBackend G M

def HodgeGeometricBackend.toConcreteInhabitant
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeGeometricBackend G M) :
    HodgeConcreteInhabitant G M :=
  {
    codimZero := B.codimZero.toCycleProducer
    codimOne := B.codimOne.toCycleProducer
    higher := B.higher.toMaterialProducer
  }

theorem HodgeGeometricBackend.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeGeometricBackend G M) :
    ConcreteAlgebraicityPayload M :=
  B.toConcreteInhabitant.toConcretePayload

/-- Fully anchored package including the two model/formalization adapters. -/
structure FullyAnchoredHodgeBackend
    (D : HodgeSemanticData)
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  semanticAdapter : GradedSemanticAdapter D G
  spanAdapter : CycleSpanAdapter G M
  geometry : HodgeGeometricBackend G M

def FullyAnchoredHodgeBackend.toAnchoredInhabitant
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : FullyAnchoredHodgeBackend D G M) :
    AnchoredHodgeInhabitant D G M :=
  {
    semanticAdapter := B.semanticAdapter
    spanAdapter := B.spanAdapter
    material := B.geometry.toConcreteInhabitant
  }

theorem FullyAnchoredHodgeBackend.certifies
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : FullyAnchoredHodgeBackend D G M) :
    HodgeTerminalCertifies D :=
  B.toAnchoredInhabitant.certifies

#print axioms MCore.Lefschetz11DivisorBackend.toCycleProducer
#print axioms MCore.Lefschetz11DivisorBackend.toConcreteLaw
#print axioms MCore.HigherGeometricBackend.toMaterialProducer
#print axioms MCore.HodgeGeometricBackend.toConcreteInhabitant
#print axioms MCore.HodgeGeometricBackend.toConcretePayload
#print axioms MCore.FullyAnchoredHodgeBackend.toAnchoredInhabitant
#print axioms MCore.FullyAnchoredHodgeBackend.certifies

end MCore
