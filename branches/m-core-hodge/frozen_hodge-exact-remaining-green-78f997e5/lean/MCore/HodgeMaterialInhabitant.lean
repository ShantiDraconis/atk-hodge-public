import MCore.HodgeMaterialFrontier
import MCore.HodgeTerminalLaw
import MCore.BackwardAudit.R2AfterR3

namespace MCore

/-!
# Constructive Hodge material inhabitant

This file defines the exact Type-valued data that must be constructed to close
the current Hodge frontier.  It does not assume the Hodge conjecture, does not
introduce an axiom, and does not hide the endpoint in an equivalent Prop.

The producer is split into:
* codimension 0: an explicit finite cycle combination for every input class;
* codimension 1: an explicit finite divisor/cycle combination for every input;
* codimension >= 2: a typed spread, a Qbar Hodge point, a fibre cycle, and an
  exact R3 transport contract.

All terminal propositions are derived mechanically from those witnesses.
-/

/-- Constructive codimension-zero producer.

Unlike `CodimZeroConcretePayload`, this is Type-valued data: it returns the
actual finite cycle combination and separately proves its evaluation equation. -/
structure CodimZeroCycleProducer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  combination :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 0))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP 0 α),
      CycleCombination G M X 0
  realizes :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 0))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP 0 α),
      (combination X α hX hα).eval M = α

/-- A constructive p=0 producer closes exactly the p=0 material slice. -/
theorem codimZeroCycleProducer_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : CodimZeroCycleProducer G M) :
    CodimZeroConcretePayload M := by
  intro X α hX hα
  exact ⟨P.combination X α hX hα, P.realizes X α hX hα⟩

/-- Constructive codimension-one producer.

For a genuine complex-projective implementation, this is where the imported
Lefschetz (1,1) theorem must ultimately manufacture an explicit divisor-cycle
combination. -/
structure CodimOneCycleProducer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  combination :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 1))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP 1 α),
      CycleCombination G M X 1
  realizes :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 1))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP 1 α),
      (combination X α hX hα).eval M = α

/-- The constructive p=1 producer gives the existing concrete Lefschetz law. -/
def CodimOneCycleProducer.toLefschetz11ConcreteLaw
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : CodimOneCycleProducer G M) :
    BackwardAudit.Lefschetz11ConcreteLaw M :=
  {
    algebraic := by
      intro X α hX hα
      exact ⟨P.combination X α hX hα, P.realizes X α hX hα⟩
  }

/-- Exact Type-valued higher-codimension run for one endpoint input.

The return value contains the complete material chain:
SpreadData -> R1DescentPointContract -> R2PointProductionContract +
R3TransportContract. -/
structure HigherMaterialRun
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) where
  spread : BackwardAudit.SpreadData G X p α hX hα
  descent : BackwardAudit.R1DescentPointContract spread
  package : BackwardAudit.TypedR2R3Package M spread descent

/-- Constructive producer for every genuinely higher codimension.

No `ConcreteAlgebraicityPayload` or Hodge proposition occurs as an input. -/
structure HigherMaterialProducer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  run :
    ∀ (X : G.Variety)
      (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hp : 2 ≤ p)
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      HigherMaterialRun M X p α hX hα

/-- A complete higher-material run yields the literal finite-cycle witness at
the original class. -/
theorem higherMaterialRun_yields_concreteSpan
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (W : HigherMaterialRun M X p α hX hα) :
    InConcreteCycleSpan M α := by
  exact BackwardAudit.r1d_r2_r3_yields_concrete_witness
    W.descent W.package.r2 W.package.r3

/-- A constructive higher producer closes exactly the p>=2 material slice. -/
theorem higherMaterialProducer_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HigherMaterialProducer G M) :
    HigherCodimConcretePayload M := by
  intro X p α hp hX hα
  exact higherMaterialRun_yields_concreteSpan (P.run X p α hp hX hα)

/-- The complete concrete inhabitant.

Every field is constructive data.  There is no field of type
`ConcreteAlgebraicityPayload M`, `GradedRationalHodgeConjecture G`, or
`RationalHodgeConjecture D`. -/
structure HodgeConcreteInhabitant
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  codimZero : CodimZeroCycleProducer G M
  codimOne : CodimOneCycleProducer G M
  higher : HigherMaterialProducer G M

/-- Mechanical projection from the constructive inhabitant to the exact K18
frontier. -/
theorem HodgeConcreteInhabitant.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConcreteInhabitant G M) :
    ConcreteAlgebraicityPayload M := by
  exact concretePayload_of_materialProducers
    (codimZeroCycleProducer_closes H.codimZero)
    H.codimOne.toLefschetz11ConcreteLaw
    (higherMaterialProducer_closes H.higher)

/-- A concrete inhabitant plus the already-explicit K15 span adapter closes the
graded rational Hodge statement. -/
theorem HodgeConcreteInhabitant.toGradedHodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : HodgeConcreteInhabitant G M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload A).2 H.toConcretePayload

/-- Final bridge into the earlier semantic terminal law.

The semantic adapter is not hidden: it is the formalization link between the
graded concrete model and the earlier generic HodgeSemanticData. -/
theorem HodgeConcreteInhabitant.toTerminalCertifies
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (SA : GradedSemanticAdapter D G)
    (A : CycleSpanAdapter G M)
    (H : HodgeConcreteInhabitant G M) :
    HodgeTerminalCertifies D :=
  SA.gradedToOld (H.toGradedHodge A)

/-- Fully anchored producer: packages both formalization adapters together with
all constructive material witnesses.  Inhabiting this type is the exact final
construction target for the current repository architecture. -/
structure AnchoredHodgeInhabitant
    (D : HodgeSemanticData)
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  semanticAdapter : GradedSemanticAdapter D G
  spanAdapter : CycleSpanAdapter G M
  material : HodgeConcreteInhabitant G M

/-- The anchored inhabitant certifies the terminal statement with no additional
mathematical hypothesis. -/
theorem AnchoredHodgeInhabitant.certifies
    {D : HodgeSemanticData}
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : AnchoredHodgeInhabitant D G M) :
    HodgeTerminalCertifies D :=
  H.material.toTerminalCertifies H.semanticAdapter H.spanAdapter

#print axioms MCore.codimZeroCycleProducer_closes
#print axioms MCore.CodimOneCycleProducer.toLefschetz11ConcreteLaw
#print axioms MCore.higherMaterialRun_yields_concreteSpan
#print axioms MCore.higherMaterialProducer_closes
#print axioms MCore.HodgeConcreteInhabitant.toConcretePayload
#print axioms MCore.HodgeConcreteInhabitant.toGradedHodge
#print axioms MCore.HodgeConcreteInhabitant.toTerminalCertifies
#print axioms MCore.AnchoredHodgeInhabitant.certifies

end MCore
