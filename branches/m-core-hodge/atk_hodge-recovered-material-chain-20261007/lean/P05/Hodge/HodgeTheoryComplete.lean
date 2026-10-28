import P05.Hodge.HodgeFormalRealization
import P05.Hodge.HodgeMaterialMincut
import P05.Hodge.HigherR3KernelPressure
import MCore.BackwardAudit.R1dQbarPointBoundary
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3SpecializationBoundary

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-!
# Canonical Hodge material theory

This file is the forward-only theory layer for the current P05-HODGE lane.

It separates:
* formal realization data;
* the six constructive material producers;
* the exact higher-codimension residues R1d/R2/R3;
* the terminal payload.

No theorem below assumes the terminal payload in order to reconstruct it.
-/

/-- Leaf 0: codimension-zero component cycle production. -/
abbrev CodimZeroMaterialTarget
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) :=
  CodimZeroComponentBackend G M

/-- Leaf 1: codimension-one divisor production. -/
abbrev CodimOneMaterialTarget
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) :=
  Lefschetz11DivisorBackend G M

/-- Leaf 2: a spread attached to every higher-codimension endpoint input. -/
abbrev HigherSpreadMaterialTarget
    (G : GradedRationalHodgeData) :=
  HigherSpreadProducer G

/-- Leaf 3: an arithmetic/Qbar Hodge point on the selected spread. -/
abbrev HigherQbarMaterialTarget
    {G : GradedRationalHodgeData}
    (S : HigherSpreadProducer G) :=
  HigherQbarPointProducer S

/-- Leaf 4: a finite concrete cycle combination on the selected fibre. -/
abbrev HigherFiberMaterialTarget
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (S : HigherSpreadProducer G)
    (Q : HigherQbarPointProducer S) :=
  HigherFiberCycleProducer M S Q

/-- Leaf 5: specialization/transport of concrete cycles back to the source. -/
abbrev HigherTransportMaterialTarget
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (S : HigherSpreadProducer G) :=
  HigherTransportProducer M S

/-- The full forward-only mathematical source package. -/
structure HodgeTheoryPackage
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  realization : HodgeFormalRealization G M
  codimZero : CodimZeroMaterialTarget G M
  codimOne : CodimOneMaterialTarget G M
  higherSpread : HigherSpreadMaterialTarget G
  higherQbar : HigherQbarMaterialTarget higherSpread
  higherFiber : HigherFiberMaterialTarget M higherSpread higherQbar
  higherTransport : HigherTransportMaterialTarget M higherSpread

def HodgeTheoryPackage.toMaterialMincut
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (T : HodgeTheoryPackage G M) :
    HodgeMaterialMincut G M :=
  {
    codimZero := T.codimZero
    codimOne := T.codimOne
    higherSpread := T.higherSpread
    higherQbar := T.higherQbar
    higherFiber := T.higherFiber
    higherTransport := T.higherTransport
  }

def HodgeTheoryPackage.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (T : HodgeTheoryPackage G M) :
    ConcreteAlgebraicityPayload M :=
  formalRealization_plus_material_closes
    T.realization T.toMaterialMincut

/-- Canonical terminal theorem: once the forward source package is genuinely
inhabited, the exact concrete algebraicity endpoint follows. -/
theorem hodge_theory_package_closes_terminal
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (T : HodgeTheoryPackage G M) :
    HodgeTerminalCertifies (canonicalHodgeSemanticData G M) :=
  (canonicalTerminal_iff_concretePayload G M).2 (HodgeTheoryPackage.toConcretePayload T)

/-- The higher-codimension path is explicitly decomposed into three exact
mathematical residues after the spread has been chosen. -/
structure HigherExactResidues
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  r1dContract : R1DescentPointContract S
  r2 : R2FiberAlgebraicityTarget M r1dContract
  r3 : R3SpecializationPayload M S

theorem HigherExactResidues.r1d_target
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : HigherExactResidues M S) :
    R1dQbarHodgePointTarget S :=
  (r1d_contract_iff_target S).1 ⟨R.r1dContract⟩

/-- Theory inventory: 1 formal realization package + 6 material leaves. -/
def theoryInputCount : Nat := 7

theorem theoryInputCount_eq_seven :
    theoryInputCount = 7 := rfl

/-- Structural/type theory is complete; material inhabitance is intentionally
not asserted by this module. -/
inductive TheoryLayerStatus
  | typed
  | materialOpen
  deriving DecidableEq, Repr

structure HodgeTheoryLedger where
  formalTheory : TheoryLayerStatus
  codimZero : TheoryLayerStatus
  codimOne : TheoryLayerStatus
  higherSpread : TheoryLayerStatus
  higherQbar : TheoryLayerStatus
  higherFiber : TheoryLayerStatus
  higherTransport : TheoryLayerStatus
  deriving Repr

def hodgeTheoryLedger : HodgeTheoryLedger :=
  {
    formalTheory := .typed
    codimZero := .materialOpen
    codimOne := .materialOpen
    higherSpread := .materialOpen
    higherQbar := .materialOpen
    higherFiber := .materialOpen
    higherTransport := .materialOpen
  }

#print axioms P05.Hodge.HodgeTheoryPackage.toMaterialMincut
#print axioms P05.Hodge.HodgeTheoryPackage.toConcretePayload
#print axioms P05.Hodge.hodge_theory_package_closes_terminal
#print axioms P05.Hodge.theoryInputCount_eq_seven

end P05.Hodge
