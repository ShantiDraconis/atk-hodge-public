import MCore.BackwardAudit.R1dArithmeticIntersection
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3aHilbertProperness

namespace P05.Hodge.OpenMath

open MCore
open MCore.BackwardAudit

/--
Geometric H2 witness only.  It does not mention `InConcreteCycleSpan` and
therefore does not assume the R2 conclusion.
-/
structure UsefulQbarFiberGeometry
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  y : S.Base
  path : S.Path S.basepoint y
  hQbar : S.fieldOfDefinition.isDefinedOverQbar y
  hHodge : S.isHodgeAlong path
  hNonCircular : y ≠ S.basepoint

/-- Exact non-circular strengthening of the existing R1d arithmetic cut. -/
def NonCircularQbarIntersectsHodgeLocus
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ y : S.Base,
    y ≠ S.basepoint ∧
    S.hodgeLocusForAlpha y ∧
    S.fieldOfDefinition.isDefinedOverQbar y

/-- H2a has no hidden packaging beyond the non-circular arithmetic intersection. -/
theorem nonempty_usefulFiber_iff_nonCircularQbarIntersection
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (UsefulQbarFiberGeometry S) ↔
      NonCircularQbarIntersectsHodgeLocus S := by
  constructor
  · rintro ⟨U⟩
    exact ⟨U.y, U.hNonCircular, ⟨U.path, U.hHodge⟩, U.hQbar⟩
  · rintro ⟨y, hne, ⟨γ, hHodge⟩, hQbar⟩
    exact ⟨{
      y := y
      path := γ
      hQbar := hQbar
      hHodge := hHodge
      hNonCircular := hne
    }⟩

/-- The useful point gives an ordinary R1d descent witness without choice. -/
def UsefulQbarFiberGeometry.toDescentPoint
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (U : UsefulQbarFiberGeometry S) :
    R1DescentPointContract S :=
  {
    point := {
      y := U.y
      path := U.path
      y_is_hodge := U.hHodge
      y_is_defined_over_Qbar := U.hQbar
    }
  }

/--
H2 -> H3 forcing object with geometric provenance.

Unlike an arbitrary `CycleCombination`, every term is produced by one
relative Hilbert/Chow component over the useful Qbar fibre, and the component
is supplied together with proper+dense image laws.  The remaining equality is
the hard H2c statement: these geometrically produced cycle classes generate
the transported Hodge class.

Coefficients use `M.Coeff`, not `ℚ`: K15 intentionally keeps the
coefficient type abstract.
-/
structure HilbertGeneratedFiberDecomposition
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (U : UsefulQbarFiberGeometry S) where
  topology : ClosureInterface S.Base
  component : RelativeHilbertChowComponent S
  componentLaws : ProperDominantComponentLaws topology component
  terms : List (M.Coeff × component.PointAt U.y)
  class_decomposition :
    (show G.CohomologyQ (S.Family U.y) (2 * p) from
      (⟨terms.map (fun t => (t.1, component.cycleAt U.y t.2))⟩ :
        CycleCombination G M (S.Family U.y) p).eval M) =
      S.transportedAlpha U.path

/-- Forget only the Hilbert/Chow provenance and expose the concrete combination. -/
def HilbertGeneratedFiberDecomposition.toCombination
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {U : UsefulQbarFiberGeometry S}
    (D : HilbertGeneratedFiberDecomposition (M := M) U) :
    CycleCombination G M (S.Family U.y) p :=
  ⟨D.terms.map (fun t => (t.1, D.component.cycleAt U.y t.2))⟩

/--
Purely mechanical H3 projection.  No geometric theorem is used here:
the producer already supplied the explicit class equality.
-/
theorem decomposition_implies_concrete_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {U : UsefulQbarFiberGeometry S}
    (D : HilbertGeneratedFiberDecomposition (M := M) U) :
    InConcreteCycleSpan M (S.transportedAlpha U.path) := by
  refine ⟨D.toCombination, ?_⟩
  exact D.class_decomposition

/-- The same mechanical projection, stated at the repository's exact R2 cut. -/
theorem decomposition_implies_R2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {U : UsefulQbarFiberGeometry S}
    (D : HilbertGeneratedFiberDecomposition (M := M) U) :
    R2FiberAlgebraicityTarget M U.toDescentPoint := by
  exact decomposition_implies_concrete_span D

/-- Build the actual R2 contract, not merely its propositional target. -/
def HilbertGeneratedFiberDecomposition.toR2Contract
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {U : UsefulQbarFiberGeometry S}
    (D : HilbertGeneratedFiberDecomposition (M := M) U) :
    R2PointProductionContract M S U.toDescentPoint :=
  {
    produceCycle := {
      combination := D.toCombination
      combination_class := D.class_decomposition
    }
  }

/-- The H2->H3 object therefore inhabits the exact R2 wrapper mechanically. -/
theorem decomposition_implies_R2_nonempty
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {U : UsefulQbarFiberGeometry S}
    (D : HilbertGeneratedFiberDecomposition (M := M) U) :
    Nonempty (R2PointProductionContract M S U.toDescentPoint) :=
  ⟨D.toR2Contract⟩

/--
Exact producer to pressure next.  It is deliberately stronger than arbitrary
R2: it must choose a non-circular Qbar/Hodge fibre and a proper/dominant
Hilbert/Chow component whose fibre cycles generate the transported class.
-/
def UsefulFiberProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ U : UsefulQbarFiberGeometry S,
    Nonempty (HilbertGeneratedFiberDecomposition (M := M) U)

#print axioms P05.Hodge.OpenMath.decomposition_implies_concrete_span
#print axioms P05.Hodge.OpenMath.decomposition_implies_R2
#print axioms P05.Hodge.OpenMath.HilbertGeneratedFiberDecomposition.toR2Contract
#print axioms P05.Hodge.OpenMath.decomposition_implies_R2_nonempty


/--
H2a: a genuinely non-circular Qbar/Hodge fibre has been produced.
No cycle-span conclusion is included.
-/
structure H2aSpecialFiberProducer
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  useful : UsefulQbarFiberGeometry S

/--
H2b: Hilbert/Chow geometry exists over the useful fibre and its image is
proper/closed+dense in the abstract closure interface.  This produces genuine
cycles on the selected fibre, but says nothing yet about generation of alpha.
-/
structure H2bHilbertCycleProducer
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H2a : H2aSpecialFiberProducer S) where
  topology : ClosureInterface S.Base
  component : RelativeHilbertChowComponent S
  laws : ProperDominantComponentLaws topology component
  sourcePoint : component.PointAt H2a.useful.y

/-- A cycle genuinely sourced from the Hilbert/Chow point selected in H2b. -/
def H2bHilbertCycleProducer.sourceCycle
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a) :
    G.CycleQ (S.Family H2a.useful.y) p :=
  H2b.component.cycleAt H2a.useful.y H2b.sourcePoint

/--
H2c: the exact remaining generation statement, but with every term carrying
Hilbert/Chow provenance through H2b.component.PointAt.

This is the only field below that asserts that the transported Hodge class is
generated by the produced algebraic cycles.
-/
structure H2cCohomologyGenerationProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a) where
  terms : List (M.Coeff × H2b.component.PointAt H2a.useful.y)
  generates :
    (show G.CohomologyQ (S.Family H2a.useful.y) (2 * p) from
      (⟨terms.map (fun t =>
          (t.1, H2b.component.cycleAt H2a.useful.y t.2))⟩ :
        CycleCombination G M (S.Family H2a.useful.y) p).eval M) =
      S.transportedAlpha H2a.useful.path

/-- H2a + H2b + H2c assemble the provenance-backed decomposition. -/
def assembleHilbertGeneratedFiberDecomposition
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H2a : H2aSpecialFiberProducer S)
    (H2b : H2bHilbertCycleProducer H2a)
    (H2c : H2cCohomologyGenerationProducer (M := M) H2b) :
    HilbertGeneratedFiberDecomposition (M := M) H2a.useful :=
  {
    topology := H2b.topology
    component := H2b.component
    componentLaws := H2b.laws
    terms := H2c.terms
    class_decomposition := H2c.generates
  }

/-- Complete H2->H3 producer, split so the hard field cannot be hidden. -/
structure H2H3HilbertProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  h2a : H2aSpecialFiberProducer S
  h2b : H2bHilbertCycleProducer h2a
  h2c : H2cCohomologyGenerationProducer (M := M) h2b

/-- Complete H2->H3 data closes R2 by construction. -/
def H2H3HilbertProducer.toR2Contract
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : H2H3HilbertProducer M S) :
    R2PointProductionContract M S H.h2a.useful.toDescentPoint :=
  (assembleHilbertGeneratedFiberDecomposition H.h2a H.h2b H.h2c).toR2Contract

/-- Complete H2->H3 data also exposes the exact R2 target. -/
theorem H2H3HilbertProducer.closesR2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : H2H3HilbertProducer M S) :
    R2FiberAlgebraicityTarget M H.h2a.useful.toDescentPoint := by
  exact decomposition_implies_R2
    (assembleHilbertGeneratedFiberDecomposition H.h2a H.h2b H.h2c)

/--
Fail-closed frontier: these are status labels only.  They do not create an
inhabitant of any producer.
-/
inductive H2H3ForcingStatus where
  | typed
  | mechanicallyClosed
  | openGeometry
  | openGeneration
  deriving Repr, DecidableEq

structure H2H3ForcingFrontier where
  specialFiberType : H2H3ForcingStatus
  hilbertCycleType : H2H3ForcingStatus
  generationType : H2H3ForcingStatus
  decompositionToR2 : H2H3ForcingStatus
  specialFiberExistence : H2H3ForcingStatus
  hilbertCycleExistence : H2H3ForcingStatus
  transportedAlphaGeneration : H2H3ForcingStatus

def h2h3ForcingFrontier : H2H3ForcingFrontier :=
  {
    specialFiberType := .typed
    hilbertCycleType := .typed
    generationType := .typed
    decompositionToR2 := .mechanicallyClosed
    specialFiberExistence := .openGeometry
    hilbertCycleExistence := .openGeometry
    transportedAlphaGeneration := .openGeneration
  }

theorem h2h3_mechanical_tail_closed :
    h2h3ForcingFrontier.decompositionToR2 = .mechanicallyClosed := rfl

theorem h2c_generation_still_open :
    h2h3ForcingFrontier.transportedAlphaGeneration = .openGeneration := rfl

#print axioms P05.Hodge.OpenMath.assembleHilbertGeneratedFiberDecomposition
#print axioms P05.Hodge.OpenMath.H2H3HilbertProducer.toR2Contract
#print axioms P05.Hodge.OpenMath.H2H3HilbertProducer.closesR2
#print axioms P05.Hodge.OpenMath.h2h3_mechanical_tail_closed
#print axioms P05.Hodge.OpenMath.h2c_generation_still_open

/-- Once H2a/H2b/H2c are inhabited, the repository's exact R3 contract
    transports the concrete witness back to the original class. -/
theorem h2h3_then_r3_yields_original_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : H2H3HilbertProducer M S)
    (R3 : R3TransportContract M S) :
    InConcreteCycleSpan M α := by
  exact r1d_r2_r3_yields_concrete_witness
    H.h2a.useful.toDescentPoint
    H.toR2Contract
    R3

#print axioms P05.Hodge.OpenMath.nonempty_usefulFiber_iff_nonCircularQbarIntersection
#print axioms P05.Hodge.OpenMath.h2h3_then_r3_yields_original_span


/-!
## H2b does not imply H2c

The following fail-closed model proves that the current H2a/H2b interfaces,
including a proper+dense Hilbert/Chow component, cannot by themselves force
generation of the transported Hodge class.
-/

def h2cCounterG : GradedRationalHodgeData :=
  {
    Variety := Unit
    CohomologyQ := fun _ _ => Bool
    CycleQ := fun _ _ => Unit
    isSmoothProjective := fun _ => True
    isTypePP := fun _ _ => True
    inCycleClassSpan := fun _ _ => False
  }

def h2cCounterM : CycleSpanMechanics h2cCounterG :=
  {
    Coeff := Bool
    zero := false
    add := Bool.or
    smul := fun a b => a && b
    addClass := Bool.or
    zeroClass := false
    cycleClass := fun _ _ => false
  }

def h2cCounterSpread :
    SpreadData h2cCounterG () 2 true True.intro True.intro :=
  {
    Base := Bool
    basepoint := false
    Family := fun _ => ()
    fiberAtBasepoint := rfl
    Path := fun _ _ => Unit
    pathRefl := fun _ => ()
    pathComp := fun _ _ => ()
    parallelTransport := fun _ b => b
    parallelTransport_refl := by
      intro b β
      rfl
    parallelTransport_comp := by
      intro b0 b1 b2 γ01 γ12 β
      rfl
    fieldOfDefinition := {
      isDefinedOverQbar := fun _ => True
    }
  }

def h2cCounterUseful :
    UsefulQbarFiberGeometry h2cCounterSpread :=
  {
    y := true
    path := ()
    hQbar := True.intro
    hHodge := True.intro
    hNonCircular := by decide
  }

def h2cCounterClosure : ClosureInterface Bool :=
  {
    closure := fun _ _ => True
    subset_closure := by
      intro A b hb
      exact True.intro
  }

def h2cCounterComponent :
    RelativeHilbertChowComponent h2cCounterSpread :=
  {
    PointAt := fun _ => Unit
    cycleAt := fun _ _ => ()
  }

def h2cCounterComponentLaws :
    ProperDominantComponentLaws h2cCounterClosure h2cCounterComponent :=
  {
    imageClosed := by
      intro b hb
      exact ⟨()⟩
    imageDense := by
      intro b
      exact True.intro
  }

def h2cCounterH2a :
    H2aSpecialFiberProducer h2cCounterSpread :=
  { useful := h2cCounterUseful }

def h2cCounterH2b :
    H2bHilbertCycleProducer h2cCounterH2a :=
  {
    topology := h2cCounterClosure
    component := h2cCounterComponent
    laws := h2cCounterComponentLaws
    sourcePoint := ()
  }

theorem h2cCounterCombination_eval_false
    (C : CycleCombination h2cCounterG h2cCounterM () 2) :
    C.eval h2cCounterM = false := by
  cases C with
  | mk terms =>
      induction terms with
      | nil =>
          rfl
      | cons hd tl ih =>
          rcases hd with ⟨a, z⟩
          simp [CycleCombination.eval, h2cCounterM, ih]

/--
Even with H2a inhabited and H2b supplied by a proper+dense relative
Hilbert/Chow component, H2c can fail.  Therefore properness/dominance and
source-cycle existence are strictly insufficient for the generation step.
-/
theorem h2a_h2b_do_not_force_h2c :
    ¬ Nonempty
      (H2cCohomologyGenerationProducer
        (M := h2cCounterM) h2cCounterH2b) := by
  intro h
  rcases h with ⟨H2c⟩
  have heval :
      (⟨H2c.terms.map (fun t =>
          (t.1, h2cCounterH2b.component.cycleAt
            h2cCounterH2a.useful.y t.2))⟩ :
        CycleCombination h2cCounterG h2cCounterM () 2).eval
          h2cCounterM = false :=
    h2cCounterCombination_eval_false _
  have htrue :
      (⟨H2c.terms.map (fun t =>
          (t.1, h2cCounterH2b.component.cycleAt
            h2cCounterH2a.useful.y t.2))⟩ :
        CycleCombination h2cCounterG h2cCounterM () 2).eval
          h2cCounterM = true := by
    simpa [h2cCounterSpread, h2cCounterUseful] using H2c.generates
  rw [heval] at htrue
  cases htrue

#print axioms P05.Hodge.OpenMath.h2cCounterCombination_eval_false
#print axioms P05.Hodge.OpenMath.h2a_h2b_do_not_force_h2c


/-!
## Route D: divisor-intersection generation

The repository currently has a genuine codimension-one backend but no product,
intersection, Gysin, or Kunneth machinery connecting it to p >= 2.  The
following interface isolates exactly that missing geometry without asserting
that arbitrary Hodge classes are divisor-generated.
-/

/-- A typed p-fold intersection constructor on one fibre.
It manufactures actual codimension-p cycles from p divisor cycles. -/
structure DivisorIntersectionBackend
    {G : GradedRationalHodgeData}
    (X : G.Variety)
    (p : Nat) where
  DivisorTuple : Type
  divisors : DivisorTuple -> List (G.CycleQ X 1)
  length_eq : forall d : DivisorTuple, (divisors d).length = p
  intersect : DivisorTuple -> G.CycleQ X p

/-- Hilbert/Chow provenance for divisor-intersection cycles on the useful fibre.
No cohomological generation statement appears in this structure. -/
structure HilbertDivisorIntersectionRealization
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a)
    (I : DivisorIntersectionBackend (S.Family H2a.useful.y) p) where
  pointOfIntersection :
    I.DivisorTuple -> H2b.component.PointAt H2a.useful.y
  cycle_matches :
    forall d : I.DivisorTuple,
      H2b.component.cycleAt H2a.useful.y (pointOfIntersection d) =
        I.intersect d

/-- Purely geometric/cohomological target for the divisor route.
This does NOT say `InConcreteCycleSpan`; it says specifically that the
transported class is reconstructed from p-fold divisor intersections. -/
structure DivisorIntersectionGeneration
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (I : DivisorIntersectionBackend (S.Family H2a.useful.y) p) where
  terms : List (M.Coeff × I.DivisorTuple)
  reconstruct :
    (show G.CohomologyQ (S.Family H2a.useful.y) (2 * p) from
      (⟨terms.map (fun t => (t.1, I.intersect t.2))⟩ :
        CycleCombination G M (S.Family H2a.useful.y) p).eval M) =
      S.transportedAlpha H2a.useful.path

/-- Once the special fibre is divisor-generated and those intersection cycles
are realized in the chosen Hilbert/Chow component, H2c is mechanical. -/
def h2cOfDivisorIntersectionGeneration
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a)
    (I : DivisorIntersectionBackend (S.Family H2a.useful.y) p)
    (R : HilbertDivisorIntersectionRealization H2b I)
    (D : DivisorIntersectionGeneration (M := M) I) :
    H2cCohomologyGenerationProducer (M := M) H2b :=
  {
    terms := D.terms.map (fun t => (t.1, R.pointOfIntersection t.2))
    generates := by
      change
        (show G.CohomologyQ (S.Family H2a.useful.y) (2 * p) from
          (⟨(D.terms.map (fun t => (t.1, R.pointOfIntersection t.2))).map
              (fun t =>
                (t.1, H2b.component.cycleAt H2a.useful.y t.2))⟩ :
            CycleCombination G M (S.Family H2a.useful.y) p).eval M) =
          S.transportedAlpha H2a.useful.path
      simpa [List.map_map, Function.comp_def, R.cycle_matches] using D.reconstruct
  }

/-- Route-level producer.  The only genuinely new mathematical field is
`generation`: intersection machinery and Hilbert realization are separated
from the assertion that THIS transported class is generated by those cycles. -/
structure H2cDivisorRouteProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a) where
  intersection : DivisorIntersectionBackend (S.Family H2a.useful.y) p
  hilbertRealization :
    HilbertDivisorIntersectionRealization H2b intersection
  generation :
    DivisorIntersectionGeneration (M := M) intersection

def H2cDivisorRouteProducer.toH2c
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {H2b : H2bHilbertCycleProducer H2a}
    (D : H2cDivisorRouteProducer (M := M) H2b) :
    H2cCohomologyGenerationProducer (M := M) H2b :=
  h2cOfDivisorIntersectionGeneration
    H2b D.intersection D.hilbertRealization D.generation

inductive H2cDivisorRouteStatus where
  | typed
  | mechanical
  | missingIntersectionGeometry
  | missingGenerationTheorem
  deriving Repr, DecidableEq

structure H2cDivisorRouteFrontier where
  intersectionType : H2cDivisorRouteStatus
  hilbertRealizationToH2c : H2cDivisorRouteStatus
  concreteIntersectionBackend : H2cDivisorRouteStatus
  transportedAlphaDivisorGeneration : H2cDivisorRouteStatus

def h2cDivisorRouteFrontier : H2cDivisorRouteFrontier :=
  {
    intersectionType := .typed
    hilbertRealizationToH2c := .mechanical
    concreteIntersectionBackend := .missingIntersectionGeometry
    transportedAlphaDivisorGeneration := .missingGenerationTheorem
  }

theorem h2c_divisor_route_tail_mechanical :
    h2cDivisorRouteFrontier.hilbertRealizationToH2c = .mechanical := rfl

#print axioms P05.Hodge.OpenMath.h2cOfDivisorIntersectionGeneration
#print axioms P05.Hodge.OpenMath.H2cDivisorRouteProducer.toH2c
#print axioms P05.Hodge.OpenMath.h2c_divisor_route_tail_mechanical


/-!
## Route C: primitive/correspondence generation

No primitive-cohomology, Kunneth, Gysin, projector, motive, or correspondence
backend exists in the current repository.  This route therefore types the
smallest non-circular interface needed to turn a geometric correspondence
construction into H2c.
-/

/-- Auxiliary geometric source for a correspondence on the useful fibre.
The source object and correspondence data are intentionally abstract here:
they produce an actual codimension-p cycle, but contain no statement that the
target Hodge class is generated by such cycles. -/
structure CorrespondenceCycleBackend
    {G : GradedRationalHodgeData}
    (X : G.Variety)
    (p : Nat) where
  Source : Type
  CorrespondenceData : Source -> Type
  realize :
    (s : Source) -> CorrespondenceData s -> G.CycleQ X p

/-- Hilbert/Chow realization of cycles produced by the correspondence backend. -/
structure HilbertCorrespondenceRealization
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a)
    (C : CorrespondenceCycleBackend (S.Family H2a.useful.y) p) where
  pointOf :
    (s : C.Source) -> C.CorrespondenceData s ->
      H2b.component.PointAt H2a.useful.y
  cycle_matches :
    forall (s : C.Source) (d : C.CorrespondenceData s),
      H2b.component.cycleAt H2a.useful.y (pointOf s d) =
        C.realize s d

/-- Exact generation payload for the correspondence route.
This is the only field asserting that THIS transported class is reconstructed
from correspondence-produced algebraic cycles. -/
structure CorrespondenceGeneration
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (C : CorrespondenceCycleBackend (S.Family H2a.useful.y) p) where
  Term : Type
  coefficient : Term -> M.Coeff
  source : Term -> C.Source
  data : (t : Term) -> C.CorrespondenceData (source t)
  terms : List Term
  reconstruct :
    (show G.CohomologyQ (S.Family H2a.useful.y) (2 * p) from
      (⟨terms.map (fun t =>
          (coefficient t, C.realize (source t) (data t)))⟩ :
        CycleCombination G M (S.Family H2a.useful.y) p).eval M) =
      S.transportedAlpha H2a.useful.path

/-- Correspondence generation + Hilbert realization closes H2c mechanically. -/
def h2cOfCorrespondenceGeneration
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a)
    (C : CorrespondenceCycleBackend (S.Family H2a.useful.y) p)
    (R : HilbertCorrespondenceRealization H2b C)
    (D : CorrespondenceGeneration (M := M) C) :
    H2cCohomologyGenerationProducer (M := M) H2b :=
  {
    terms := D.terms.map (fun t =>
      (D.coefficient t, R.pointOf (D.source t) (D.data t)))
    generates := by
      change
        (show G.CohomologyQ (S.Family H2a.useful.y) (2 * p) from
          (⟨(D.terms.map (fun t =>
              (D.coefficient t,
                R.pointOf (D.source t) (D.data t)))).map
              (fun t =>
                (t.1, H2b.component.cycleAt H2a.useful.y t.2))⟩ :
            CycleCombination G M (S.Family H2a.useful.y) p).eval M) =
          S.transportedAlpha H2a.useful.path
      simpa [List.map_map, Function.comp_def, R.cycle_matches] using D.reconstruct
  }

/-- Complete correspondence-route producer. -/
structure H2cCorrespondenceRouteProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a) where
  correspondence :
    CorrespondenceCycleBackend (S.Family H2a.useful.y) p
  hilbertRealization :
    HilbertCorrespondenceRealization H2b correspondence
  generation :
    CorrespondenceGeneration (M := M) correspondence

def H2cCorrespondenceRouteProducer.toH2c
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {H2b : H2bHilbertCycleProducer H2a}
    (D : H2cCorrespondenceRouteProducer (M := M) H2b) :
    H2cCohomologyGenerationProducer (M := M) H2b :=
  h2cOfCorrespondenceGeneration
    H2b D.correspondence D.hilbertRealization D.generation

inductive H2cCorrespondenceRouteStatus where
  | typed
  | mechanical
  | missingCorrespondenceGeometry
  | missingGenerationTheorem
  deriving Repr, DecidableEq

structure H2cCorrespondenceRouteFrontier where
  correspondenceType : H2cCorrespondenceRouteStatus
  hilbertRealizationToH2c : H2cCorrespondenceRouteStatus
  concreteCorrespondenceBackend : H2cCorrespondenceRouteStatus
  transportedAlphaCorrespondenceGeneration : H2cCorrespondenceRouteStatus

def h2cCorrespondenceRouteFrontier : H2cCorrespondenceRouteFrontier :=
  {
    correspondenceType := .typed
    hilbertRealizationToH2c := .mechanical
    concreteCorrespondenceBackend := .missingCorrespondenceGeometry
    transportedAlphaCorrespondenceGeneration := .missingGenerationTheorem
  }

theorem h2c_correspondence_route_tail_mechanical :
    h2cCorrespondenceRouteFrontier.hilbertRealizationToH2c = .mechanical := rfl

#print axioms P05.Hodge.OpenMath.h2cOfCorrespondenceGeneration
#print axioms P05.Hodge.OpenMath.H2cCorrespondenceRouteProducer.toH2c
#print axioms P05.Hodge.OpenMath.h2c_correspondence_route_tail_mechanical


/-!
## Route C2: cohomological action of an algebraic correspondence

This refines Route C so the hard statement is no longer a generic
`reconstruct` field.  The correspondence carries an explicit action on
cohomology, a cycle-class compatibility law, and a finite algebraic source.
The only target-specific open equality is that the resulting action equals
the transported Hodge class.
-/

/-- Cohomological action attached to the already typed algebraic
correspondence backend.  `sourceClass` is an auxiliary class carrier; no
surjectivity or Hodge statement is built into this interface. -/
structure CohomologicalCorrespondenceAction
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : CorrespondenceCycleBackend X p) where
  SourceClass : Type
  classOf :
    (s : C.Source) -> C.CorrespondenceData s -> SourceClass
  act :
    SourceClass -> G.CohomologyQ X (2 * p)
  cycleClass_compat :
    forall (s : C.Source) (d : C.CorrespondenceData s),
      act (classOf s d) = M.cycleClass p (C.realize s d)

/-- Finite source package for the correspondence action.  This is lower-level
than H2c: it contains only coefficients and algebraic correspondence data. -/
structure FiniteCorrespondenceSource
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : CorrespondenceCycleBackend X p) where
  Term : Type
  coefficient : Term -> M.Coeff
  source : Term -> C.Source
  data : (t : Term) -> C.CorrespondenceData (source t)
  terms : List Term

/-- Evaluate the finite source after applying the correspondence action.
This uses the same K15 fold semantics as `CycleCombination.eval`. -/
def FiniteCorrespondenceSource.actionEval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : CorrespondenceCycleBackend X p}
    (A : CohomologicalCorrespondenceAction (M := M) C)
    (F : FiniteCorrespondenceSource (M := M) C) :
    G.CohomologyQ X (2 * p) :=
  F.terms.foldr
    (fun t acc =>
      M.addClass (M.smul (F.coefficient t)
        (A.act (A.classOf (F.source t) (F.data t)))) acc)
    M.zeroClass

/-- Mechanical compatibility: action evaluation is exactly evaluation of the
finite target-cycle combination produced by the same correspondence data. -/
theorem correspondence_actionEval_eq_cycleEval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : CorrespondenceCycleBackend X p}
    (A : CohomologicalCorrespondenceAction (M := M) C)
    (F : FiniteCorrespondenceSource (M := M) C) :
    F.actionEval A =
      (⟨F.terms.map (fun t =>
        (F.coefficient t, C.realize (F.source t) (F.data t)))⟩ :
        CycleCombination G M X p).eval M := by
  unfold FiniteCorrespondenceSource.actionEval
  induction F.terms with
  | nil =>
      rfl
  | cons hd tl ih =>
      simp [CycleCombination.eval, A.cycleClass_compat, ih]

/-- The unique target-specific mathematical equality for Route C2. -/
structure CorrespondenceHitsTransportedAlpha
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {C : CorrespondenceCycleBackend (S.Family H2a.useful.y) p}
    (A : CohomologicalCorrespondenceAction (M := M) C)
    (F : FiniteCorrespondenceSource (M := M) C) : Prop where
  hit :
    F.actionEval A = S.transportedAlpha H2a.useful.path

/-- Route C2 converts the single action equality into the older generation
payload mechanically. -/
def correspondenceGenerationOfActionHit
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (C : CorrespondenceCycleBackend (S.Family H2a.useful.y) p)
    (A : CohomologicalCorrespondenceAction (M := M) C)
    (F : FiniteCorrespondenceSource (M := M) C)
    (H : CorrespondenceHitsTransportedAlpha A F) :
    CorrespondenceGeneration (M := M) C :=
  {
    Term := F.Term
    coefficient := F.coefficient
    source := F.source
    data := F.data
    terms := F.terms
    reconstruct := by
      rw [← correspondence_actionEval_eq_cycleEval A F]
      exact H.hit
  }

/-- Complete refined correspondence route.  Geometry/action compatibility are
separated from the one target-specific hit equality. -/
structure H2cCohomologicalCorrespondenceProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a) where
  correspondence :
    CorrespondenceCycleBackend (S.Family H2a.useful.y) p
  hilbertRealization :
    HilbertCorrespondenceRealization H2b correspondence
  action :
    CohomologicalCorrespondenceAction (M := M) correspondence
  finiteSource :
    FiniteCorrespondenceSource (M := M) correspondence
  hitsTarget :
    CorrespondenceHitsTransportedAlpha action finiteSource

def H2cCohomologicalCorrespondenceProducer.toH2c
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {H2b : H2bHilbertCycleProducer H2a}
    (D : H2cCohomologicalCorrespondenceProducer (M := M) H2b) :
    H2cCohomologyGenerationProducer (M := M) H2b :=
  h2cOfCorrespondenceGeneration
    H2b
    D.correspondence
    D.hilbertRealization
    (correspondenceGenerationOfActionHit
      D.correspondence D.action D.finiteSource D.hitsTarget)

inductive H2cCorrespondenceActionStatus where
  | typed
  | mechanical
  | openActionGeometry
  | openTargetHit
  deriving Repr, DecidableEq

structure H2cCorrespondenceActionFrontier where
  actionType : H2cCorrespondenceActionStatus
  actionToGeneration : H2cCorrespondenceActionStatus
  concreteActionGeometry : H2cCorrespondenceActionStatus
  gammaPushesSourceToTransportedAlpha : H2cCorrespondenceActionStatus

def h2cCorrespondenceActionFrontier : H2cCorrespondenceActionFrontier :=
  {
    actionType := .typed
    actionToGeneration := .mechanical
    concreteActionGeometry := .openActionGeometry
    gammaPushesSourceToTransportedAlpha := .openTargetHit
  }

theorem h2c_correspondence_action_tail_mechanical :
    h2cCorrespondenceActionFrontier.actionToGeneration = .mechanical := rfl

#print axioms P05.Hodge.OpenMath.correspondence_actionEval_eq_cycleEval
#print axioms P05.Hodge.OpenMath.correspondenceGenerationOfActionHit
#print axioms P05.Hodge.OpenMath.H2cCohomologicalCorrespondenceProducer.toH2c
#print axioms P05.Hodge.OpenMath.h2c_correspondence_action_tail_mechanical


/-!
## Route C2 firewall and strict lower-codimension refinement

The abstract `CorrespondenceCycleBackend` is still too permissive: it can
encode arbitrary target cycles by taking the source itself to be `CycleQ X p`.
The following construction records that shortcut explicitly and therefore
prevents treating Route C2 as a genuine reduction unless the source geometry
is restricted.
-/

def identityCorrespondenceBackend
    {G : GradedRationalHodgeData}
    (X : G.Variety)
    (p : Nat) :
    CorrespondenceCycleBackend X p :=
  {
    Source := G.CycleQ X p
    CorrespondenceData := fun _ => Unit
    realize := fun z _ => z
  }

theorem identityCorrespondenceBackend_realize
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    (z : G.CycleQ X p) :
    (identityCorrespondenceBackend X p).realize z () = z := rfl

/--
A genuine correspondence reduction must start from lower codimension.
This structure cannot choose arbitrary target p-cycles as its source.
-/
structure LowerCodimCorrespondenceBackend
    {G : GradedRationalHodgeData}
    (X : G.Variety)
    (p : Nat) where
  sourceVariety : G.Variety
  q : Nat
  hq_lt_p : q < p
  Correspondence : Type
  pushCycle :
    Correspondence -> G.CycleQ sourceVariety q -> G.CycleQ X p

/-- Cohomological push-forward attached to the strict lower-codimension
correspondence, with compatibility against actual algebraic cycle classes. -/
structure LowerCodimCorrespondenceAction
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : LowerCodimCorrespondenceBackend X p) where
  pushClass :
    C.Correspondence ->
      G.CohomologyQ C.sourceVariety (2 * C.q) ->
      G.CohomologyQ X (2 * p)
  cycleClass_compat :
    forall (Γ : C.Correspondence)
      (z : G.CycleQ C.sourceVariety C.q),
      pushClass Γ (M.cycleClass C.q z) =
        M.cycleClass p (C.pushCycle Γ z)

/-- Finite algebraic source in strictly smaller codimension. -/
structure LowerCodimAlgebraicSource
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : LowerCodimCorrespondenceBackend X p) where
  terms :
    List (M.Coeff × C.Correspondence × G.CycleQ C.sourceVariety C.q)

/-- Evaluate the push-forward classes with K15's explicit fold semantics. -/
def LowerCodimAlgebraicSource.pushEval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : LowerCodimCorrespondenceBackend X p}
    (A : LowerCodimCorrespondenceAction (M := M) C)
    (F : LowerCodimAlgebraicSource (M := M) C) :
    G.CohomologyQ X (2 * p) :=
  F.terms.foldr
    (fun t acc =>
      M.addClass
        (M.smul t.1 (A.pushClass t.2.1 (M.cycleClass C.q t.2.2)))
        acc)
    M.zeroClass

/-- The lower-codimension push evaluation agrees mechanically with the
target-cycle combination obtained by pushing the source cycles. -/
theorem lowerCodim_pushEval_eq_cycleEval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : LowerCodimCorrespondenceBackend X p}
    (A : LowerCodimCorrespondenceAction (M := M) C)
    (F : LowerCodimAlgebraicSource (M := M) C) :
    F.pushEval A =
      (⟨F.terms.map (fun t =>
        (t.1, C.pushCycle t.2.1 t.2.2))⟩ :
        CycleCombination G M X p).eval M := by
  unfold LowerCodimAlgebraicSource.pushEval
  induction F.terms with
  | nil =>
      rfl
  | cons hd tl ih =>
      rcases hd with ⟨a, Γ, z⟩
      simp [CycleCombination.eval, A.cycleClass_compat, ih]

/-- Exact target-specific hard equality for the strict Route C3. -/
structure LowerCodimCorrespondenceHitsTransportedAlpha
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {C : LowerCodimCorrespondenceBackend
      (S.Family H2a.useful.y) p}
    (A : LowerCodimCorrespondenceAction (M := M) C)
    (F : LowerCodimAlgebraicSource (M := M) C) : Prop where
  hit :
    F.pushEval A = S.transportedAlpha H2a.useful.path

/-- Adapt the strict lower-codimension backend to Route C only after the
geometric restriction q < p has been enforced. -/
def lowerCodimToCorrespondenceBackend
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    (C : LowerCodimCorrespondenceBackend X p) :
    CorrespondenceCycleBackend X p :=
  {
    Source := C.Correspondence × G.CycleQ C.sourceVariety C.q
    CorrespondenceData := fun _ => Unit
    realize := fun s _ => C.pushCycle s.1 s.2
  }

/-- The strict action-hit equality supplies Route C generation mechanically. -/
def correspondenceGenerationOfLowerCodimHit
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (C : LowerCodimCorrespondenceBackend
      (S.Family H2a.useful.y) p)
    (A : LowerCodimCorrespondenceAction (M := M) C)
    (F : LowerCodimAlgebraicSource (M := M) C)
    (H : LowerCodimCorrespondenceHitsTransportedAlpha A F) :
    CorrespondenceGeneration
      (M := M) (lowerCodimToCorrespondenceBackend C) :=
  {
    Term :=
      M.Coeff × C.Correspondence × G.CycleQ C.sourceVariety C.q
    coefficient := fun t => t.1
    source := fun t => (t.2.1, t.2.2)
    data := fun _ => ()
    terms := F.terms
    reconstruct := by
      rw [← lowerCodim_pushEval_eq_cycleEval A F]
      exact H.hit
  }

inductive H2cLowerCodimRouteStatus where
  | firewallProved
  | typed
  | mechanical
  | openLowerCodimGeometry
  | openTargetHit
  deriving Repr, DecidableEq

structure H2cLowerCodimRouteFrontier where
  arbitraryCorrespondenceShortcut : H2cLowerCodimRouteStatus
  strictLowerCodimType : H2cLowerCodimRouteStatus
  lowerCodimToGeneration : H2cLowerCodimRouteStatus
  concretePushforwardGeometry : H2cLowerCodimRouteStatus
  pushedSourceHitsTransportedAlpha : H2cLowerCodimRouteStatus

def h2cLowerCodimRouteFrontier : H2cLowerCodimRouteFrontier :=
  {
    arbitraryCorrespondenceShortcut := .firewallProved
    strictLowerCodimType := .typed
    lowerCodimToGeneration := .mechanical
    concretePushforwardGeometry := .openLowerCodimGeometry
    pushedSourceHitsTransportedAlpha := .openTargetHit
  }

theorem h2c_lowerCodim_route_tail_mechanical :
    h2cLowerCodimRouteFrontier.lowerCodimToGeneration = .mechanical := rfl

#print axioms P05.Hodge.OpenMath.identityCorrespondenceBackend_realize
#print axioms P05.Hodge.OpenMath.lowerCodim_pushEval_eq_cycleEval
#print axioms P05.Hodge.OpenMath.correspondenceGenerationOfLowerCodimHit
#print axioms P05.Hodge.OpenMath.h2c_lowerCodim_route_tail_mechanical


/-!
## Route C3.1: force q = 1 and reuse Lefschetz (1,1)

This route specializes the strict lower-codimension correspondence to
codimension one.  It does not assert that every p >= 2 Hodge class comes from
a divisor correspondence; it only makes that sufficient route explicit.
-/

/-- Strict lower-codimension correspondence with q definitionally equal to 1. -/
structure DivisorSourceCorrespondenceBackend
    {G : GradedRationalHodgeData}
    (X : G.Variety)
    (p : Nat) where
  hp : 2 <= p
  sourceVariety : G.Variety
  Correspondence : Type
  pushDivisor :
    Correspondence -> G.CycleQ sourceVariety 1 -> G.CycleQ X p

def DivisorSourceCorrespondenceBackend.toLowerCodim
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    (C : DivisorSourceCorrespondenceBackend X p) :
    LowerCodimCorrespondenceBackend X p :=
  {
    sourceVariety := C.sourceVariety
    q := 1
    hq_lt_p := lt_of_lt_of_le (by decide : 1 < 2) C.hp
    Correspondence := C.Correspondence
    pushCycle := C.pushDivisor
  }

/-- Cohomological action for the divisor-source correspondence. -/
structure DivisorSourceCorrespondenceAction
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : DivisorSourceCorrespondenceBackend X p) where
  pushClass :
    C.Correspondence ->
      G.CohomologyQ C.sourceVariety (2 * 1) ->
      G.CohomologyQ X (2 * p)
  cycleClass_compat :
    forall (Γ : C.Correspondence)
      (z : G.CycleQ C.sourceVariety 1),
      pushClass Γ (M.cycleClass 1 z) =
        M.cycleClass p (C.pushDivisor Γ z)

def DivisorSourceCorrespondenceAction.toLowerCodim
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : DivisorSourceCorrespondenceBackend X p}
    (A : DivisorSourceCorrespondenceAction (M := M) C) :
    LowerCodimCorrespondenceAction
      (M := M) C.toLowerCodim :=
  {
    pushClass := A.pushClass
    cycleClass_compat := A.cycleClass_compat
  }

/-- Finite list of source divisor cycles together with the correspondence
used to push each one to codimension p. -/
structure DivisorSourceFiniteData
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : DivisorSourceCorrespondenceBackend X p) where
  terms :
    List (M.Coeff × C.Correspondence × G.CycleQ C.sourceVariety 1)

def DivisorSourceFiniteData.toLowerCodim
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : DivisorSourceCorrespondenceBackend X p}
    (F : DivisorSourceFiniteData (M := M) C) :
    LowerCodimAlgebraicSource (M := M) C.toLowerCodim :=
  { terms := F.terms }

/-- Exact target hit for the q=1 route. -/
structure DivisorCorrespondenceHitsTransportedAlpha
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {C : DivisorSourceCorrespondenceBackend
      (S.Family H2a.useful.y) p}
    (A : DivisorSourceCorrespondenceAction (M := M) C)
    (F : DivisorSourceFiniteData (M := M) C) : Prop where
  hit :
    (F.toLowerCodim).pushEval A.toLowerCodim =
      S.transportedAlpha H2a.useful.path

/-- Package a codimension-one algebraicity law on the auxiliary source.
This makes the intended reuse of Lefschetz (1,1) explicit. -/
structure DivisorSourceLefschetzData
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    (C : DivisorSourceCorrespondenceBackend X p) where
  hSourceSmoothProjective :
    G.isSmoothProjective C.sourceVariety
  lefschetz11 :
    MCore.BackwardAudit.Lefschetz11ConcreteLaw M

/-- Extract concrete algebraicity of any source (1,1)-class. -/
theorem divisorSource_class_algebraic
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {C : DivisorSourceCorrespondenceBackend X p}
    (L : DivisorSourceLefschetzData (M := M) C)
    (β : G.CohomologyQ C.sourceVariety (2 * 1))
    (hβ : G.isTypePP 1 β) :
    InConcreteCycleSpan M β :=
  L.lefschetz11.algebraic
    C.sourceVariety β L.hSourceSmoothProjective hβ

/-- Complete q=1 route.  Notice that the source cycles themselves are explicit;
Lefschetz is recorded separately as the classical reason this source class can
be algebraic in genuine geometry. -/
structure H2cDivisorCorrespondenceProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    (H2b : H2bHilbertCycleProducer H2a) where
  correspondence :
    DivisorSourceCorrespondenceBackend (S.Family H2a.useful.y) p
  action :
    DivisorSourceCorrespondenceAction (M := M) correspondence
  finiteSource :
    DivisorSourceFiniteData (M := M) correspondence
  hitsTarget :
    DivisorCorrespondenceHitsTransportedAlpha action finiteSource
  hilbertRealization :
    HilbertCorrespondenceRealization H2b
      (lowerCodimToCorrespondenceBackend correspondence.toLowerCodim)

/-- q=1 correspondence route closes H2c mechanically once the target-hit
equality is supplied. -/
def H2cDivisorCorrespondenceProducer.toH2c
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {H2a : H2aSpecialFiberProducer S}
    {H2b : H2bHilbertCycleProducer H2a}
    (D : H2cDivisorCorrespondenceProducer (M := M) H2b) :
    H2cCohomologyGenerationProducer (M := M) H2b := by
  let Hlower :
      LowerCodimCorrespondenceHitsTransportedAlpha
        D.action.toLowerCodim D.finiteSource.toLowerCodim :=
    { hit := D.hitsTarget.hit }
  exact h2cOfCorrespondenceGeneration
    H2b
    (lowerCodimToCorrespondenceBackend D.correspondence.toLowerCodim)
    D.hilbertRealization
    (correspondenceGenerationOfLowerCodimHit
      D.correspondence.toLowerCodim
      D.action.toLowerCodim
      D.finiteSource.toLowerCodim
      Hlower)

inductive H2cDivisorCorrespondenceStatus where
  | typed
  | mechanical
  | classicalSourceAvailable
  | openPushforwardGeometry
  | openTargetHit
  deriving Repr, DecidableEq

structure H2cDivisorCorrespondenceFrontier where
  qEqualsOne : H2cDivisorCorrespondenceStatus
  sourceLefschetz : H2cDivisorCorrespondenceStatus
  q1ToH2c : H2cDivisorCorrespondenceStatus
  concretePushforwardGeometry : H2cDivisorCorrespondenceStatus
  pushedDivisorsHitTransportedAlpha : H2cDivisorCorrespondenceStatus

def h2cDivisorCorrespondenceFrontier :
    H2cDivisorCorrespondenceFrontier :=
  {
    qEqualsOne := .typed
    sourceLefschetz := .classicalSourceAvailable
    q1ToH2c := .mechanical
    concretePushforwardGeometry := .openPushforwardGeometry
    pushedDivisorsHitTransportedAlpha := .openTargetHit
  }

theorem h2c_divisor_correspondence_tail_mechanical :
    h2cDivisorCorrespondenceFrontier.q1ToH2c = .mechanical := rfl

#print axioms P05.Hodge.OpenMath.DivisorSourceCorrespondenceBackend.toLowerCodim
#print axioms P05.Hodge.OpenMath.divisorSource_class_algebraic
#print axioms P05.Hodge.OpenMath.H2cDivisorCorrespondenceProducer.toH2c
#print axioms P05.Hodge.OpenMath.h2c_divisor_correspondence_tail_mechanical

end P05.Hodge.OpenMath
