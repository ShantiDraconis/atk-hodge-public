import MCore.OpenMath.HodgePrizeSurgeryLane2

namespace MCore

/-- Concrete geometry payload for the refutation lane. -/
structure HodgePrizeGeometryPayload (D : ClayHodgeData) where
  Xsurgery : D.Variety
  smoothProjective : D.isProjectiveNonsingularOverC Xsurgery
  constructionName : String
  sourceDescription : String
  gluingDescription : String
  criticalTransition : HodgeCriticalTransition
  identifiesSurgeryPoint : Prop
  certifiedAtCriticalBalance : identifiesSurgeryPoint

/-- Minimal genuinely mathematical residue of GEOMETRY after descriptive
metadata is fixed. The critical transition is explicit to avoid hidden imports. -/
structure HodgePrizeGeometryCore (D : ClayHodgeData) where
  Xsurgery : D.Variety
  smoothProjective : D.isProjectiveNonsingularOverC Xsurgery
  criticalTransition : HodgeCriticalTransition
  identifiesSurgeryPoint : Prop
  certifiedAtCriticalBalance : identifiesSurgeryPoint

def geometryPayloadFromCore
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryCore D) :
    HodgePrizeGeometryPayload D :=
  {
    Xsurgery := G.Xsurgery
    smoothProjective := G.smoothProjective
    constructionName := "critical-balance-surgery"
    sourceDescription := "geometry generated at the certified critical balance frontier"
    gluingDescription := "minimal-cut surgery candidate"
    criticalTransition := G.criticalTransition
    identifiesSurgeryPoint := G.identifiesSurgeryPoint
    certifiedAtCriticalBalance := G.certifiedAtCriticalBalance
  }

/-- Concrete rational Hodge-class payload on the chosen surgery geometry. -/
structure HodgePrizeClassPayload
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryPayload D) where
  p : Nat
  h : D.Cohomology G.Xsurgery (2 * p)
  rational : D.isRationalClass h
  typePP : D.isTypePP p h

/-- Minimal scientific core of CLASS. -/
structure HodgePrizeClassCore
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D) where
  p : Nat
  h : D.Cohomology G.Xsurgery (2 * p)
  rational : D.isRationalClass h
  typePP : D.isTypePP p h

def classPayloadFromCore
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) :
    HodgePrizeClassPayload D (geometryPayloadFromCore G) :=
  {
    p := C.p
    h := C.h
    rational := C.rational
    typePP := C.typePP
  }

/-- Explicit separating invariant on the full cohomology carrier in the
chosen degree. It must vanish on every rational algebraic-cycle combination
and detect the chosen Hodge class. -/
structure HodgePrizeSeparatorCore
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) where
  I : D.Cohomology G.Xsurgery (2 * C.p) → Nat
  algebraicVanishes :
    ∀ α : D.Cohomology G.Xsurgery (2 * C.p),
      D.isRationalLinearCombinationOfCycleClasses α →
      I α = 0
  detectsH : I C.h ≠ 0

theorem separator_proves_notAlgebraic
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (S : HodgePrizeSeparatorCore D G C) :
    ¬ D.isRationalLinearCombinationOfCycleClasses C.h := by
  intro hAlg
  exact S.detectsH (S.algebraicVanishes C.h hAlg)

noncomputable def notAlgebraic_to_separator
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (hNA : ¬ D.isRationalLinearCombinationOfCycleClasses C.h) :
    HodgePrizeSeparatorCore D G C := by
  classical
  let I : D.Cohomology G.Xsurgery (2 * C.p) → Nat :=
    fun α => if D.isRationalLinearCombinationOfCycleClasses α then 0 else 1
  refine {
    I := I
    algebraicVanishes := ?_
    detectsH := ?_
  }
  · intro α hAlg
    simp [I, hAlg]
  · simp [I, hNA]

theorem separator_iff_notAlgebraic
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G} :
    Nonempty (HodgePrizeSeparatorCore D G C) ↔
      ¬ D.isRationalLinearCombinationOfCycleClasses C.h := by
  constructor
  · intro h
    rcases h with ⟨S⟩
    exact separator_proves_notAlgebraic S
  · intro h
    exact ⟨notAlgebraic_to_separator h⟩

/-- Exact coefficient syntax for finite rational combinations. -/
structure HodgeRationalCoeffEncoding where
  numerator : Int
  denominator : Nat
  denominatorPositive : 0 < denominator

/-- One term q * [Z] in codimension p. This is syntax only; no hidden
cohomology addition or scalar multiplication is assumed. -/
structure HodgeCycleSpanTerm
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) where
  coeff : HodgeRationalCoeffEncoding
  cycle : D.AlgebraicCycle G.Xsurgery C.p

/-- A concrete finite-span syntax plus its semantic evaluator. The evaluator
and completeness theorem are the real model obligations. -/
structure HodgeFiniteCycleSpanSemantics
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) where
  eval :
    List (HodgeCycleSpanTerm D G C) →
      D.Cohomology G.Xsurgery (2 * C.p)
  sound :
    ∀ terms : List (HodgeCycleSpanTerm D G C),
      D.isRationalLinearCombinationOfCycleClasses (eval terms)
  complete :
    ∀ α : D.Cohomology G.Xsurgery (2 * C.p),
      D.isRationalLinearCombinationOfCycleClasses α →
      ∃ terms : List (HodgeCycleSpanTerm D G C), eval terms = α

/-- Minimal operations required to interpret finite rational
combinations of cycle classes in the chosen cohomology group. No field/module
instance is fabricated; every operation and law is explicit data. -/
structure HodgeRationalCohomologyOperations
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) where
  zero : D.Cohomology G.Xsurgery (2 * C.p)
  add :
    D.Cohomology G.Xsurgery (2 * C.p) →
    D.Cohomology G.Xsurgery (2 * C.p) →
    D.Cohomology G.Xsurgery (2 * C.p)
  qsmul :
    HodgeRationalCoeffEncoding →
    D.Cohomology G.Xsurgery (2 * C.p) →
    D.Cohomology G.Xsurgery (2 * C.p)
  zero_in_span :
    D.isRationalLinearCombinationOfCycleClasses zero
  cycle_scaled_in_span :
    ∀ (q : HodgeRationalCoeffEncoding)
      (Z : D.AlgebraicCycle G.Xsurgery C.p),
      D.isRationalLinearCombinationOfCycleClasses
        (qsmul q (D.cycleClass Z))
  add_closed :
    ∀ a b,
      D.isRationalLinearCombinationOfCycleClasses a →
      D.isRationalLinearCombinationOfCycleClasses b →
      D.isRationalLinearCombinationOfCycleClasses (add a b)

def finiteSpanEval
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C) :
    List (HodgeCycleSpanTerm D G C) →
      D.Cohomology G.Xsurgery (2 * C.p)
  | [] => O.zero
  | t :: ts =>
      O.add
        (O.qsmul t.coeff (D.cycleClass t.cycle))
        (finiteSpanEval O ts)

theorem finiteSpanEval_sound
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C) :
    ∀ terms : List (HodgeCycleSpanTerm D G C),
      D.isRationalLinearCombinationOfCycleClasses (finiteSpanEval O terms) := by
  intro terms
  induction terms with
  | nil =>
      exact O.zero_in_span
  | cons t ts ih =>
      exact O.add_closed
        (O.qsmul t.coeff (D.cycleClass t.cycle))
        (finiteSpanEval O ts)
        (O.cycle_scaled_in_span t.coeff t.cycle)
        ih

/-- Witness-based concrete finite-span membership for the current Clay interface. -/
def HodgeConcreteFiniteSpanAt
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C)
    (α : D.Cohomology G.Xsurgery (2 * C.p)) : Prop :=
  ∃ terms : List (HodgeCycleSpanTerm D G C), finiteSpanEval O terms = α

theorem concreteFiniteSpan_implies_abstract
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C)
    {α : D.Cohomology G.Xsurgery (2 * C.p)}
    (h : HodgeConcreteFiniteSpanAt O α) :
    D.isRationalLinearCombinationOfCycleClasses α := by
  rcases h with ⟨terms, rfl⟩
  exact finiteSpanEval_sound O terms

/-- Exact open adapter direction: every abstract span member has an explicit
finite rational cycle-combination witness. -/
def HodgeFiniteSpanCompleteness
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C) : Prop :=
  ∀ α : D.Cohomology G.Xsurgery (2 * C.p),
    D.isRationalLinearCombinationOfCycleClasses α →
    HodgeConcreteFiniteSpanAt O α

theorem finiteSpan_iff_abstract_given_complete
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C)
    (hComplete : HodgeFiniteSpanCompleteness O)
    (α : D.Cohomology G.Xsurgery (2 * C.p)) :
    D.isRationalLinearCombinationOfCycleClasses α ↔
      HodgeConcreteFiniteSpanAt O α := by
  constructor
  · exact hComplete α
  · exact concreteFiniteSpan_implies_abstract O

/-- Separator phrased only on explicit finite cycle-combination witnesses.
This avoids assuming a global semantic law on every cohomology class. -/
structure HodgeFiniteWitnessSeparator
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C) where
  I : D.Cohomology G.Xsurgery (2 * C.p) → Nat
  vanishes :
    ∀ terms : List (HodgeCycleSpanTerm D G C),
      I (finiteSpanEval O terms) = 0
  detects : I C.h ≠ 0

theorem finiteWitnessSeparator_proves_notAlgebraic
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (O : HodgeRationalCohomologyOperations D G C)
    (hComplete : HodgeFiniteSpanCompleteness O)
    (S : HodgeFiniteWitnessSeparator O) :
    ¬ D.isRationalLinearCombinationOfCycleClasses C.h := by
  intro hAlg
  rcases hComplete C.h hAlg with ⟨terms, hterms⟩
  apply S.detects
  rw [← hterms]
  exact S.vanishes terms

/-- Dedicated semantic core for the finite rational cycle span. -/
structure HodgeFiniteSpanSemanticCore
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) where
  eval :
    List (HodgeCycleSpanTerm D G C) →
      D.Cohomology G.Xsurgery (2 * C.p)
  sound :
    ∀ terms : List (HodgeCycleSpanTerm D G C),
      D.isRationalLinearCombinationOfCycleClasses (eval terms)
  complete :
    ∀ α : D.Cohomology G.Xsurgery (2 * C.p),
      D.isRationalLinearCombinationOfCycleClasses α →
      ∃ terms : List (HodgeCycleSpanTerm D G C), eval terms = α

def finiteSpanSemanticsFromCore
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (S : HodgeFiniteSpanSemanticCore D G C) :
    HodgeFiniteCycleSpanSemantics D G C :=
  {
    eval := S.eval
    sound := S.sound
    complete := S.complete
  }

/-- Concrete semantic model for a non-circular separation argument.
SpanWitness represents actual finite rational combinations of algebraic cycle
classes. realize interprets them in cohomology, and spanComplete connects that
explicit carrier to the Clay predicate. -/
structure HodgeConcreteSpanSeparationModel
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) where
  SpanWitness : Type
  realize : SpanWitness → D.Cohomology G.Xsurgery (2 * C.p)
  spanComplete :
    ∀ α : D.Cohomology G.Xsurgery (2 * C.p),
      D.isRationalLinearCombinationOfCycleClasses α →
      ∃ w : SpanWitness, realize w = α
  I : D.Cohomology G.Xsurgery (2 * C.p) → Nat
  vanishesOnRealizedSpan : ∀ w : SpanWitness, I (realize w) = 0
  detectsH : I C.h ≠ 0

def concreteSpanModelFromFiniteSemantics
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (S : HodgeFiniteCycleSpanSemantics D G C)
    (I : D.Cohomology G.Xsurgery (2 * C.p) → Nat)
    (vanishes :
      ∀ terms : List (HodgeCycleSpanTerm D G C),
        I (S.eval terms) = 0)
    (detects : I C.h ≠ 0) :
    HodgeConcreteSpanSeparationModel D G C :=
  {
    SpanWitness := List (HodgeCycleSpanTerm D G C)
    realize := S.eval
    spanComplete := S.complete
    I := I
    vanishesOnRealizedSpan := vanishes
    detectsH := detects
  }

theorem concrete_span_model_proves_notAlgebraic
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (M : HodgeConcreteSpanSeparationModel D G C) :
    ¬ D.isRationalLinearCombinationOfCycleClasses C.h := by
  intro hAlg
  rcases M.spanComplete C.h hAlg with ⟨w, hw⟩
  apply M.detectsH
  rw [← hw]
  exact M.vanishesOnRealizedSpan w

/-- Exact remaining scientific theorem after GEOMETRY and CLASS are fixed. -/
structure HodgePrizeSeparationCore
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G) : Prop where
  notAlgebraic :
    ¬ D.isRationalLinearCombinationOfCycleClasses C.h

def separationCoreFromConcreteSpanModel
    {D : ClayHodgeData}
    {G : HodgePrizeGeometryCore D}
    {C : HodgePrizeClassCore D G}
    (M : HodgeConcreteSpanSeparationModel D G C) :
    HodgePrizeSeparationCore D G C :=
  { notAlgebraic := concrete_span_model_proves_notAlgebraic M }

/-- Final separation payload: the chosen rational (p,p)-class is outside
the rational span of algebraic cycle classes. -/
def separationCoreFromSeparator
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G)
    (S : HodgePrizeSeparatorCore D G C) :
    HodgePrizeSeparationCore D G C :=
  { notAlgebraic := separator_proves_notAlgebraic S }

/-- Final separation payload: the chosen rational (p,p)-class is outside
the rational span of algebraic cycle classes. -/
structure HodgePrizeSeparationPayload
    (D : ClayHodgeData)
    (G : HodgePrizeGeometryPayload D)
    (C : HodgePrizeClassPayload D G) : Prop where
  notAlgebraic :
    ¬ D.isRationalLinearCombinationOfCycleClasses C.h

def separationPayloadFromCore
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryCore D)
    (C : HodgePrizeClassCore D G)
    (S : HodgePrizeSeparationCore D G C) :
    HodgePrizeSeparationPayload D
      (geometryPayloadFromCore G)
      (classPayloadFromCore G C) :=
  { notAlgebraic := S.notAlgebraic }

/-- The three exact payloads assemble mechanically into the single dense
PrizeCounterexampleConstruction expected by the certified refutation lane. -/
def assemblePrizeCounterexample
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryPayload D)
    (C : HodgePrizeClassPayload D G)
    (S : HodgePrizeSeparationPayload D G C) :
    PrizeCounterexampleConstruction D :=
  {
    Xsurgery := G.Xsurgery
    smoothProjective := G.smoothProjective
    constructionName := G.constructionName
    sourceDescription := G.sourceDescription
    gluingDescription := G.gluingDescription
    criticalTransition := G.criticalTransition
    identifiesSurgeryPoint := G.identifiesSurgeryPoint
    certifiedAtCriticalBalance := G.certifiedAtCriticalBalance
    p := C.p
    h := C.h
    rational := C.rational
    typePP := C.typePP
    notAlgebraic := S.notAlgebraic
  }

theorem assembled_prize_yields_counterexample
    {D : ClayHodgeData}
    (G : HodgePrizeGeometryPayload D)
    (C : HodgePrizeClassPayload D G)
    (S : HodgePrizeSeparationPayload D G C) :
    ClayHodgeCounterexample D :=
  prize_construction_yields_clay_counterexample
    (assemblePrizeCounterexample G C S)

end MCore
