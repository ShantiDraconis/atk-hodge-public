import MCore.BackwardAudit.CodimOneLefschetz11

namespace MCore.BackwardAudit

/-!
# Codimension-one adapter firewall

A semantic Lefschetz (1,1) theorem and a concrete finite-cycle certificate are
not definitionally the same thing.  The K15 CycleSpanAdapter is the bridge.

This module proves that bridge is genuinely additional data by constructing an
abstract model where the semantic span predicate is always true while the
concrete finite-cycle span fails on a nonzero class.

Therefore:
  semantic Lefschetz (1,1) alone
does NOT imply
  Lefschetz11ConcreteLaw
without a CycleSpanAdapter or equivalent semantic identification.
-/

def adapterCounterexampleG : GradedRationalHodgeData :=
  {
    Variety := Unit
    CohomologyQ := fun _ _ => Bool
    CycleQ := fun _ _ => Empty
    isSmoothProjective := fun _ => True
    isTypePP := fun _ _ => True
    inCycleClassSpan := fun _ _ => True
  }

def adapterCounterexampleM :
    CycleSpanMechanics adapterCounterexampleG :=
  {
    Coeff := Bool
    zero := false
    add := Bool.or
    smul := fun r a => r && a
    addClass := Bool.or
    zeroClass := false
    cycleClass := by
      intro X p Z
      exact Empty.elim Z
  }

def adapterCounterexampleSemanticLefschetz11 :
    Lefschetz11SemanticLaw adapterCounterexampleG :=
  {
    algebraic := by
      intro X α hX hα
      trivial
  }

theorem adapter_counterexample_true_not_concrete :
    ¬ InConcreteCycleSpan adapterCounterexampleM
      (X := ()) (p := 1) true := by
  rintro ⟨C, hC⟩
  cases C with
  | mk terms =>
      cases terms with
      | nil =>
          cases hC
      | cons hd tl =>
          rcases hd with ⟨r, Z⟩
          exact Empty.elim Z

/-- The semantic theorem can hold while the concrete theorem fails. -/
theorem semantic_lefschetz11_does_not_force_concrete_without_adapter :
    Lefschetz11SemanticLaw adapterCounterexampleG ∧
    ¬ Lefschetz11ConcreteLaw adapterCounterexampleM := by
  constructor
  · exact adapterCounterexampleSemanticLefschetz11
  · intro L
    have h := L.algebraic () true True.intro True.intro
    exact adapter_counterexample_true_not_concrete h

/-- Hence K15's semantic/concrete span adapter cannot be manufactured from the
raw G and M interfaces. -/
theorem abstract_core_does_not_force_cycle_span_adapter :
    ¬ CycleSpanAdapter adapterCounterexampleG adapterCounterexampleM := by
  intro A
  have hSem :
      adapterCounterexampleG.inCycleClassSpan
        (X := ()) 1 true := True.intro
  have hConcrete :
      InConcreteCycleSpan adapterCounterexampleM
        (X := ()) (p := 1) true :=
    (A.span_iff true).1 hSem
  exact adapter_counterexample_true_not_concrete hConcrete

/-- Exact codimension-one certification package required by the current core:
the classical semantic theorem plus the K15 semantic/concrete adapter. -/
structure CodimOneCertificationInputs
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  spanAdapter : CycleSpanAdapter G M
  lefschetz11 : Lefschetz11SemanticLaw G

def concreteLefschetz11OfCertificationInputs
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (I : CodimOneCertificationInputs M) :
    Lefschetz11ConcreteLaw M :=
  concreteLefschetz11OfSemantic I.spanAdapter I.lefschetz11

theorem codimOne_endpoint_of_certification_inputs
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (I : CodimOneCertificationInputs M)
    (X : G.Variety)
    (α : G.CohomologyQ X (2 * 1))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP 1 α) :
    InConcreteCycleSpan M α :=
  codimOne_concrete_algebraicity
    (concreteLefschetz11OfCertificationInputs I)
    X α hX hα

theorem codimOne_r3_of_certification_inputs
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    (I : CodimOneCertificationInputs M) :
    R3VariationalAlgebraicityPayload M S :=
  r3_variational_codimOne_of_lefschetz11
    (concreteLefschetz11OfCertificationInputs I)

inductive CodimOneAdapterStatus where
  | exactInputsIdentified
  | semanticTheoremExternalClassical
  | concreteSpanAdapterOpen
  | adapterShortcutRejected
  deriving Repr, DecidableEq

structure CodimOneAdapterFrontier where
  certificationInputs : CodimOneAdapterStatus
  semanticLefschetz11 : CodimOneAdapterStatus
  cycleSpanAdapter : CodimOneAdapterStatus
  automaticAdapter : CodimOneAdapterStatus

def codimOneAdapterFrontier : CodimOneAdapterFrontier :=
  {
    certificationInputs := .exactInputsIdentified
    semanticLefschetz11 := .semanticTheoremExternalClassical
    cycleSpanAdapter := .concreteSpanAdapterOpen
    automaticAdapter := .adapterShortcutRejected
  }

theorem codimOne_exact_inputs_identified :
    codimOneAdapterFrontier.certificationInputs =
      .exactInputsIdentified := rfl

theorem codimOne_cycle_span_adapter_open :
    codimOneAdapterFrontier.cycleSpanAdapter =
      .concreteSpanAdapterOpen := rfl

theorem codimOne_automatic_adapter_rejected :
    codimOneAdapterFrontier.automaticAdapter =
      .adapterShortcutRejected := rfl

#print axioms MCore.BackwardAudit.adapterCounterexampleSemanticLefschetz11
#print axioms MCore.BackwardAudit.adapter_counterexample_true_not_concrete
#print axioms MCore.BackwardAudit.semantic_lefschetz11_does_not_force_concrete_without_adapter
#print axioms MCore.BackwardAudit.abstract_core_does_not_force_cycle_span_adapter
#print axioms MCore.BackwardAudit.concreteLefschetz11OfCertificationInputs
#print axioms MCore.BackwardAudit.codimOne_endpoint_of_certification_inputs
#print axioms MCore.BackwardAudit.codimOne_r3_of_certification_inputs
#print axioms MCore.BackwardAudit.codimOne_exact_inputs_identified
#print axioms MCore.BackwardAudit.codimOne_cycle_span_adapter_open
#print axioms MCore.BackwardAudit.codimOne_automatic_adapter_rejected

end MCore.BackwardAudit
