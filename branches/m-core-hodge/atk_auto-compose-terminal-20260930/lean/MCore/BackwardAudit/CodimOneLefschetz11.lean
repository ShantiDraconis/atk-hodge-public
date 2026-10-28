import MCore.BackwardAudit.R3CombinationMinimal
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary

namespace MCore.BackwardAudit

/-!
# Codimension-one classical fragment: Lefschetz (1,1)

For genuine smooth projective complex varieties, the rational Hodge conjecture
in codimension one is the classical Lefschetz (1,1) theorem.

The current MCore geometry is intentionally abstract.  Therefore this file does
NOT assert Lefschetz (1,1) as an axiom.  Instead it:

1. types the exact semantic theorem that a concrete complex-geometry adapter
   must import/prove;
2. proves mechanically that it closes the concrete codimension-one endpoint;
3. proves mechanically that it closes exact R3 in codimension one without
   using algebraicity of the transported fibre;
4. gives a countermodel showing that no such theorem follows from the abstract
   GradedRationalHodgeData interface alone.
-/

/-- Semantic codimension-one Hodge theorem.

For a genuine complex-projective realization this is the content of the
classical Lefschetz (1,1) theorem, stated using the semantic K13 span predicate.
-/
structure Lefschetz11SemanticLaw
    (G : GradedRationalHodgeData) : Prop where
  algebraic :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 1)),
      G.isSmoothProjective X →
      G.isTypePP 1 α →
      G.inCycleClassSpan 1 α

/-- Concrete K15 form of the same codimension-one theorem. -/
structure Lefschetz11ConcreteLaw
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  algebraic :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 1)),
      G.isSmoothProjective X →
      G.isTypePP 1 α →
      InConcreteCycleSpan M α

/-- The already-existing span adapter transports the semantic classical theorem
to the concrete finite-cycle formulation. -/
def concreteLefschetz11OfSemantic
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (L : Lefschetz11SemanticLaw G) :
    Lefschetz11ConcreteLaw M :=
  {
    algebraic := by
      intro X α hX hα
      exact (A.span_iff α).1 (L.algebraic X α hX hα)
  }

/-- Direct codimension-one endpoint: no deformation argument is required. -/
theorem codimOne_concrete_algebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : Lefschetz11ConcreteLaw M)
    (X : G.Variety)
    (α : G.CohomologyQ X (2 * 1))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP 1 α) :
    InConcreteCycleSpan M α :=
  L.algebraic X α hX hα

/-- Exact R3 is automatically satisfied in codimension one from Lefschetz
(1,1), independently of the algebraicity premise on the remote fibre.

This is non-circular with respect to R3: the theorem uses the external
codimension-one Hodge theorem on the ORIGINAL smooth projective X, not the R3
target as an assumption. -/
theorem r3_variational_codimOne_of_lefschetz11
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    (L : Lefschetz11ConcreteLaw M) :
    R3VariationalAlgebraicityPayload M S := by
  intro y γ hy hq hRemote
  exact L.algebraic X α hX hα

theorem r3_contract_codimOne_of_lefschetz11
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    (L : Lefschetz11ConcreteLaw M) :
    Nonempty (R3TransportContract M S) :=
  (r3_contract_iff_variational_algebraicity).2
    (r3_variational_codimOne_of_lefschetz11 L)

/-- If each fibre of the abstract spread is certified smooth projective, the
same classical law also closes R2 at the selected R1d point. -/
structure SmoothProjectiveFamilyLaw
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop where
  smoothProjective :
    ∀ b : S.Base, G.isSmoothProjective (S.Family b)

theorem r2_codimOne_of_lefschetz11
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {α : G.CohomologyQ X (2 * 1)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP 1 α}
    {S : SpreadData G X 1 α hX hα}
    (F : SmoothProjectiveFamilyLaw S)
    (D : R1DescentPointContract S)
    (L : Lefschetz11ConcreteLaw M) :
    R2FiberAlgebraicityTarget M D := by
  exact L.algebraic
    (S.Family D.point.y)
    (S.transportedAlpha D.point.path)
    (F.smoothProjective D.point.y)
    D.point.y_is_hodge

/-!
## Abstract-interface countermodel

This model is intentionally non-geometric.  It proves that the abstract MCore
types alone cannot imply Lefschetz (1,1): a semantic complex-geometry adapter is
genuinely necessary.
-/

def lefschetzCounterexampleG : GradedRationalHodgeData :=
  {
    Variety := Unit
    CohomologyQ := fun _ _ => Bool
    CycleQ := fun _ _ => Empty
    isSmoothProjective := fun _ => True
    isTypePP := fun _ _ => True
    inCycleClassSpan := fun _ _ => False
  }

def lefschetzCounterexampleM :
    CycleSpanMechanics lefschetzCounterexampleG :=
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

theorem counterexample_true_not_in_concrete_span :
    ¬ InConcreteCycleSpan lefschetzCounterexampleM
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

/-- Fail-closed firewall: Lefschetz (1,1) cannot be manufactured from the
generic interfaces. -/
theorem abstract_core_does_not_force_lefschetz11 :
    ¬ Lefschetz11ConcreteLaw lefschetzCounterexampleM := by
  intro L
  have h := L.algebraic () true True.intro True.intro
  exact counterexample_true_not_in_concrete_span h

inductive CodimOneStatus where
  | provedReduction
  | externalClassicalTheorem
  | openSemanticAdapter
  | abstractShortcutRejected
  deriving Repr, DecidableEq

structure CodimOneFrontier where
  lefschetz11Mathematics : CodimOneStatus
  semanticComplexGeometryAdapter : CodimOneStatus
  lefschetz11ToConcreteEndpoint : CodimOneStatus
  lefschetz11ToExactR3 : CodimOneStatus
  genericAbstractDerivation : CodimOneStatus

def codimOneFrontier : CodimOneFrontier :=
  {
    lefschetz11Mathematics := .externalClassicalTheorem
    semanticComplexGeometryAdapter := .openSemanticAdapter
    lefschetz11ToConcreteEndpoint := .provedReduction
    lefschetz11ToExactR3 := .provedReduction
    genericAbstractDerivation := .abstractShortcutRejected
  }

theorem codimOne_r3_reduction_green :
    codimOneFrontier.lefschetz11ToExactR3 = .provedReduction := rfl

theorem codimOne_semantic_adapter_open :
    codimOneFrontier.semanticComplexGeometryAdapter = .openSemanticAdapter := rfl

theorem codimOne_abstract_shortcut_rejected :
    codimOneFrontier.genericAbstractDerivation =
      .abstractShortcutRejected := rfl

#print axioms MCore.BackwardAudit.concreteLefschetz11OfSemantic
#print axioms MCore.BackwardAudit.codimOne_concrete_algebraicity
#print axioms MCore.BackwardAudit.r3_variational_codimOne_of_lefschetz11
#print axioms MCore.BackwardAudit.r3_contract_codimOne_of_lefschetz11
#print axioms MCore.BackwardAudit.r2_codimOne_of_lefschetz11
#print axioms MCore.BackwardAudit.counterexample_true_not_in_concrete_span
#print axioms MCore.BackwardAudit.abstract_core_does_not_force_lefschetz11
#print axioms MCore.BackwardAudit.codimOne_r3_reduction_green
#print axioms MCore.BackwardAudit.codimOne_semantic_adapter_open
#print axioms MCore.BackwardAudit.codimOne_abstract_shortcut_rejected

end MCore.BackwardAudit
