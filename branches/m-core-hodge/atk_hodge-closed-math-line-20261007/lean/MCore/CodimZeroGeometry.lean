import MCore.HodgeMaterialInhabitant
import MCore.K17

namespace MCore

/-!
# Codimension-zero geometric producer

The abstract K13/K15 interfaces do not contain connected components or
fundamental codimension-zero cycles.  This module adds exactly that missing
geometric realization layer.

No Hodge proposition is assumed.  The backend gives concrete finite component
data and an equality reconstructing the degree-zero cohomology class.
-/

/-- One explicit connected-component contribution to a codimension-zero class.

The repository deliberately keeps the abstract geometry independent of any
particular component implementation, so a concrete model supplies the component
cycle and its coefficient directly. -/
structure CodimZeroComponentTerm
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety) where
  coefficient : M.Coeff
  cycle : G.CycleQ X 0

/-- Finite component decomposition for one class. -/
structure CodimZeroClassDecomposition
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (α : G.CohomologyQ X (2 * 0)) where
  components : List (CodimZeroComponentTerm M X)
  reconstruct :
    (components.map (fun t => (t.coefficient, t.cycle)) :
      List (M.Coeff × G.CycleQ X 0)).foldr
        (fun t acc =>
          M.addClass (M.smul t.1 (M.cycleClass 0 t.2)) acc)
        M.zeroClass = α

/-- Geometric p=0 backend.

A genuine complex-projective adapter should implement this from the finitely
many connected components of X and their codimension-zero fundamental cycles.
The backend does not mention the Hodge conjecture or a cycle-span proposition. -/
structure CodimZeroComponentBackend
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  decompose :
    ∀ (X : G.Variety)
      (α : G.CohomologyQ X (2 * 0))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP 0 α),
      CodimZeroClassDecomposition M X α

/-- Convert the geometric component backend into the previously kernel-checked
Type-valued producer. -/
def CodimZeroComponentBackend.toCycleProducer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : CodimZeroComponentBackend G M) :
    CodimZeroCycleProducer G M :=
  {
    combination := by
      intro X α hX hα
      let D := B.decompose X α hX hα
      exact ⟨D.components.map (fun t => (t.coefficient, t.cycle))⟩
    realizes := by
      intro X α hX hα
      let D := B.decompose X α hX hα
      change
        (D.components.map (fun t => (t.coefficient, t.cycle))).foldr
          (fun t acc =>
            M.addClass (M.smul t.1 (M.cycleClass 0 t.2)) acc)
          M.zeroClass = α
      exact D.reconstruct
  }

/-- Hence an actual component backend closes the entire codimension-zero slice. -/
theorem codimZeroPayload_of_componentBackend
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : CodimZeroComponentBackend G M) :
    CodimZeroConcretePayload M :=
  codimZeroCycleProducer_closes B.toCycleProducer

/-!
## Fail-closed abstract-interface firewall

This model proves that no generic theorem can derive the codimension-zero
producer from `GradedRationalHodgeData` and `CycleSpanMechanics` alone.
-/

def codimZeroCounterexampleG : GradedRationalHodgeData :=
  {
    Variety := Unit
    CohomologyQ := fun _ _ => Bool
    CycleQ := fun _ _ => Empty
    isSmoothProjective := fun _ => True
    isTypePP := fun _ _ => True
    inCycleClassSpan := fun _ _ => False
  }

def codimZeroCounterexampleM :
    CycleSpanMechanics codimZeroCounterexampleG :=
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

theorem codimZero_true_not_in_concrete_span :
    ¬ InConcreteCycleSpan codimZeroCounterexampleM
      (X := ()) (p := 0) true := by
  rintro ⟨C, hC⟩
  cases C with
  | mk terms =>
      cases terms with
      | nil =>
          cases hC
      | cons hd tl =>
          rcases hd with ⟨r, Z⟩
          exact Empty.elim Z

theorem abstract_core_does_not_force_codimZeroPayload :
    ¬ CodimZeroConcretePayload codimZeroCounterexampleM := by
  intro H
  exact codimZero_true_not_in_concrete_span
    (H () true True.intro True.intro)

theorem abstract_core_does_not_force_codimZeroProducer :
    ¬ Nonempty
      (CodimZeroCycleProducer codimZeroCounterexampleG
        codimZeroCounterexampleM) := by
  rintro ⟨P⟩
  exact abstract_core_does_not_force_codimZeroPayload
    (codimZeroCycleProducer_closes P)

#print axioms MCore.CodimZeroComponentBackend.toCycleProducer
#print axioms MCore.codimZeroPayload_of_componentBackend
#print axioms MCore.codimZero_true_not_in_concrete_span
#print axioms MCore.abstract_core_does_not_force_codimZeroPayload
#print axioms MCore.abstract_core_does_not_force_codimZeroProducer

end MCore
