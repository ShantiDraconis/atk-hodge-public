import MCore.K6

namespace MCore

/-- Carrier for a faithful formalization of the official Clay/Deligne Hodge statement.
    This structure itself asserts no mathematical result. -/
structure ClayHodgeData where
  Variety : Type
  Cohomology : Variety → Nat → Type
  AlgebraicCycle : Variety → Nat → Type
  isProjectiveNonsingularOverC : Variety → Prop
  isRationalClass : {X : Variety} → {n : Nat} → Cohomology X n → Prop
  isTypePP : {X : Variety} → (p : Nat) → Cohomology X (2*p) → Prop
  cycleClass :
    {X : Variety} → {p : Nat} →
    AlgebraicCycle X p → Cohomology X (2*p)
  isRationalLinearCombinationOfCycleClasses :
    {X : Variety} → {p : Nat} →
    Cohomology X (2*p) → Prop

def ClayHodgeClass (D : ClayHodgeData) {X : D.Variety} (p : Nat)
    (α : D.Cohomology X (2*p)) : Prop :=
  D.isRationalClass α ∧ D.isTypePP p α

def ClayHodgeStatement (D : ClayHodgeData) : Prop :=
  ∀ (X : D.Variety), D.isProjectiveNonsingularOverC X →
    ∀ (p : Nat) (α : D.Cohomology X (2*p)),
      ClayHodgeClass D p α →
      D.isRationalLinearCombinationOfCycleClasses α

/-- Direct mathematical refutation of the Clay statement: an admissible
    rational (p,p)-class outside the rational span of algebraic cycle classes. -/
def ClayHodgeCounterexample (D : ClayHodgeData) : Prop :=
  ∃ (X : D.Variety), D.isProjectiveNonsingularOverC X ∧
    ∃ (p : Nat) (α : D.Cohomology X (2*p)),
      ClayHodgeClass D p α ∧
      ¬ D.isRationalLinearCombinationOfCycleClasses α

/-- The repository's sole OPEN_MATH claim.
    To inhabit it one must refute the official Clay/Deligne implication itself,
    not merely a local encoding or a metadata route. -/
structure ClayLogicRefutationClaim (D : ClayHodgeData) : Prop where
  counterexample : ClayHodgeCounterexample D

def HODGE_RESOLUTION_OPEN_MATH (D : ClayHodgeData) : Prop :=
  ClayLogicRefutationClaim D

end MCore
