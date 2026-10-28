import P05.Hodge.MathlibCycleClassBridge

namespace P05.Hodge

open MCore

/-!
# Cohomology / cycle-class adapter shell

This remains a typed shell only.  The external cycle carrier comes from
`MathlibCycleClassBridge.CycleCarrier`; an inhabitant must still supply the
actual backend and cycle-class realization.
-/

structure MathlibCohomologyCycleClassAdapter
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G)
    (B : MathlibCycleClassBridge G M) where
  Cohomology :
    (X : G.Variety) → Nat → Type
  repoToCohomology :
    ∀ (X : G.Variety) (n : Nat),
      G.CohomologyQ X n → Cohomology X n
  cohomologyToRepo :
    ∀ (X : G.Variety) (n : Nat),
      Cohomology X n → G.CohomologyQ X n
  cohomology_roundtrip :
    ∀ (X : G.Variety) (n : Nat) (α : G.CohomologyQ X n),
      cohomologyToRepo X n (repoToCohomology X n α) = α
  cycleClass :
    ∀ (X : G.Variety) (p : Nat),
      B.CycleCarrier X p → Cohomology X (2 * p)
  cycleClass_compat :
    ∀ (X : G.Variety) (p : Nat) (z : G.CycleQ X p),
      cohomologyToRepo X (2 * p)
        (cycleClass X p (B.cycleToExternal X p z)) =
      M.cycleClass p z

def MathlibCohomologyCycleClassAdapter.realizeRepoCycleClass
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {B : MathlibCycleClassBridge G M}
    (A : MathlibCohomologyCycleClassAdapter G M B)
    {X : G.Variety}
    {p : Nat}
    (z : G.CycleQ X p) :
    G.CohomologyQ X (2 * p) :=
  A.cohomologyToRepo X (2 * p)
    (A.cycleClass X p (B.cycleToExternal X p z))

theorem MathlibCohomologyCycleClassAdapter.realizeRepoCycleClass_eq
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {B : MathlibCycleClassBridge G M}
    (A : MathlibCohomologyCycleClassAdapter G M B)
    {X : G.Variety}
    {p : Nat}
    (z : G.CycleQ X p) :
    A.realizeRepoCycleClass z = M.cycleClass p z :=
  A.cycleClass_compat X p z

def cohomologyAdapterFieldCount : Nat := 6

theorem cohomologyAdapterFieldCount_eq_six :
    cohomologyAdapterFieldCount = 6 := rfl

#print axioms P05.Hodge.MathlibCohomologyCycleClassAdapter.realizeRepoCycleClass_eq
#print axioms P05.Hodge.cohomologyAdapterFieldCount_eq_six

end P05.Hodge
