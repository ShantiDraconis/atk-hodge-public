import MCore.BackwardAudit.HodgeHabitant
import MCore.K17

namespace MCore.BackwardAudit

/-!
# Concrete partial constructors for the F4 Hodge inhabitant

These are genuine cycle witnesses.  They do not assert the universal Hodge
inhabitant; they construct explicit Z whenever the target class is already
known to be the zero class or a scalar multiple of a concrete cycle class.
-/

/-- The zero cohomology class has an explicit realization: the empty cycle
combination. -/
theorem realize_zeroClass
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat) :
    ∃ Z : CycleCombination G M X p,
      Z.eval M = (M.zeroClass : G.CohomologyQ X (2 * p)) := by
  exact ⟨CycleCombination.empty M X p,
    CycleCombination.eval_empty M X p⟩

/-- Any scalar multiple of an actual cycle class has an explicit realization
by the singleton cycle combination, provided the additive identity law needed
by K17 is supplied. -/
theorem realize_smul_cycleClass
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M)
    {X : G.Variety}
    (p : Nat)
    (a : M.Coeff)
    (z : G.CycleQ X p) :
    ∃ Z : CycleCombination G M X p,
      Z.eval M = M.smul a (M.cycleClass p z) := by
  exact smul_cycleClass_in_concrete_span L p a z

/-- Pointwise constructor: if an admissible Hodge class is identified with the
zero class, the F4 realization is inhabited by the empty combination. -/
theorem realize_hodgeClass_eq_zero
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    (hzero : alpha = M.zeroClass) :
    ∃ Z : CycleCombination G M X p,
      Z.eval M = alpha := by
  subst alpha
  exact realize_zeroClass M X p

/-- Pointwise constructor: if the target class is explicitly a scalar multiple
of a concrete cycle class, the singleton combination is the required F4
inhabitant for that class. -/
theorem realize_hodgeClass_eq_smul_cycleClass
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M)
    {X : G.Variety}
    {p : Nat}
    {alpha : G.CohomologyQ X (2 * p)}
    (a : M.Coeff)
    (z : G.CycleQ X p)
    (hrep : alpha = M.smul a (M.cycleClass p z)) :
    ∃ Z : CycleCombination G M X p,
      Z.eval M = alpha := by
  subst alpha
  exact realize_smul_cycleClass L p a z

#print axioms MCore.BackwardAudit.realize_zeroClass
#print axioms MCore.BackwardAudit.realize_smul_cycleClass
#print axioms MCore.BackwardAudit.realize_hodgeClass_eq_zero
#print axioms MCore.BackwardAudit.realize_hodgeClass_eq_smul_cycleClass

end MCore.BackwardAudit
