import MCore.BackwardAudit.HodgeHabitant
import MCore.BackwardAudit.CodimOneLefschetz11

namespace MCore.BackwardAudit

/-!
# HodgeHabitat generic-target falsification

The current abstract `GradedRationalHodgeData` / `CycleSpanMechanics`
interface admits non-geometric models with no algebraic cycles. Therefore a
generic theorem constructing `HodgeHabitant M` for arbitrary `G, M` is
false. This file proves that directly in the kernel.

Consequently, the actual OPEN_MATH attack must instantiate the genuine
complex-projective Hodge model and prove the inhabitant there.
-/

/-- The existing countermodel has no Hodge inhabitant. -/
theorem no_hodgeHabitant_on_counterexample :
    ¬ Nonempty (HodgeHabitant lefschetzCounterexampleM) := by
  rintro ⟨H⟩
  have h :=
    H.realize
      ()
      1
      true
      True.intro
      True.intro
  exact counterexample_true_not_in_concrete_span h

/-- Hence no theorem can produce a Hodge inhabitant uniformly for every
abstract model in the present core. -/
theorem no_generic_hodgeHabitant :
    ¬ (∀ (G : GradedRationalHodgeData)
         (M : CycleSpanMechanics G),
        Nonempty (HodgeHabitant M)) := by
  intro h
  exact no_hodgeHabitant_on_counterexample
    (h lefschetzCounterexampleG lefschetzCounterexampleM)

#print axioms MCore.BackwardAudit.no_hodgeHabitant_on_counterexample
#print axioms MCore.BackwardAudit.no_generic_hodgeHabitant

end MCore.BackwardAudit
