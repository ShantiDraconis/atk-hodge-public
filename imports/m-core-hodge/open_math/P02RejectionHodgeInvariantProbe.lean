import MCore.Real.P02DeterministicRejectionHodge

namespace MCore.Hodge

open HodgeRejectionSystem

/--
Q1-Q6 bundle: exactly the symmetry data that survives the corrected Hodge
translation. It intentionally contains no algebraicity/zero-defect premise.
-/
structure HodgeInvariantProbe (M : HodgeRejectionSystem) : Prop where
  q1_reflection_closure : ∀ x : M.Point, ∃ y : M.Point, y = M.reflect x
  q2_involution : ∀ x : M.Point, M.reflect (M.reflect x) = x
  q3_defect_symmetry : ∀ x : M.Point, M.defect (M.reflect x) = M.defect x
  q4_magnitude_preservation :
    ∀ x : M.Point, Int.natAbs (M.defect (M.reflect x)) = Int.natAbs (M.defect x)
  q5_orbit_size_control : ∀ x : M.Point, M.reflect x = x ∨ M.reflect x ≠ x
  q6_no_growth : ∀ x : M.Point, M.defect (M.reflect (M.reflect x)) = M.defect x

def toyProbe : HodgeInvariantProbe toyTranscendental where
  q1_reflection_closure := by
    intro x
    exact ⟨toyTranscendental.reflect x, rfl⟩
  q2_involution := toyTranscendental.reflect_reflect
  q3_defect_symmetry := toyTranscendental.defect_reflect
  q4_magnitude_preservation := by
    intro x
    exact congrArg Int.natAbs (toyTranscendental.defect_reflect x)
  q5_orbit_size_control := by
    intro x
    by_cases h : toyTranscendental.reflect x = x
    · exact Or.inl h
    · exact Or.inr h
  q6_no_growth := by
    intro x
    rw [toyTranscendental.reflect_reflect]

/-- Q7: forbidden promotion. Q1-Q6 do not imply HodgeProperty. -/
theorem q7_forbidden_promotion :
    HodgeInvariantProbe toyTranscendental ∧ ¬ HodgeProperty toyTranscendental := by
  exact ⟨toyProbe, corrected_symmetry_does_not_force_hodgeProperty⟩

/-- Q8: involution alone does not imply orbit collapse. -/
theorem q8_involution_not_orbitCollapse :
    ¬ OrbitCollapse toyTranscendental := by
  intro h
  have h1 : false = true := by
    exact h true
  contradiction

/-- Q9: even orbit collapse does not imply defect collapse. -/
theorem q9_orbitCollapse_not_defectCollapse :
    OrbitCollapse toyFixedOrbitNonzeroDefect ∧
      ¬ DefectCollapse toyFixedOrbitNonzeroDefect :=
  orbitCollapse_does_not_force_defectCollapse

/--
Q10 / DIAGONAL-OBSTRUCTION:
any genuine closure principle must rule out the explicit nonzero-defect model.
This theorem records the exact semantic min-cut without pretending to supply
the missing geometric theorem.
-/
def RulesOutTranscendentalToy
    (P : HodgeRejectionSystem → Prop) : Prop :=
  ¬ P toyTranscendental

def ForcesDefectCollapse
    (P : HodgeRejectionSystem → Prop) : Prop :=
  ∀ M, P M → DefectCollapse M

theorem q10_any_defect_collapse_rule_excludes_toy
    (P : HodgeRejectionSystem → Prop)
    (hP : ForcesDefectCollapse P) :
    RulesOutTranscendentalToy P := by
  intro hToy
  have hCollapse := hP toyTranscendental hToy
  have h1 : (1 : Int) = 0 := by
    exact hCollapse true
  have hne : (1 : Int) ≠ 0 := by decide
  exact hne h1

/--
Conversely, merely being compatible with Q1-Q6 cannot count as a terminal
producer, because the toy model already satisfies all six invariants.
-/
theorem q10_invariants_are_not_terminal :
    HodgeInvariantProbe toyTranscendental ∧
      ¬ DefectCollapse toyTranscendental := by
  constructor
  · exact toyProbe
  · intro h
    have h1 : (1 : Int) = 0 := by
      exact h true
    have hne : (1 : Int) ≠ 0 := by decide
    exact hne h1

end MCore.Hodge
