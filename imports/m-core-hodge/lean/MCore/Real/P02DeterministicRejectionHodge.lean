import MCore.Hodge

namespace MCore.Hodge

/--
Kernel-level rejection/symmetry probe for Hodge.
The toy carrier is deliberately finite and dependency-free: it tests only the
logical implication "involution + invariant defect ⇒ collapse", not geometry.
-/
structure HodgeRejectionSystem where
  Point : Type
  reflect : Point → Point
  defect : Point → Int
  reflect_reflect : ∀ x, reflect (reflect x) = x
  defect_reflect : ∀ x, defect (reflect x) = defect x

namespace HodgeRejectionSystem

def HodgeProperty (M : HodgeRejectionSystem) : Prop :=
  ∀ x : M.Point, M.defect x = 0

def OrbitCollapse (M : HodgeRejectionSystem) : Prop :=
  ∀ x : M.Point, M.reflect x = x

def DefectCollapse (M : HodgeRejectionSystem) : Prop :=
  ∀ x : M.Point, M.defect x = 0

theorem defectCollapse_iff_hodgeProperty (M : HodgeRejectionSystem) :
    DefectCollapse M ↔ HodgeProperty M := by
  rfl

/--
Negative control: a genuine 2-cycle with invariant nonzero defect.
This is the abstract {a,-a} obstruction stripped of all unnecessary analysis.
-/
def toyTranscendental : HodgeRejectionSystem where
  Point := Bool
  reflect := Bool.not
  defect := fun _ => 1
  reflect_reflect := by
    intro x
    cases x <;> rfl
  defect_reflect := by
    intro x
    rfl

theorem involution_does_not_force_defect_collapse :
    ∃ (M : HodgeRejectionSystem) (x : M.Point), M.defect x ≠ 0 := by
  refine ⟨toyTranscendental, true, ?_⟩
  decide

theorem corrected_symmetry_does_not_force_hodgeProperty :
    ¬ HodgeProperty toyTranscendental := by
  intro h
  have h1 : (1 : Int) = 0 := by
    exact h true
  have hne : (1 : Int) ≠ 0 := by decide
  exact hne h1

/--
Stronger negative control: even literal fixed-point collapse of every orbit
does not imply zero defect.
-/
def toyFixedOrbitNonzeroDefect : HodgeRejectionSystem where
  Point := Bool
  reflect := id
  defect := fun _ => 1
  reflect_reflect := by
    intro x
    rfl
  defect_reflect := by
    intro x
    rfl

theorem toyFixedOrbit_orbitCollapse :
    OrbitCollapse toyFixedOrbitNonzeroDefect := by
  intro x
  rfl

theorem orbitCollapse_does_not_force_defectCollapse :
    OrbitCollapse toyFixedOrbitNonzeroDefect ∧
      ¬ DefectCollapse toyFixedOrbitNonzeroDefect := by
  constructor
  · exact toyFixedOrbit_orbitCollapse
  · intro h
    have h1 : (1 : Int) = 0 := by
      exact h true
    have hne : (1 : Int) ≠ 0 := by decide
    exact hne h1

/--
Firewall replacing the false P≠NP-shaped idempotence rule.
For an involution, imposing idempotence collapses reflection to the identity.
-/
theorem involutive_and_idempotent_forces_fixed
    (M : HodgeRejectionSystem)
    (hIdem : ∀ x, M.reflect (M.reflect x) = M.reflect x) :
    ∀ x, M.reflect x = x := by
  intro x
  calc
    M.reflect x = M.reflect (M.reflect x) := by
      symm
      exact hIdem x
    _ = x := M.reflect_reflect x

end HodgeRejectionSystem

end MCore.Hodge
