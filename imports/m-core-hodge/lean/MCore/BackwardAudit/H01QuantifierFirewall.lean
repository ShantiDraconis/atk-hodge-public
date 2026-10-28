import MCore.K0

namespace MCore.HodgeQuantifierFirewall

/-!
H01 quantifier firewall.

The Hodge endpoint has pointwise dependency order
  forall input, exists geometric data.
This file gives a kernel-checked countermodel showing that this may not be
replaced by one uniform existential witness outside the universal quantifier.

It is a logical firewall only; it proves no Hodge class algebraic.
-/

def Match (x s : Bool) : Prop := x = s

theorem pointwise_witness_exists :
    ∀ x : Bool, ∃ s : Bool, Match x s := by
  intro x
  exact ⟨x, rfl⟩

theorem no_uniform_witness :
    ¬ ∃ s : Bool, ∀ x : Bool, Match x s := by
  rintro ⟨s, hs⟩
  cases s with
  | false =>
      have h := hs true
      simp [Match] at h
  | true =>
      have h := hs false
      simp [Match] at h

theorem pointwise_does_not_imply_uniform :
    ¬ ((∀ x : Bool, ∃ s : Bool, Match x s) →
       (∃ s : Bool, ∀ x : Bool, Match x s)) := by
  intro h
  exact no_uniform_witness (h pointwise_witness_exists)

#print axioms MCore.HodgeQuantifierFirewall.pointwise_witness_exists
#print axioms MCore.HodgeQuantifierFirewall.no_uniform_witness
#print axioms MCore.HodgeQuantifierFirewall.pointwise_does_not_imply_uniform

end MCore.HodgeQuantifierFirewall
