import MCore.BackwardAudit.HodgeUnconditionalCertificate

namespace MCore.BackwardAudit

/-!
# Hodge F4 inhabitant

The unique mathematical inhabitant for the positive Hodge route is an explicit
realization function: every rational Hodge class on every smooth projective
object is hit by a finite algebraic-cycle combination.

No decomposition, adapter, status flag, or theorem name inhabits this object.
Only concrete realization data does.
-/

/-- F4 REALIZATION inhabitant: for every admissible Hodge class alpha,
produce an explicit finite algebraic-cycle combination whose evaluated cycle
class is exactly alpha. -/
structure HodgeHabitant
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Type 1 where
  realize :
    ∀ (X : G.Variety)
      (p : Nat)
      (alpha : G.CohomologyQ X (2 * p)),
      G.isSmoothProjective X →
      G.isTypePP p alpha →
      ∃ Z : CycleCombination G M X p,
        Z.eval M = alpha

/-- A genuine F4 inhabitant is exactly sufficient to build the universal
concrete algebraicity payload. -/
theorem concretePayload_of_habitant
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeHabitant M) :
    MCore.ConcreteAlgebraicityPayload M := by
  intro X p alpha hX hAlpha
  exact H.realize X p alpha hX hAlpha

/-- Conversely, the existing concrete payload contains exactly the same
realization data. This proves that HodgeHabitant is not a weaker wrapper. -/
def habitant_of_concretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h : MCore.ConcreteAlgebraicityPayload M) :
    HodgeHabitant M :=
  {
    realize := by
      intro X p alpha hX hAlpha
      exact h X p alpha hX hAlpha
  }

/-- Exact equivalence between existence of the F4 inhabitant and the existing
OPEN_MATH material producer. -/
theorem nonempty_hodgeHabitant_iff_concretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G} :
    Nonempty (HodgeHabitant M) ↔
      MCore.ConcreteAlgebraicityPayload M := by
  constructor
  · rintro ⟨H⟩
    exact concretePayload_of_habitant H
  · intro h
    exact ⟨habitant_of_concretePayload h⟩

/-- The inhabitant creates the exact unconditional terminal certificate once
the already-certified boundary is supplied. -/
def unconditionalCertificateOfHabitant
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (H : HodgeHabitant M) :
    UnconditionalHodgeCertificate G M :=
  {
    boundary := B
    algebraicity := concretePayload_of_habitant H
  }

/-- Final theorem activation from the unique positive mathematical inhabitant. -/
theorem hodge_of_habitant
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (H : HodgeHabitant M) :
    GradedRationalHodgeConjecture G :=
  unconditional_hodge_claim (unconditionalCertificateOfHabitant B H)

/-- F4 label for the unique remaining material producer. -/
def hodgeHabitantStatus : String :=
  "OPEN_MATH_CORE: construct HodgeHabitant.realize for every rational Hodge class"

#print axioms MCore.BackwardAudit.concretePayload_of_habitant
#print axioms MCore.BackwardAudit.habitant_of_concretePayload
#print axioms MCore.BackwardAudit.nonempty_hodgeHabitant_iff_concretePayload
#print axioms MCore.BackwardAudit.unconditionalCertificateOfHabitant
#print axioms MCore.BackwardAudit.hodge_of_habitant

end MCore.BackwardAudit
