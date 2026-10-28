import MCore.BackwardAudit.ThreeResidueFailProof
import MCore.BackwardAudit.R3CombinationMinimal

namespace MCore.BackwardAudit

/-!
# Exact three-residue fail-proof closure

The original ThreeResidueFailProof used DirectPathwiseSpecializationData as R3.
That backend is sufficient but stronger than the original R3TransportContract.

This module replaces it with the exact equivalent R3 variational-algebraicity
payload proved in R3CombinationMinimal.
-/

/-- Exact pointwise package:
    R1d = Qbar Hodge point;
    R2 = algebraicity of the transported class at that point;
    R3 = exact variational algebraicity transport back to the original class.
-/
def ExactThreeResiduesAt
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) : Prop :=
  ∃ S : SpreadData G X p α hX hα,
    ∃ D : R1DescentPointContract S,
      R2FiberAlgebraicityTarget M D ∧
      R3VariationalAlgebraicityPayload M S

/-- The exact three residues close one concrete algebraicity endpoint. -/
theorem exact_three_residues_at_yield_concrete_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (H : ExactThreeResiduesAt M X p α hX hα) :
    InConcreteCycleSpan M α := by
  rcases H with ⟨S, D, hR2, hR3⟩
  rcases r2_nonempty_of_fiber_algebraicity D hR2 with ⟨R2⟩
  let R3 : R3TransportContract M S :=
    r3ContractOfCombinationPayload
      (combination_payload_iff_variational_algebraicity.mpr hR3)
  exact r1d_r2_r3_yields_concrete_witness D R2 R3

def AllExactThreeResidues
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      ExactThreeResiduesAt M X p α hX hα

theorem all_exact_three_residues_yield_concrete_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : AllExactThreeResidues M) :
    ConcreteAlgebraicityPayload M := by
  intro X p α hX hα
  exact exact_three_residues_at_yield_concrete_span
    (H X p α hX hα)

theorem all_exact_three_residues_yield_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : AllExactThreeResidues M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload A).2
    (all_exact_three_residues_yield_concrete_payload H)

/-- The old atomwise three-residue package implies the exact package.  This is
the certified direction: old R3 was a sufficient strengthening. -/
theorem three_residues_at_implies_exact
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (H : ThreeResiduesAt M X p α hX hα) :
    ExactThreeResiduesAt M X p α hX hα := by
  rcases H with ⟨S, D, hR2, ⟨A⟩⟩
  exact ⟨S, D, hR2,
    variational_payload_of_atomic_specialization A⟩

theorem all_three_residues_imply_all_exact
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : AllThreeResidues M) :
    AllExactThreeResidues M := by
  intro X p α hX hα
  exact three_residues_at_implies_exact
    (H X p α hX hα)

inductive ExactFailProofStatus where
  | exactClosureTheoremProved
  | oldR3CertifiedAsStrongBackend
  | r1dOpen
  | r2Open
  | r3VariationalOpen
  deriving Repr, DecidableEq

structure ExactFailProofFrontier where
  closure : ExactFailProofStatus
  oldAtomwiseR3 : ExactFailProofStatus
  r1d : ExactFailProofStatus
  r2 : ExactFailProofStatus
  r3 : ExactFailProofStatus

def exactFailProofFrontier : ExactFailProofFrontier :=
  {
    closure := .exactClosureTheoremProved
    oldAtomwiseR3 := .oldR3CertifiedAsStrongBackend
    r1d := .r1dOpen
    r2 := .r2Open
    r3 := .r3VariationalOpen
  }

theorem exact_fail_proof_closure_green :
    exactFailProofFrontier.closure =
      .exactClosureTheoremProved := rfl

theorem old_atomwise_r3_is_strong_backend :
    exactFailProofFrontier.oldAtomwiseR3 =
      .oldR3CertifiedAsStrongBackend := rfl

theorem exact_r3_variational_still_open :
    exactFailProofFrontier.r3 =
      .r3VariationalOpen := rfl

#print axioms MCore.BackwardAudit.exact_three_residues_at_yield_concrete_span
#print axioms MCore.BackwardAudit.all_exact_three_residues_yield_concrete_payload
#print axioms MCore.BackwardAudit.all_exact_three_residues_yield_hodge
#print axioms MCore.BackwardAudit.three_residues_at_implies_exact
#print axioms MCore.BackwardAudit.all_three_residues_imply_all_exact
#print axioms MCore.BackwardAudit.exact_fail_proof_closure_green
#print axioms MCore.BackwardAudit.old_atomwise_r3_is_strong_backend
#print axioms MCore.BackwardAudit.exact_r3_variational_still_open

end MCore.BackwardAudit
