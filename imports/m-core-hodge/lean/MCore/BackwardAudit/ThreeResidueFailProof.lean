import MCore.K18
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary
import MCore.BackwardAudit.R3AtomicSpecialization

namespace MCore.BackwardAudit

/-!
# Three-residue fail-proof closure

This module contains no conjectural theorem and no placeholder.  It states the
three exact residues as explicit input data and proves that supplying them for
every endpoint input yields the already-defined concrete algebraicity payload.
-/

/-- Exact pointwise fail-proof package:
    * the witness D is R1d;
    * fiber algebraicity at D is R2;
    * a direct pathwise specialization backend is R3. -/
def ThreeResiduesAt
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
      Nonempty (DirectPathwiseSpecializationData M S)

/-- The three exact residues close one concrete algebraicity endpoint.  Because
    the target is Prop-valued, Nonempty witnesses can be eliminated without any
    choice axiom. -/
theorem three_residues_at_yield_concrete_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (H : ThreeResiduesAt M X p α hX hα) :
    InConcreteCycleSpan M α := by
  rcases H with ⟨S, D, hR2, ⟨A⟩⟩
  rcases r2_nonempty_of_fiber_algebraicity D hR2 with ⟨R2⟩
  exact r1d_r2_r3_yields_concrete_witness
    D R2 (r3TransportOfAtomicSpecialization A)

/-- Universal fail-proof payload: each endpoint may use its own spread. -/
def AllThreeResidues
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      ThreeResiduesAt M X p α hX hα

/-- This is the formal closure theorem requested by the attack protocol:
    if R1d, R2 and R3 are supplied for every endpoint input, the exact concrete
    algebraicity payload follows. -/
theorem all_three_residues_yield_concrete_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : AllThreeResidues M) :
    ConcreteAlgebraicityPayload M := by
  intro X p α hX hα
  exact three_residues_at_yield_concrete_span (H X p α hX hα)

/-- With the already-certified span adapter, the same three-residue package
    yields the graded rational Hodge statement.  This theorem does not assert
    that the package exists. -/
theorem all_three_residues_yield_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M)
    (H : AllThreeResidues M) :
    GradedRationalHodgeConjecture G :=
  (hodge_iff_concretePayload A).2
    (all_three_residues_yield_concrete_payload H)

inductive FailProofAttackStatus where
  | closureTheoremProved
  | residuesOpen
  deriving Repr, DecidableEq

def failProofClosureStatus : FailProofAttackStatus := .closureTheoremProved
def failProofResiduesStatus : FailProofAttackStatus := .residuesOpen

theorem fail_proof_closure_green :
    failProofClosureStatus = .closureTheoremProved := rfl

theorem fail_proof_residues_open :
    failProofResiduesStatus = .residuesOpen := rfl

#print axioms MCore.BackwardAudit.three_residues_at_yield_concrete_span
#print axioms MCore.BackwardAudit.all_three_residues_yield_concrete_payload
#print axioms MCore.BackwardAudit.all_three_residues_yield_hodge
#print axioms MCore.BackwardAudit.fail_proof_closure_green
#print axioms MCore.BackwardAudit.fail_proof_residues_open

end MCore.BackwardAudit
