import MCore.BackwardAudit.ThreeResidueFailProofExact
import MCore.BackwardAudit.R2HardCore

namespace MCore.BackwardAudit

/-!
# Exact three-residue equivalence firewall

Because the spread is existentially chosen, the constant Qbar spread is always
available at the abstract interface level.  On that spread:

* R1d is trivial at the basepoint;
* R2 is exactly the original concrete algebraicity endpoint;
* exact R3 can return the already-known algebraicity of alpha.

Hence the exact three-residue package is globally equivalent to the concrete
algebraicity payload.  This prevents interpreting the decomposition as a
reduction to three strictly easier independent problems.
-/

/-- Concrete algebraicity immediately supplies the exact three residues by
choosing the constant Qbar spread. -/
theorem concrete_payload_yields_all_exact_three_residues
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : ConcreteAlgebraicityPayload M) :
    AllExactThreeResidues M := by
  intro X p α hX hα
  let S := trivialSpreadQbar G X p α hX hα
  let D : R1DescentPointContract S :=
    trivialQbarDescent
      (G := G) (X := X) (p := p)
      (α := α) (hX := hX) (hα := hα)
  have hR2 : R2FiberAlgebraicityTarget M D := by
    exact (r2_trivial_qbar_iff_original_span).2
      (H X p α hX hα)
  have hR3 : R3VariationalAlgebraicityPayload M S := by
    intro y γ hy hq hAlg
    exact H X p α hX hα
  exact ⟨S, D, hR2, hR3⟩

/-- Exact theorem: the universal exact three-residue package is neither weaker
nor stronger than the concrete algebraicity payload. -/
theorem all_exact_three_residues_iff_concrete_payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    AllExactThreeResidues M ↔
      ConcreteAlgebraicityPayload M := by
  constructor
  · exact all_exact_three_residues_yield_concrete_payload
  · exact concrete_payload_yields_all_exact_three_residues

/-- With the existing semantic span adapter, the same package is exactly
equivalent to the graded rational Hodge statement. -/
theorem all_exact_three_residues_iff_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (A : CycleSpanAdapter G M) :
    AllExactThreeResidues M ↔
      GradedRationalHodgeConjecture G :=
  (all_exact_three_residues_iff_concrete_payload M).trans
    (hodge_iff_concretePayload A).symm

inductive ThreeResidueEquivalenceStatus where
  | exactRepackaging
  | strongBackendOnly
  | noDifficultyReductionCertified
  deriving Repr, DecidableEq

structure ThreeResidueEquivalenceFrontier where
  exactPackage : ThreeResidueEquivalenceStatus
  oldAtomwisePackage : ThreeResidueEquivalenceStatus
  difficultyClaim : ThreeResidueEquivalenceStatus

def threeResidueEquivalenceFrontier : ThreeResidueEquivalenceFrontier :=
  {
    exactPackage := .exactRepackaging
    oldAtomwisePackage := .strongBackendOnly
    difficultyClaim := .noDifficultyReductionCertified
  }

theorem exact_three_residue_package_is_repackaging :
    threeResidueEquivalenceFrontier.exactPackage =
      .exactRepackaging := rfl

theorem old_atomwise_package_is_only_strong_backend :
    threeResidueEquivalenceFrontier.oldAtomwisePackage =
      .strongBackendOnly := rfl

theorem no_difficulty_reduction_certified :
    threeResidueEquivalenceFrontier.difficultyClaim =
      .noDifficultyReductionCertified := rfl

#print axioms MCore.BackwardAudit.concrete_payload_yields_all_exact_three_residues
#print axioms MCore.BackwardAudit.all_exact_three_residues_iff_concrete_payload
#print axioms MCore.BackwardAudit.all_exact_three_residues_iff_hodge
#print axioms MCore.BackwardAudit.exact_three_residue_package_is_repackaging
#print axioms MCore.BackwardAudit.old_atomwise_package_is_only_strong_backend
#print axioms MCore.BackwardAudit.no_difficulty_reduction_certified

end MCore.BackwardAudit
