import MCore.BackwardAudit.R3Contract

namespace MCore.BackwardAudit

/-!
# R3 atomic specialization

A cast-free reduction of R3 to elementary geometric laws.  Specialization is
taken directly from a selected fiber back to the original variety X, so no
hidden compatibility with dependent equality casts is required.
-/

structure DirectPathwiseSpecializationData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where

  specializeClass :
    {y : S.Base} →
    (γ : S.Path S.basepoint y) →
    G.CohomologyQ (S.Family y) (2 * p) →
    G.CohomologyQ X (2 * p)

  specializeCycle :
    {y : S.Base} →
    (γ : S.Path S.basepoint y) →
    G.CycleQ (S.Family y) p →
    G.CycleQ X p

  zero_compat :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y),
      specializeClass γ (M.zeroClass (X := S.Family y) (p := p)) =
        M.zeroClass

  add_compat :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y)
      (a b : G.CohomologyQ (S.Family y) (2 * p)),
      specializeClass γ (M.addClass a b) =
        M.addClass (specializeClass γ a) (specializeClass γ b)

  smul_compat :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y)
      (r : M.Coeff)
      (a : G.CohomologyQ (S.Family y) (2 * p)),
      specializeClass γ (M.smul r a) =
        M.smul r (specializeClass γ a)

  cycleClass_compat :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y)
      (Z : G.CycleQ (S.Family y) p),
      specializeClass γ (M.cycleClass p Z) =
        M.cycleClass p (specializeCycle γ Z)

  transportedAlpha_compat :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y),
      specializeClass γ (S.transportedAlpha γ) = α

def DirectPathwiseSpecializationData.specializeTerms
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S)
    {y : S.Base}
    (γ : S.Path S.basepoint y) :
    List (M.Coeff × G.CycleQ (S.Family y) p) →
      List (M.Coeff × G.CycleQ X p) :=
  List.map (fun t => (t.1, A.specializeCycle γ t.2))

def DirectPathwiseSpecializationData.specializeCombination
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S)
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (C : CycleCombination G M (S.Family y) p) :
    CycleCombination G M X p :=
  { terms := A.specializeTerms γ C.terms }

theorem specializeTerms_eval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S)
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (terms : List (M.Coeff × G.CycleQ (S.Family y) p)) :
    (CycleCombination.mk (A.specializeTerms γ terms)).eval M =
      A.specializeClass γ (CycleCombination.mk terms |>.eval M) := by
  induction terms with
  | nil =>
      simpa [DirectPathwiseSpecializationData.specializeTerms,
        CycleCombination.eval] using (A.zero_compat γ).symm
  | cons t ts ih =>
      rcases t with ⟨r, Z⟩
      change
        M.addClass
          (M.smul r (M.cycleClass p (A.specializeCycle γ Z)))
          ((CycleCombination.mk (A.specializeTerms γ ts)).eval M) =
        A.specializeClass γ
          (M.addClass
            (M.smul r (M.cycleClass p Z))
            ((CycleCombination.mk ts).eval M))
      rw [A.add_compat, A.smul_compat, A.cycleClass_compat, ih]

theorem specializeCombination_eval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S)
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (C : CycleCombination G M (S.Family y) p) :
    (A.specializeCombination γ C).eval M =
      A.specializeClass γ (C.eval M) := by
  cases C with
  | mk terms =>
      exact specializeTerms_eval A γ terms

/-- The five atomic laws are sufficient for the exact R3 contract. -/
def r3TransportOfAtomicSpecialization
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S) :
    R3TransportContract M S :=
  {
    transport := by
      intro P
      refine ⟨A.specializeCombination P.path P.combination, ?_⟩
      rw [specializeCombination_eval A P.path P.combination,
        P.combination_class, A.transportedAlpha_compat P.path]
  }

/-- Hence a concrete implementation of the atomic laws closes R3 without any
    further logical or finite-combination residue. -/
theorem r3_transport_of_atomic_specialization
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S) :
    Nonempty (R3TransportContract M S) :=
  ⟨r3TransportOfAtomicSpecialization A⟩

inductive R3AtomicResidueStatus where
  | provedLift
  | externalConstruction
  | externalCompatibility
  deriving Repr, DecidableEq

structure R3AtomicFrontier where
  finiteCombinationLift : R3AtomicResidueStatus
  cohomologySpecialization : R3AtomicResidueStatus
  cycleSpecialization : R3AtomicResidueStatus
  linearityLaws : R3AtomicResidueStatus
  cycleClassCompatibility : R3AtomicResidueStatus
  transportedClassRecovery : R3AtomicResidueStatus

def r3AtomicFrontier : R3AtomicFrontier :=
  {
    finiteCombinationLift := .provedLift
    cohomologySpecialization := .externalConstruction
    cycleSpecialization := .externalConstruction
    linearityLaws := .externalCompatibility
    cycleClassCompatibility := .externalCompatibility
    transportedClassRecovery := .externalCompatibility
  }

theorem r3_finite_combination_lift_proved :
    r3AtomicFrontier.finiteCombinationLift = .provedLift := rfl

#print axioms MCore.BackwardAudit.specializeTerms_eval
#print axioms MCore.BackwardAudit.specializeCombination_eval
#print axioms MCore.BackwardAudit.r3TransportOfAtomicSpecialization
#print axioms MCore.BackwardAudit.r3_transport_of_atomic_specialization
#print axioms MCore.BackwardAudit.r3_finite_combination_lift_proved

end MCore.BackwardAudit
