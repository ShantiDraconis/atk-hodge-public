import MCore.BackwardAudit.R3AtomicSpecialization

namespace MCore.BackwardAudit

/-!
# R3 exact combination-level cut

The original R3 contract consumes an AlgebraicPointData whose algebraic witness
is already a finite CycleCombination.  Therefore atomwise specialization of
every cycle term is only one sufficient implementation strategy; it is not the
minimal logical residue.

This module identifies the exact combination-level payload and proves it
equivalent to existence of the original R3TransportContract.
-/

/-- Exact witness-level R3 payload, stated directly on finite combinations.

Given the same data that can form an AlgebraicPointData, any algebraic
combination representing the transported class must yield some algebraic
combination representing the original class. -/
def R3CombinationPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∀ (y : S.Base)
    (γ : S.Path S.basepoint y)
    (hy : S.isHodgeAlong γ)
    (hq : S.fieldOfDefinition.isDefinedOverQbar y)
    (C : CycleCombination G M (S.Family y) p),
      C.eval M = S.transportedAlpha γ →
      ∃ C0 : CycleCombination G M X p,
        C0.eval M = α

/-- A transport contract gives the exact combination payload. -/
theorem r3_contract_implies_combination_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R3 : R3TransportContract M S) :
    R3CombinationPayload M S := by
  intro y γ hy hq C hC
  exact R3.transport
    {
      y := y
      path := γ
      y_is_hodge := hy
      y_is_defined_over_Qbar := hq
      combination := C
      combination_class := hC
    }

/-- Conversely, the exact combination payload constructs the original R3
transport contract with no additional geometric or logical input. -/
def r3ContractOfCombinationPayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (H : R3CombinationPayload M S) :
    R3TransportContract M S :=
  {
    transport := by
      intro P
      exact H
        P.y P.path
        P.y_is_hodge
        P.y_is_defined_over_Qbar
        P.combination
        P.combination_class
  }

/-- Kernel-checked exact equivalence: there is no hidden R3 theorem between the
combination payload and the original R3 contract. -/
theorem r3_contract_iff_combination_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα} :
    Nonempty (R3TransportContract M S) ↔
      R3CombinationPayload M S := by
  constructor
  · intro h
    rcases h with ⟨R3⟩
    exact r3_contract_implies_combination_payload R3
  · intro h
    exact ⟨r3ContractOfCombinationPayload h⟩

/-- Equivalent proposition-level form: algebraicity of the transported class at
the selected Hodge/Qbar point implies algebraicity of the original class.

This is the exact variational-algebraicity shape of R3. -/
def R3VariationalAlgebraicityPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∀ (y : S.Base)
    (γ : S.Path S.basepoint y)
    (hy : S.isHodgeAlong γ)
    (hq : S.fieldOfDefinition.isDefinedOverQbar y),
      InConcreteCycleSpan M (S.transportedAlpha γ) →
      InConcreteCycleSpan M α

theorem combination_payload_iff_variational_algebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα} :
    R3CombinationPayload M S ↔
      R3VariationalAlgebraicityPayload M S := by
  constructor
  · intro h y γ hy hq hAlg
    rcases hAlg with ⟨C, hC⟩
    exact h y γ hy hq C hC
  · intro h y γ hy hq C hC
    exact h y γ hy hq ⟨C, hC⟩

theorem r3_contract_iff_variational_algebraicity
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα} :
    Nonempty (R3TransportContract M S) ↔
      R3VariationalAlgebraicityPayload M S :=
  r3_contract_iff_combination_payload.trans
    combination_payload_iff_variational_algebraicity

/-- The old atomwise specialization backend is a sufficient route to the exact
combination payload.  This theorem deliberately has no converse. -/
theorem combination_payload_of_atomic_specialization
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S) :
    R3CombinationPayload M S :=
  r3_contract_implies_combination_payload
    (r3TransportOfAtomicSpecialization A)

theorem variational_payload_of_atomic_specialization
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : DirectPathwiseSpecializationData M S) :
    R3VariationalAlgebraicityPayload M S :=
  combination_payload_iff_variational_algebraicity.mp
    (combination_payload_of_atomic_specialization A)

inductive R3MinimalStatus where
  | exactEquivalent
  | sufficientStrongBackend
  | openVariationalAlgebraicity
  deriving Repr, DecidableEq

structure R3MinimalFrontier where
  combinationPayload : R3MinimalStatus
  variationalAlgebraicityPayload : R3MinimalStatus
  atomwiseSpecialization : R3MinimalStatus

def r3MinimalFrontier : R3MinimalFrontier :=
  {
    combinationPayload := .exactEquivalent
    variationalAlgebraicityPayload := .openVariationalAlgebraicity
    atomwiseSpecialization := .sufficientStrongBackend
  }

theorem r3_combination_payload_exact :
    r3MinimalFrontier.combinationPayload = .exactEquivalent := rfl

theorem r3_variational_algebraicity_open :
    r3MinimalFrontier.variationalAlgebraicityPayload =
      .openVariationalAlgebraicity := rfl

theorem r3_atomwise_is_only_sufficient_backend :
    r3MinimalFrontier.atomwiseSpecialization =
      .sufficientStrongBackend := rfl

#print axioms MCore.BackwardAudit.r3_contract_implies_combination_payload
#print axioms MCore.BackwardAudit.r3ContractOfCombinationPayload
#print axioms MCore.BackwardAudit.r3_contract_iff_combination_payload
#print axioms MCore.BackwardAudit.combination_payload_iff_variational_algebraicity
#print axioms MCore.BackwardAudit.r3_contract_iff_variational_algebraicity
#print axioms MCore.BackwardAudit.combination_payload_of_atomic_specialization
#print axioms MCore.BackwardAudit.variational_payload_of_atomic_specialization
#print axioms MCore.BackwardAudit.r3_combination_payload_exact
#print axioms MCore.BackwardAudit.r3_variational_algebraicity_open
#print axioms MCore.BackwardAudit.r3_atomwise_is_only_sufficient_backend

end MCore.BackwardAudit
