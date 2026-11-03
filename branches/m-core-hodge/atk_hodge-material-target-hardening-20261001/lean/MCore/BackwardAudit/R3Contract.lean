import MCore.BackwardAudit.TypedVariationalGeometry

namespace MCore.BackwardAudit

/-- Exact R3 target: the K15 finite rational cycle-span witness at the
    ORIGINAL class alpha. -/
def R3ConcreteTarget
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    (α : G.CohomologyQ X (2 * p)) : Prop :=
  InConcreteCycleSpan M α

/-- Quantifier-faithful R3 contract.

    Input is an AlgebraicPointData attached to the exact
    (G,X,p,alpha,hX,hAlpha,SpreadData) instance. Output is the exact K15 target
    at the original fiber. No generic CandidateBridge proposition remains. -/
structure R3TransportContract
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  transport :
    AlgebraicPointData M S →
    R3ConcreteTarget M α

/-- With a typed R3 contract and a typed algebraic point, the exact K15
    witness follows. -/
theorem r3_contract_yields_concrete_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R3 : R3TransportContract M S)
    (P : AlgebraicPointData M S) :
    InConcreteCycleSpan M α :=
  R3.transport P

/-- K15 adapter converts the exact R3 witness into the semantic span predicate
    used by K13. -/
theorem r3_contract_yields_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : CycleSpanAdapter G M)
    (R3 : R3TransportContract M S)
    (P : AlgebraicPointData M S) :
    G.inCycleClassSpan p α :=
  (A.span_iff α).2 (R3.transport P)

/-- The new R3 signature is indexed by the canonical K13 input and its exact
    spread instance. Quantifier matching is therefore true by construction;
    existence of the transport theorem remains open. -/
def r3CandidateQuantifierMatch : Bool := true

/-- No mathematical transport/specialization theorem is asserted. -/
def r3TransportClosed : Bool := false

inductive R3ResidueStatus where
  | openResidue
  | typeInterfaceNeeded
  deriving Repr, DecidableEq

structure R3ResidueRecord where
  name : String
  status : R3ResidueStatus
  note : String
  deriving Repr

def r3Residues : List R3ResidueRecord :=
  [
    ⟨"CYCLE_SPECIALIZATION", .typeInterfaceNeeded,
      "A typed specialization operation for cycle combinations is not present in the current corpus."⟩,
    ⟨"CYCLE_SPREAD", .typeInterfaceNeeded,
      "A typed spread-of-cycles interface is not present in the current corpus."⟩,
    ⟨"HILBERT_CHOW_PARAMETER_SPACE", .typeInterfaceNeeded,
      "No Hilbert/Chow parameter-space type is present in the current corpus."⟩,
    ⟨"FLATNESS_PROPERNESS", .typeInterfaceNeeded,
      "The geometric hypotheses needed for specialization are not typed yet."⟩,
    ⟨"CYCLE_CLASS_SPECIALIZATION_COMPATIBILITY", .openResidue,
      "This is the exact mathematical compatibility needed to turn the fiber witness into the K15 target."⟩
  ]

theorem r3_quantifier_match :
    r3CandidateQuantifierMatch = true := by
  rfl

theorem r3_transport_still_open :
    r3TransportClosed = false := by
  rfl

#print axioms MCore.BackwardAudit.r3_contract_yields_concrete_span
#print axioms MCore.BackwardAudit.r3_contract_yields_span
#print axioms MCore.BackwardAudit.r3_quantifier_match
#print axioms MCore.BackwardAudit.r3_transport_still_open

end MCore.BackwardAudit
