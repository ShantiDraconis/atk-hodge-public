import MCore.FinalAttack

namespace MCore
namespace Frontier

/-!
# Algebraicity candidate bridge

This file is a non-promoting frontier experiment.  It creates no K27 and does
not change the epistemic status of the Hodge conjecture.

The K26 terminal cut is used exactly as certified:

  GradedRationalHodgeConjecture G ↔ ConcreteAlgebraicityPayload M.

Candidate propositions are kept abstract on purpose.  A later geometry layer
may instantiate them with actual standard-conjecture, absolute-Hodge,
variational, motivated-cycle, spread, or normal-function definitions.

No candidate below is asserted.  No implication into the algebraicity payload
is manufactured.
-/

abbrev HodgeAtBoundary (G : GradedRationalHodgeData) : Prop :=
  GradedRationalHodgeConjecture G

abbrev AlgebraicityPayload
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G) : Prop :=
  ConcreteAlgebraicityPayload M

/-- Semantic slots for the six candidate families requested at the terminal
    frontier.  Each field is only a proposition supplied by an external
    geometry formalization. -/
structure AlgebraicityCandidateVocabulary where
  standardConjectureD : Prop
  lefschetzDecompositionHodge : Prop
  absoluteHodge : Prop
  hodgeLocusAlgebraic : Prop
  hasAlgebraicPointOnHodgeLocus : Prop
  motivatedCycle : Prop
  spreadExists : Prop
  spreadDefinedOverQbar : Prop
  normalFunctionHasAlgebraicZero : Prop

def C_Lef_D (V : AlgebraicityCandidateVocabulary) : Prop :=
  V.standardConjectureD ∧ V.lefschetzDecompositionHodge

def C_AbsHodge (V : AlgebraicityCandidateVocabulary) : Prop :=
  V.absoluteHodge

def C_Variational (V : AlgebraicityCandidateVocabulary) : Prop :=
  V.hodgeLocusAlgebraic ∧ V.hasAlgebraicPointOnHodgeLocus

def C_Motivated (V : AlgebraicityCandidateVocabulary) : Prop :=
  V.motivatedCycle

def C_Spread (V : AlgebraicityCandidateVocabulary) : Prop :=
  V.spreadExists ∧ V.spreadDefinedOverQbar

def C_NormalFunction (V : AlgebraicityCandidateVocabulary) : Prop :=
  V.normalFunctionHasAlgebraicZero

/-- Four implication slots are tracked independently.  Missing edges remain
    `none`; an `Option` value is metadata carrying an actual proof when one
    has been supplied. -/
structure CandidateEdges (H A C : Prop) where
  H_implies_C : Option (PLift (H → C)) := none
  A_implies_C : Option (PLift (A → C)) := none
  C_implies_H : Option (PLift (C → H)) := none
  C_implies_A : Option (PLift (C → A)) := none

/-- The six candidate rows can be tested in a single build without claiming
    that any row is complete. -/
structure CandidateMatrix
    {G : GradedRationalHodgeData} (M : CycleSpanMechanics G)
    (V : AlgebraicityCandidateVocabulary) where
  lefschetzD :
    CandidateEdges (HodgeAtBoundary G) (AlgebraicityPayload M) (C_Lef_D V)
  absoluteHodge :
    CandidateEdges (HodgeAtBoundary G) (AlgebraicityPayload M) (C_AbsHodge V)
  variational :
    CandidateEdges (HodgeAtBoundary G) (AlgebraicityPayload M) (C_Variational V)
  motivated :
    CandidateEdges (HodgeAtBoundary G) (AlgebraicityPayload M) (C_Motivated V)
  spread :
    CandidateEdges (HodgeAtBoundary G) (AlgebraicityPayload M) (C_Spread V)
  normalFunction :
    CandidateEdges (HodgeAtBoundary G) (AlgebraicityPayload M) (C_NormalFunction V)

/-- Logical equivalence follows immediately if both A→C and C→A are proved. -/
theorem candidate_equivalent_of_both_directions
    {A C : Prop} (hAC : A → C) (hCA : C → A) : C ↔ A :=
  ⟨hCA, hAC⟩

/-- A useful sanity check for the originally proposed five-field test:
    demanding A→C, C→A, and ¬(C↔A) simultaneously is inconsistent. -/
theorem strict_nonequivalence_impossible_of_both_directions
    {A C : Prop} (hAC : A → C) (hCA : C → A) :
    ¬ (¬ (C ↔ A)) := by
  intro h
  exact h (candidate_equivalent_of_both_directions hAC hCA)

/-- A candidate can only close the terminal cut when an actual proof of the
    candidate is available independently and an actual reduction C→A has been
    proved.  This is the logical core of a future promotion review, not a
    promotion itself. -/
structure CandidateClosureEvidence (C A : Prop) where
  candidateProof : C
  candidateToAlgebraicity : C → A

theorem candidate_closure_yields_algebraicity
    {C A : Prop} (E : CandidateClosureEvidence C A) : A :=
  E.candidateToAlgebraicity E.candidateProof

/-- Once a candidate has genuinely produced the K26 payload, the already
    certified K26 direction transports it to Hodge.  No candidate is supplied
    by this theorem. -/
theorem candidate_closure_yields_hodge
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    {C : Prop}
    (E : CandidateClosureEvidence C (AlgebraicityPayload M)) :
    HodgeAtBoundary G :=
  (k26_minimal_cut B).2 (candidate_closure_yields_algebraicity E)

/-! ## Variational + spread factorization

The following lemmas deliberately expose, rather than hide, the exact missing
arrows.  In particular, algebraicity of the Hodge locus alone does not produce
the algebraicity payload.
-/

theorem variational_of_locus_and_algebraic_point
    {V : AlgebraicityCandidateVocabulary}
    (hLocus : V.hodgeLocusAlgebraic)
    (hPoint : V.hasAlgebraicPointOnHodgeLocus) :
    C_Variational V :=
  ⟨hLocus, hPoint⟩

/-- This is the precise conditional specialization slot.  The theorem does not
    assert specialization; it shows exactly what proving that geometric theorem
    would buy. -/
theorem variational_to_payload_given_specialization
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    {V : AlgebraicityCandidateVocabulary}
    (specialization :
      V.hasAlgebraicPointOnHodgeLocus → AlgebraicityPayload M) :
    C_Variational V → AlgebraicityPayload M := by
  intro hV
  exact specialization hV.2

/-- Spread can feed the variational row only after a separate theorem produces
    an algebraic point on the relevant Hodge locus. -/
theorem spread_to_variational_given_point_theorem
    {V : AlgebraicityCandidateVocabulary}
    (hLocus : V.hodgeLocusAlgebraic)
    (spreadProducesPoint :
      C_Spread V → V.hasAlgebraicPointOnHodgeLocus) :
    C_Spread V → C_Variational V := by
  intro hSpread
  exact ⟨hLocus, spreadProducesPoint hSpread⟩

/-- Dense composition of the two still-open geometric arrows.  It is useful
    for CI because the only mathematical inputs are visible in the type. -/
theorem spread_to_payload_given_geometric_inputs
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    {V : AlgebraicityCandidateVocabulary}
    (hLocus : V.hodgeLocusAlgebraic)
    (spreadProducesPoint :
      C_Spread V → V.hasAlgebraicPointOnHodgeLocus)
    (specialization :
      V.hasAlgebraicPointOnHodgeLocus → AlgebraicityPayload M) :
    C_Spread V → AlgebraicityPayload M := by
  intro hSpread
  exact specialization (spreadProducesPoint hSpread)

/-- If both directions to the K26 payload are supplied, FinalAttack classifies
    the candidate as an equivalent reformulation rather than a frontier
    reduction. -/
theorem candidate_equivalence_hits_final_attack_firewall
    {G : GradedRationalHodgeData} {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (C : Prop)
    (hCA : C → AlgebraicityPayload M)
    (hAC : AlgebraicityPayload M → C) :
    C ↔ HodgeAtBoundary G := by
  exact fa_equivalent_payload_is_circular B C hCA hAC

inductive CandidateAuditStatus where
  | untested
  | externalFormalizationRequired
  | conditionalReduction
  | provedReduction
  | equivalentReformulation
  | counterexampleFound
  deriving Repr, DecidableEq

/-- Current fail-closed frontier state.  These are audit labels only; they are
    not mathematical proof objects. -/
structure AlgebraicityCandidateFrontier where
  lefschetzD : CandidateAuditStatus
  absoluteHodge : CandidateAuditStatus
  variational : CandidateAuditStatus
  motivated : CandidateAuditStatus
  spread : CandidateAuditStatus
  normalFunction : CandidateAuditStatus
  payload : SignatureStatus
  hodge : SignatureStatus

def algebraicityCandidateFrontier : AlgebraicityCandidateFrontier :=
  { lefschetzD := .externalFormalizationRequired
    absoluteHodge := .externalFormalizationRequired
    variational := .conditionalReduction
    motivated := .externalFormalizationRequired
    spread := .conditionalReduction
    normalFunction := .externalFormalizationRequired
    payload := .openBridge
    hodge := .openBridge }

theorem candidate_frontier_payload_open :
    algebraicityCandidateFrontier.payload = .openBridge := rfl

theorem candidate_frontier_hodge_open :
    algebraicityCandidateFrontier.hodge = .openBridge := rfl

#print axioms candidate_equivalent_of_both_directions
#print axioms strict_nonequivalence_impossible_of_both_directions
#print axioms candidate_closure_yields_algebraicity
#print axioms candidate_closure_yields_hodge
#print axioms variational_of_locus_and_algebraic_point
#print axioms variational_to_payload_given_specialization
#print axioms spread_to_variational_given_point_theorem
#print axioms spread_to_payload_given_geometric_inputs
#print axioms candidate_equivalence_hits_final_attack_firewall
#print axioms candidate_frontier_payload_open
#print axioms candidate_frontier_hodge_open

end Frontier
end MCore
