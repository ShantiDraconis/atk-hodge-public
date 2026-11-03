import MCore.K26

namespace MCore.BackwardAudit

/-!
# Hodge tension closure

Fail-closed dual-endpoint closure for the unique Hodge research core.

The core is P := ConcreteAlgebraicityPayload M.
A positive certificate proves P.
A negative certificate proves ¬P.
Without either certificate the logical state is OPEN_50.

The 50/0 numbers are workflow-state labels, not probabilities and not
mathematical completion percentages.
-/

inductive HodgePolarity where
  | positive
  | negative
  deriving Repr, DecidableEq

def HodgePolarity.twist : HodgePolarity → HodgePolarity
  | .positive => .negative
  | .negative => .positive

theorem twist_involutive (p : HodgePolarity) :
    p.twist.twist = p := by
  cases p <;> rfl

abbrev HodgeCore
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ConcreteAlgebraicityPayload M

structure PositiveClosureCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  closes : HodgeCore M

structure NegativeClosureCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  closes : ¬ HodgeCore M

inductive HodgeClosureState where
  | open50
  | closedTrue0
  | closedFalse0
  deriving Repr, DecidableEq

def openMathPercent : HodgeClosureState → Nat
  | .open50 => 50
  | .closedTrue0 => 0
  | .closedFalse0 => 0

theorem open_state_is_50 :
    openMathPercent .open50 = 50 := rfl

theorem true_closed_state_is_0 :
    openMathPercent .closedTrue0 = 0 := rfl

theorem false_closed_state_is_0 :
    openMathPercent .closedFalse0 = 0 := rfl

def closePositive
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (_ : PositiveClosureCertificate M) :
    HodgeClosureState :=
  .closedTrue0

def closeNegative
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (_ : NegativeClosureCertificate M) :
    HodgeClosureState :=
  .closedFalse0

theorem positive_certificate_closes_core
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : PositiveClosureCertificate M) :
    ConcreteAlgebraicityPayload M :=
  C.closes

theorem negative_certificate_refutes_core
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : NegativeClosureCertificate M) :
    ¬ ConcreteAlgebraicityPayload M :=
  C.closes

theorem positive_negative_incompatible
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : PositiveClosureCertificate M)
    (N : NegativeClosureCertificate M) :
    False :=
  N.closes P.closes

/-- Concrete local counterexample shape for the negative side. -/
structure ConcreteAlgebraicityCounterexample
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) where
  X : G.Variety
  p : Nat
  alpha : G.CohomologyQ X (2 * p)
  smoothProjective : G.isSmoothProjective X
  typePP : G.isTypePP p alpha
  outsideCycleSpan : ¬ InConcreteCycleSpan M alpha

def counterexample_to_negative
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (C : ConcreteAlgebraicityCounterexample M) :
    NegativeClosureCertificate M :=
  {
    closes := by
      intro h
      exact C.outsideCycleSpan
        (h C.X C.p C.alpha C.smoothProjective C.typePP)
  }

/-- Four scientific lanes may compete to build the positive endpoint.
The constructors carry only a genuine positive certificate; this prevents
the producer vocabulary from creating proof evidence by itself. -/
inductive PositiveProducer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
  | deformationNormalFunction (certificate : PositiveClosureCertificate M)
  | arithmeticTateLift (certificate : PositiveClosureCertificate M)
  | motivatedRealization (certificate : PositiveClosureCertificate M)
  | kTheoryRealization (certificate : PositiveClosureCertificate M)

def PositiveProducer.certificate
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G} :
    PositiveProducer M → PositiveClosureCertificate M
  | .deformationNormalFunction c => c
  | .arithmeticTateLift c => c
  | .motivatedRealization c => c
  | .kTheoryRealization c => c

theorem any_positive_producer_closes
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : PositiveProducer M) :
    ConcreteAlgebraicityPayload M :=
  P.certificate.closes

/-- At the certified boundary, positive closure transports to Hodge itself. -/
theorem positive_certificate_closes_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (C : PositiveClosureCertificate M) :
    GradedRationalHodgeConjecture G :=
  (k26_minimal_cut B).2 C.closes

/-- At the same boundary, negative closure transports to negation of Hodge. -/
theorem negative_certificate_refutes_hodge
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (C : NegativeClosureCertificate M) :
    ¬ GradedRationalHodgeConjecture G := by
  intro h
  exact C.closes ((k26_minimal_cut B).1 h)

/-- Evidence-presence classification. These are workflow states, not truth
values of the mathematical proposition. -/
inductive EndpointEvidenceState where
  | neither
  | positiveOnly
  | negativeOnly
  | both
  deriving Repr, DecidableEq

/-- Exact audit interpretation of the four evidence configurations.
The both case is inconsistent because positive and negative certificates imply False. -/
inductive ClosureAuditVerdict where
  | open
  | closedTrue
  | closedFalse
  | inconsistent
  deriving Repr, DecidableEq

def closureAuditVerdict : EndpointEvidenceState → ClosureAuditVerdict
  | .neither => .open
  | .positiveOnly => .closedTrue
  | .negativeOnly => .closedFalse
  | .both => .inconsistent

/-- Audit error percentage:
0 = valid mathematical closure;
100 = no endpoint evidence, or contradictory evidence.
There is intentionally no 50 percent mathematical proof state. -/
def auditErrorPercent : EndpointEvidenceState → Nat
  | .neither => 100
  | .positiveOnly => 0
  | .negativeOnly => 0
  | .both => 100

theorem positive_only_is_closed_true :
    closureAuditVerdict .positiveOnly = .closedTrue ∧
    auditErrorPercent .positiveOnly = 0 := by
  exact ⟨rfl, rfl⟩

theorem negative_only_is_closed_false :
    closureAuditVerdict .negativeOnly = .closedFalse ∧
    auditErrorPercent .negativeOnly = 0 := by
  exact ⟨rfl, rfl⟩

theorem neither_is_not_closed :
    closureAuditVerdict .neither = .open ∧
    auditErrorPercent .neither = 100 := by
  exact ⟨rfl, rfl⟩

theorem both_is_invalid :
    closureAuditVerdict .both = .inconsistent ∧
    auditErrorPercent .both = 100 := by
  exact ⟨rfl, rfl⟩

/-- Exact positive parameters required for closure. -/
structure PositiveClosureParameters
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  universalRealization :
    ∀ (X : G.Variety) (p : Nat) (alpha : G.CohomologyQ X (2 * p)),
      G.isSmoothProjective X →
      G.isTypePP p alpha →
      InConcreteCycleSpan M alpha

def positiveParameters_to_certificate
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : PositiveClosureParameters M) :
    PositiveClosureCertificate M :=
  ⟨P.universalRealization⟩

/-- Exact negative parameters required for closure. One faithful witness is
sufficient. -/
structure NegativeClosureParameters
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) where
  witness : ConcreteAlgebraicityCounterexample M

def negativeParameters_to_certificate
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (N : NegativeClosureParameters M) :
    NegativeClosureCertificate M :=
  counterexample_to_negative N.witness

/-- A mathematically closed Hodge outcome. Each constructor carries real
endpoint evidence rather than a status label. -/
inductive HodgeClosedOutcome
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Type
  | trueCase (proof : ConcreteAlgebraicityPayload M)
  | falseCase (proof : ¬ ConcreteAlgebraicityPayload M)

/-- The three admissible branch configurations. V/V is deliberately absent.
Each constructor must carry enough endpoint evidence to make closure real. -/
inductive AdmissibleBranchClosure
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Type
  | falseTrue (proof : ConcreteAlgebraicityPayload M)
  | trueFalse (proof : ¬ ConcreteAlgebraicityPayload M)
  | falseFalse (outcome : HodgeClosedOutcome M)

/-- Exact closure theorem for the three allowed configurations. -/
def admissible_branches_close
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G} :
    AdmissibleBranchClosure M → HodgeClosedOutcome M
  | .falseTrue h => .trueCase h
  | .trueFalse h => .falseCase h
  | .falseFalse h => h

/-- At a certified boundary, every genuine admissible closure enables either
the theorem or its negation. -/
def admissible_branches_enable_theorem
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (C : AdmissibleBranchClosure M) :
    (GradedRationalHodgeConjecture G) ∨
      (¬ GradedRationalHodgeConjecture G) :=
  match admissible_branches_close C with
  | .trueCase h => Or.inl ((k26_minimal_cut B).2 h)
  | .falseCase h =>
      Or.inr (by
        intro hh
        exact h ((k26_minimal_cut B).1 hh))

#print axioms MCore.BackwardAudit.admissible_branches_close
#print axioms MCore.BackwardAudit.admissible_branches_enable_theorem
/-- Current fail-closed state: the transport machine is ready, but neither
endpoint certificate is manufactured here. -/
def currentHodgeClosureState : HodgeClosureState := .open50

theorem current_open_math_is_50 :
    openMathPercent currentHodgeClosureState = 50 := rfl

#print axioms MCore.BackwardAudit.twist_involutive
#print axioms MCore.BackwardAudit.positive_certificate_closes_core
#print axioms MCore.BackwardAudit.negative_certificate_refutes_core
#print axioms MCore.BackwardAudit.positive_negative_incompatible
#print axioms MCore.BackwardAudit.counterexample_to_negative
#print axioms MCore.BackwardAudit.any_positive_producer_closes
#print axioms MCore.BackwardAudit.positive_certificate_closes_hodge
#print axioms MCore.BackwardAudit.negative_certificate_refutes_hodge
#print axioms MCore.BackwardAudit.positive_only_is_closed_true
#print axioms MCore.BackwardAudit.negative_only_is_closed_false
#print axioms MCore.BackwardAudit.neither_is_not_closed
#print axioms MCore.BackwardAudit.both_is_invalid
#print axioms MCore.BackwardAudit.positiveParameters_to_certificate
#print axioms MCore.BackwardAudit.negativeParameters_to_certificate
#print axioms MCore.BackwardAudit.current_open_math_is_50

end MCore.BackwardAudit
