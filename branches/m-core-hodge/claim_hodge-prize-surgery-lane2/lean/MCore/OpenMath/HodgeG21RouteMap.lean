import MCore.OpenMath.HodgeFastExternalRoute

namespace MCore

/--
Generic negative formulation pattern distilled from a falsified formulation:
a candidate formulation A is incompatible with a required condition A',
while the alleged claim P entails A'. Then A and P cannot coexist.

This is deliberately hypothesis-explicit. It does not transfer any theorem
between domains unless both arrows are instantiated in the target domain.
-/
structure NegativeFormulationPattern (A A' P : Prop) : Prop where
  rejectsRequired : A → ¬ A'
  claimRequiresRequired : P → A'

theorem negative_formulation_closes
    {A A' P : Prop}
    (F : NegativeFormulationPattern A A' P) :
    A → ¬ A' ∧ (A ∧ P → False) := by
  intro hA
  constructor
  · exact F.rejectsRequired hA
  · rintro ⟨_, hP⟩
    exact F.rejectsRequired hA (F.claimRequiresRequired hP)

/--
Hodge route classification. A negative formulation firewall may close a bad
route, but only a faithful concrete external input can inhabit the scientific
refutation lane.
-/
inductive HodgeRouteKind where
  | negativeFirewall
  | positiveProducer
  deriving Repr, DecidableEq

inductive HodgeRouteState where
  | frozenRejected
  | openMath
  | sourceReadyConditional
  deriving Repr, DecidableEq

structure HodgeRouteBoundary where
  name : String
  kind : HodgeRouteKind
  state : HodgeRouteState
  terminalTarget : String
  scientificPromotion : Bool

def hodgeAbstractSeparatorRoute : HodgeRouteBoundary :=
  {
    name := "ABSTRACT_SEPARATOR_EQUIVALENT_REFORMULATION"
    kind := .negativeFirewall
    state := .frozenRejected
    terminalTarget := "notAlgebraic"
    scientificPromotion := false
  }

def hodgeCodimOneRefutationRoute : HodgeRouteBoundary :=
  {
    name := "CODIMENSION_ONE_REFUTATION"
    kind := .negativeFirewall
    state := .frozenRejected
    terminalTarget := "PrizeCounterexampleConstruction"
    scientificPromotion := false
  }

def hodgeR2R3ShortcutRoute : HodgeRouteBoundary :=
  {
    name := "R2_R3_ENDPOINT_EQUIVALENT_SHORTCUT"
    kind := .negativeFirewall
    state := .frozenRejected
    terminalTarget := "general algebraicity"
    scientificPromotion := false
  }

def hodgeConcreteExternalRoute : HodgeRouteBoundary :=
  {
    name := "HODGE_CONCRETE_EXTERNAL_INPUT"
    kind := .positiveProducer
    state := .openMath
    terminalTarget := "HodgeScientificExternalCertificate"
    scientificPromotion := true
  }

theorem hodge_negative_firewalls_do_not_promote :
    hodgeAbstractSeparatorRoute.scientificPromotion = false ∧
    hodgeCodimOneRefutationRoute.scientificPromotion = false ∧
    hodgeR2R3ShortcutRoute.scientificPromotion = false := by
  constructor
  · rfl
  constructor <;> rfl

theorem hodge_only_live_route_is_positive_producer :
    hodgeConcreteExternalRoute.kind = .positiveProducer ∧
    hodgeConcreteExternalRoute.state = .openMath ∧
    hodgeConcreteExternalRoute.scientificPromotion = true := by
  constructor
  · rfl
  constructor <;> rfl

/-- Once the faithful Hodge producer is actually inhabited, the already-green
fast path reaches the scientific external certificate with no extra open gate. -/
def hodge_live_route_to_external
    (I : HodgeConcreteExternalInput) :
    HodgeScientificExternalCertificate I.D :=
  concreteInputScientificExternal I

#print axioms MCore.negative_formulation_closes
#print axioms MCore.hodge_negative_firewalls_do_not_promote
#print axioms MCore.hodge_only_live_route_is_positive_producer
#print axioms MCore.hodge_live_route_to_external

end MCore
