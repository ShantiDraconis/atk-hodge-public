import MCore.P05.Hodge.R3SpecializationMincut

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/--
Minimal R3 interface at exactly the level consumed by K15.
No separate zero/add/smul laws are required here: they are compressed into the
single finite-combination compatibility actually used by the endpoint.
-/
structure R3CombinationSpecialization
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (Q : QbarHodgePointData S) where
  specializeCycle :
    G.CycleQ (S.Family Q.y) p → G.CycleQ X p
  specializeClass :
    G.CohomologyQ (S.Family Q.y) (2 * p) →
      G.CohomologyQ X (2 * p)

  combination_compat :
    ∀ c : CycleCombination G M (S.Family Q.y) p,
      (⟨c.terms.map (fun t => (t.1, specializeCycle t.2))⟩ :
        CycleCombination G M X p).eval M =
      specializeClass (c.eval M)

  recover_transported :
    specializeClass (S.transportedAlpha Q.path) = α

def R3CombinationSpecialization.specializeCombination
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (R : R3CombinationSpecialization M Q)
    (c : CycleCombination G M (S.Family Q.y) p) :
    CycleCombination G M X p :=
  ⟨c.terms.map (fun t => (t.1, R.specializeCycle t.2))⟩

theorem R3CombinationSpecialization.closes_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : AlgebraicPointData M S)
    (R : R3CombinationSpecialization M
      {
        y := P.y
        path := P.path
        y_is_hodge := P.y_is_hodge
        y_is_defined_over_Qbar := P.y_is_defined_over_Qbar
      }) :
    InConcreteCycleSpan M α := by
  let cX := R.specializeCombination P.combination
  refine ⟨cX, ?_⟩
  calc
    cX.eval M = R.specializeClass (P.combination.eval M) := by
      exact R.combination_compat P.combination
    _ = R.specializeClass (S.transportedAlpha P.path) := by
      rw [P.combination_class]
    _ = α := R.recover_transported

def R3CombinationSpecialization.toContract
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (mk :
      ∀ Q : QbarHodgePointData S,
        R3CombinationSpecialization M Q) :
    R3TransportContract M S :=
  {
    transport := by
      intro P
      let Q : QbarHodgePointData S :=
        {
          y := P.y
          path := P.path
          y_is_hodge := P.y_is_hodge
          y_is_defined_over_Qbar := P.y_is_defined_over_Qbar
        }
      exact R3CombinationSpecialization.closes_span P (mk Q)
  }

/-- The stronger algebraic-law interface mechanically yields the compressed one. -/
def R3SpecializationAction.toCombinationSpecialization
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (R : R3SpecializationAction M Q) :
    R3CombinationSpecialization M Q :=
  {
    specializeCycle := R.specializeCycle
    specializeClass := R.specializeClass
    combination_compat := specializeCombination_eval R
    recover_transported := R.recover_transported
  }

inductive R3MinimalQuestion where
  | cycleSpecialization
  | finiteCombinationCompatibility
  | recoverOriginalClass
  deriving Repr, DecidableEq

def r3MinimalQuestions : List R3MinimalQuestion :=
  [.cycleSpecialization, .finiteCombinationCompatibility, .recoverOriginalClass]

theorem r3MinimalQuestions_count :
    r3MinimalQuestions.length = 3 := by decide

#print axioms P05.Hodge.R3CombinationSpecialization.closes_span
#print axioms P05.Hodge.R3CombinationSpecialization.toContract
#print axioms P05.Hodge.R3SpecializationAction.toCombinationSpecialization
#print axioms P05.Hodge.r3MinimalQuestions_count

end P05.Hodge
