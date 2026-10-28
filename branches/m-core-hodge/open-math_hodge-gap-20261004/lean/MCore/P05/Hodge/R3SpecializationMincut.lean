import MCore.P05.Hodge.MaterialSearchFrontier

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/--
R3 without endpoint restatement: a genuine specialization action on cycles and
cohomology, with algebraic compatibility laws. The only target-specific field
is recovery of the transported class back to the original alpha.
-/
structure R3SpecializationAction
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

  map_zero :
    specializeClass M.zeroClass = M.zeroClass
  map_add :
    ∀ a b,
      specializeClass (M.addClass a b) =
        M.addClass (specializeClass a) (specializeClass b)
  map_smul :
    ∀ (r : M.Coeff) (a : G.CohomologyQ (S.Family Q.y) (2 * p)),
      specializeClass (M.smul r a) =
        M.smul r (specializeClass a)
  cycleClass_compat :
    ∀ z : G.CycleQ (S.Family Q.y) p,
      specializeClass (M.cycleClass p z) =
        M.cycleClass p (specializeCycle z)

  recover_transported :
    specializeClass (S.transportedAlpha Q.path) = α

def specializeCombination
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (R : R3SpecializationAction M Q)
    (c : CycleCombination G M (S.Family Q.y) p) :
    CycleCombination G M X p :=
  ⟨c.terms.map (fun t => (t.1, R.specializeCycle t.2))⟩

theorem specializeCombination_eval
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (R : R3SpecializationAction M Q)
    (c : CycleCombination G M (S.Family Q.y) p) :
    (specializeCombination R c).eval M =
      R.specializeClass (c.eval M) := by
  unfold specializeCombination CycleCombination.eval
  induction c.terms with
  | nil =>
      exact R.map_zero.symm
  | cons t ts ih =>
      change
        M.addClass
            (M.smul t.1 (M.cycleClass p (R.specializeCycle t.2)))
            ((List.map (fun u => (u.1, R.specializeCycle u.2)) ts).foldr
              (fun u acc =>
                M.addClass (M.smul u.1 (M.cycleClass p u.2)) acc)
              M.zeroClass)
          =
        R.specializeClass
          (M.addClass
            (M.smul t.1 (M.cycleClass p t.2))
            (ts.foldr
              (fun u acc =>
                M.addClass (M.smul u.1 (M.cycleClass p u.2)) acc)
              M.zeroClass))
      calc
        _ =
            M.addClass
              (R.specializeClass
                (M.smul t.1 (M.cycleClass p t.2)))
              (R.specializeClass
                (ts.foldr
                  (fun u acc =>
                    M.addClass (M.smul u.1 (M.cycleClass p u.2)) acc)
                  M.zeroClass)) := by
              rw [ih]
              rw [R.map_smul]
              rw [R.cycleClass_compat]
        _ =
            R.specializeClass
              (M.addClass
                (M.smul t.1 (M.cycleClass p t.2))
                (ts.foldr
                  (fun u acc =>
                    M.addClass (M.smul u.1 (M.cycleClass p u.2)) acc)
                  M.zeroClass)) := by
              exact (R.map_add _ _).symm

theorem r3_action_closes_original_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : AlgebraicPointData M S)
    (R : R3SpecializationAction M
      {
        y := P.y
        path := P.path
        y_is_hodge := P.y_is_hodge
        y_is_defined_over_Qbar := P.y_is_defined_over_Qbar
      }) :
    InConcreteCycleSpan M α := by
  let Q : QbarHodgePointData S :=
    {
      y := P.y
      path := P.path
      y_is_hodge := P.y_is_hodge
      y_is_defined_over_Qbar := P.y_is_defined_over_Qbar
    }
  let cX := specializeCombination R P.combination
  refine ⟨cX, ?_⟩
  calc
    cX.eval M = R.specializeClass (P.combination.eval M) := by
      exact specializeCombination_eval R P.combination
    _ = R.specializeClass (S.transportedAlpha P.path) := by
      rw [P.combination_class]
    _ = α := R.recover_transported

def R3SpecializationAction.toContract
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
        R3SpecializationAction M Q) :
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
      exact r3_action_closes_original_span P (mk Q)
  }

/--
Compressed R3 frontier:
R3a = cycle specialization operation,
R3b = linear/cohomological compatibility,
R3c = recovery of transportedAlpha to alpha.
Once all three are supplied, the rest is kernel-mechanical.
-/
inductive R3Question where
  | cycleSpecialization
  | functorialCompatibility
  | recoverOriginalClass
  deriving Repr, DecidableEq

def r3Questions : List R3Question :=
  [.cycleSpecialization, .functorialCompatibility, .recoverOriginalClass]

theorem r3Questions_count : r3Questions.length = 3 := by decide

#print axioms P05.Hodge.specializeCombination_eval
#print axioms P05.Hodge.r3_action_closes_original_span
#print axioms P05.Hodge.R3SpecializationAction.toContract
#print axioms P05.Hodge.r3Questions_count

end P05.Hodge
