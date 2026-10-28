import MCore.Hodge

namespace MCore

theorem clay_logic_refutation_implies_not_statement {D : ClayHodgeData}
    (r : ClayLogicRefutationClaim D) : ¬ ClayHodgeStatement D := by
  intro h
  rcases r.counterexample with ⟨X, hX, p, α, hClass, hNotAlg⟩
  exact hNotAlg (h X hX p α hClass)

theorem not_statement_to_counterexample {D : ClayHodgeData}
    (h : ¬ ClayHodgeStatement D) : ClayHodgeCounterexample D := by
  apply Classical.byContradiction
  intro hn
  apply h
  intro X hX p α hClass
  apply Classical.byContradiction
  intro hna
  apply hn
  exact ⟨X, hX, p, α, hClass, hna⟩

theorem clay_refutation_exact {D : ClayHodgeData} :
    (¬ ClayHodgeStatement D) ↔ ClayHodgeCounterexample D := by
  constructor
  · exact not_statement_to_counterexample
  · intro hc hs
    rcases hc with ⟨X, hX, p, α, hClass, hNotAlg⟩
    exact hNotAlg (hs X hX p α hClass)

end MCore
