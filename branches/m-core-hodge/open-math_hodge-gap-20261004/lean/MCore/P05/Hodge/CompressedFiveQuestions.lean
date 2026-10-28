import MCore.P05.Hodge.SearchArchitecture

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-- B is mechanically inhabited once p ≥ 2: choose the original variety X. -/
def canonicalAnswerB
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D0 : R1DescentPointContract S)
    (hp : 2 ≤ p) :
    AnswerB D0 :=
  {
    hp := hp
    Y := X
    hY := hX
  }

/-- D is mechanically inhabited for every C by the empty finite source. -/
def emptyAnswerD
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    {B : AnswerB D0}
    (C : AnswerC M B) :
    AnswerD M C :=
  { terms := [] }

/-- Therefore B and D must not be reported as material open gaps. -/
theorem B_is_mechanical
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D0 : R1DescentPointContract S)
    (hp : 2 ≤ p) :
    Nonempty (AnswerB D0) :=
  ⟨canonicalAnswerB D0 hp⟩

theorem D_is_mechanical
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    {B : AnswerB D0}
    (C : AnswerC M B) :
    Nonempty (AnswerD M C) :=
  ⟨emptyAnswerD C⟩

/--
After removing the mechanically inhabited B and D shells, the genuine local
search frontier is A + C + E.
-/
inductive CompressedAnswerKind where
  | arithmeticPoint
  | correspondenceAction
  | targetHit
  deriving Repr, DecidableEq

def compressedOpenAnswers : List CompressedAnswerKind :=
  [.arithmeticPoint, .correspondenceAction, .targetHit]

theorem compressedOpenAnswers_count :
    compressedOpenAnswers.length = 3 := by decide

#print axioms P05.Hodge.B_is_mechanical
#print axioms P05.Hodge.D_is_mechanical
#print axioms P05.Hodge.compressedOpenAnswers_count

end P05.Hodge
