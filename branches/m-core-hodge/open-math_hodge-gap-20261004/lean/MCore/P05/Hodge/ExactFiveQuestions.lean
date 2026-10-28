import MCore.P05.Hodge.OpenWitnesses

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-- A: an arithmetic Hodge point on the chosen spread. -/
def AnswerA
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  QbarIntersectsHodgeLocus S

/-- B: an auxiliary smooth-projective source variety in the q=1 regime. -/
structure AnswerB
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) where
  hp : 2 ≤ p
  Y : G.Variety
  hY : G.isSmoothProjective Y

/-- C: a genuine q=1 correspondence action from B's source variety. -/
structure AnswerC
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (B : AnswerB D) where
  Correspondence : Type
  pushDivisor :
    Correspondence → G.CycleQ B.Y 1 →
      G.CycleQ (S.Family D.point.y) p
  pushClass :
    Correspondence → G.CohomologyQ B.Y (2 * 1) →
      G.CohomologyQ (S.Family D.point.y) (2 * p)
  cycleClass_compat :
    ∀ (Γ : Correspondence) (z : G.CycleQ B.Y 1),
      pushClass Γ (M.cycleClass 1 z) =
        M.cycleClass p (pushDivisor Γ z)

/-- D: a finite algebraic divisor source, without asserting it hits alpha. -/
structure AnswerD
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    {B : AnswerB D}
    (C : AnswerC M B) where
  terms :
    List (M.Coeff × C.Correspondence × G.CycleQ B.Y 1)

/-- Evaluation of D after pushing all divisor cycles through C. -/
def AnswerD.eval
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
    {C : AnswerC M B}
    (D : AnswerD M C) :
    G.CohomologyQ (S.Family D0.point.y) (2 * p) :=
  (D.terms.map (fun t => (t.1, C.pushDivisor t.2.1 t.2.2))).foldr
    (fun t acc => M.addClass (M.smul t.1 (M.cycleClass p t.2)) acc)
    M.zeroClass

/-- E: the only target-specific equality in the A-E route. -/
def AnswerE
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
    {C : AnswerC M B}
    (D : AnswerD M C) : Prop :=
  D.eval = S.transportedAlpha D0.point.path

/-- B+C+D canonically package Q2. -/
def answersBCD_to_Q2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    (B : AnswerB D0)
    (C : AnswerC M B)
    (D : AnswerD M C) :
    HodgeKernelQ2 M D0 :=
  {
    hp := B.hp
    sourceVariety := B.Y
    sourceSmoothProjective := B.hY
    Correspondence := C.Correspondence
    pushDivisor := C.pushDivisor
    pushClass := C.pushClass
    cycleClass_compat := C.cycleClass_compat
    terms := D.terms
  }

/-- E is exactly Q3 after the canonical B+C+D packaging. -/
theorem answerE_iff_Q3
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    (B : AnswerB D0)
    (C : AnswerC M B)
    (D : AnswerD M C) :
    AnswerE D ↔ HodgeKernelQ3 M D0 (answersBCD_to_Q2 B C D) := by
  rfl

/-- A witness plus B,C,D,E closes exact R2 with no additional mathematics. -/
theorem answersABCDE_close_R2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : AnswerA S)
    (Bmk : ∀ D0 : R1DescentPointContract S, AnswerB D0)
    (Cmk : ∀ (D0 : R1DescentPointContract S) (B : AnswerB D0), AnswerC M B)
    (Dmk : ∀ (D0 : R1DescentPointContract S) (B : AnswerB D0)
      (C : AnswerC M B), AnswerD M C)
    (Emk : ∀ (D0 : R1DescentPointContract S) (B : AnswerB D0)
      (C : AnswerC M B) (D : AnswerD M C), AnswerE D) :
    ∃ D0 : R1DescentPointContract S, R2FiberAlgebraicityTarget M D0 := by
  rcases (r1d_contract_iff_qbar_intersection S).2 A with ⟨D0⟩
  let B := Bmk D0
  let C := Cmk D0 B
  let D := Dmk D0 B C
  have hE : AnswerE D := Emk D0 B C D
  refine ⟨D0, ?_⟩
  exact hodgeKernelQ3_closes_R2
    (answersBCD_to_Q2 B C D)
    ((answerE_iff_Q3 B C D).1 hE)

/-- Fail-closed status: the repo currently proves the A-E tail but does not
manufacture universal inhabitants of A-E. -/
inductive FiveAnswerStatus where
  | exactType
  | implicationProved
  | openMath
  deriving Repr, DecidableEq

structure FiveAnswerFrontier where
  A : FiveAnswerStatus
  B : FiveAnswerStatus
  C : FiveAnswerStatus
  D : FiveAnswerStatus
  E : FiveAnswerStatus
  ABCDE_to_R2 : FiveAnswerStatus

def fiveAnswerFrontier : FiveAnswerFrontier :=
  {
    A := .openMath
    B := .openMath
    C := .openMath
    D := .openMath
    E := .openMath
    ABCDE_to_R2 := .implicationProved
  }

theorem five_answer_tail_closed :
    fiveAnswerFrontier.ABCDE_to_R2 = .implicationProved := rfl

#print axioms P05.Hodge.answerE_iff_Q3
#print axioms P05.Hodge.answersABCDE_close_R2
#print axioms P05.Hodge.five_answer_tail_closed

end P05.Hodge
