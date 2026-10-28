import MCore.P05.Hodge.ExactFiveQuestions

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

universe u v

/--
A sound search engine. Candidates may be generated arbitrarily; only
`accept = true` is allowed to yield a mathematical witness.
-/
structure SearchEngine (W : Sort u) where
  Candidate : Type v
  enumerate : Nat → List Candidate
  accept : Candidate → Bool
  sound : ∀ c : Candidate, accept c = true → W

def SearchEngine.certify
    {W : Sort u}
    (E : SearchEngine W)
    (c : E.Candidate)
    (h : E.accept c = true) : W :=
  E.sound c h

/-- Search engine for A: arithmetic Hodge/Qbar point. -/
abbrev AnswerASearch
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :=
  SearchEngine (AnswerA S)

/-- Search engine for B: smooth-projective auxiliary source. -/
abbrev AnswerBSearch
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D0 : R1DescentPointContract S) :=
  SearchEngine (AnswerB D0)

/-- Search engine for C: q=1 algebraic correspondence geometry. -/
abbrev AnswerCSearch
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    (B : AnswerB D0) :=
  SearchEngine (AnswerC M B)

/-- Search engine for D: finite divisor source. -/
abbrev AnswerDSearch
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    {B : AnswerB D0}
    (C : AnswerC M B) :=
  SearchEngine (AnswerD M C)

/--
Injective computable coordinates for a cohomology carrier. This is the exact
extra structure needed to turn equality testing for E into a Boolean check.
-/
structure CohomologyCoordinates (V : Type u) where
  Coord : Type v
  decEq : DecidableEq Coord
  encode : V → Coord
  encode_injective :
    ∀ {a b : V}, encode a = encode b → a = b

def CohomologyCoordinates.equal
    {V : Type u}
    (K : CohomologyCoordinates V)
    (a b : V) : Bool := by
  letI : DecidableEq K.Coord := K.decEq
  exact decide (K.encode a = K.encode b)

theorem CohomologyCoordinates.equal_sound
    {V : Type u}
    (K : CohomologyCoordinates V)
    {a b : V}
    (h : K.equal a b = true) :
    a = b := by
  unfold CohomologyCoordinates.equal at h
  simp only [decide_eq_true_eq] at h
  exact K.encode_injective h

theorem CohomologyCoordinates.equal_complete
    {V : Type u}
    (K : CohomologyCoordinates V)
    {a b : V}
    (h : a = b) :
    K.equal a b = true := by
  subst b
  unfold CohomologyCoordinates.equal
  simp

/-- Boolean verifier for the only target-specific answer E. -/
def verifyAnswerE
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
    (D : AnswerD M C)
    (K : CohomologyCoordinates
      (G.CohomologyQ (S.Family D0.point.y) (2 * p))) : Bool :=
  K.equal D.eval (S.transportedAlpha D0.point.path)

theorem verifyAnswerE_sound
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
    (D : AnswerD M C)
    (K : CohomologyCoordinates
      (G.CohomologyQ (S.Family D0.point.y) (2 * p)))
    (h : verifyAnswerE D K = true) :
    AnswerE D :=
  K.equal_sound h

theorem verifyAnswerE_complete
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
    (D : AnswerD M C)
    (K : CohomologyCoordinates
      (G.CohomologyQ (S.Family D0.point.y) (2 * p)))
    (h : AnswerE D) :
    verifyAnswerE D K = true :=
  K.equal_complete h

/--
Full A-D search architecture plus a coordinate model for E.
This object still contains no A-E witness: it contains only generators,
Boolean checks, and soundness theorems.
-/
structure FiveAnswerSearchArchitecture
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  searchA : AnswerASearch S
  searchB : ∀ D0 : R1DescentPointContract S, AnswerBSearch D0
  searchC :
    ∀ (D0 : R1DescentPointContract S) (B : AnswerB D0),
      AnswerCSearch M B
  searchD :
    ∀ (D0 : R1DescentPointContract S) (B : AnswerB D0)
      (C : AnswerC M B),
      AnswerDSearch M C
  coordinates :
    ∀ D0 : R1DescentPointContract S,
      CohomologyCoordinates
        (G.CohomologyQ (S.Family D0.point.y) (2 * p))

/-- A concrete accepted A candidate yields the exact arithmetic witness. -/
def FiveAnswerSearchArchitecture.certifyA
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : FiveAnswerSearchArchitecture M S)
    (c : P.searchA.Candidate)
    (h : P.searchA.accept c = true) :
    AnswerA S :=
  P.searchA.certify c h

/--
Once search has certified A,B,C,D and the coordinate verifier accepts E,
exact R2 follows with no further open mathematics.
-/
theorem certified_search_answers_close_R2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (A : AnswerA S)
    (D0 : R1DescentPointContract S)
    (B : AnswerB D0)
    (C : AnswerC M B)
    (D : AnswerD M C)
    (K : CohomologyCoordinates
      (G.CohomologyQ (S.Family D0.point.y) (2 * p)))
    (hE : verifyAnswerE D K = true) :
    R2FiberAlgebraicityTarget M D0 := by
  have E : AnswerE D := verifyAnswerE_sound D K hE
  exact hodgeKernelQ3_closes_R2
    (answersBCD_to_Q2 B C D)
    ((answerE_iff_Q3 B C D).1 E)

inductive SearchArchitectureStatus where
  | structured
  | sound
  | needsConcreteEnumerator
  | needsCoordinateModel
  | needsAcceptedCandidate
  deriving Repr, DecidableEq

structure FiveAnswerSearchFrontier where
  AEngine : SearchArchitectureStatus
  BEngine : SearchArchitectureStatus
  CEngine : SearchArchitectureStatus
  DEngine : SearchArchitectureStatus
  EVerifier : SearchArchitectureStatus
  soundness : SearchArchitectureStatus
  concreteSearch : SearchArchitectureStatus

def fiveAnswerSearchFrontier : FiveAnswerSearchFrontier :=
  {
    AEngine := .structured
    BEngine := .structured
    CEngine := .structured
    DEngine := .structured
    EVerifier := .structured
    soundness := .sound
    concreteSearch := .needsConcreteEnumerator
  }

theorem five_answer_search_sound :
    fiveAnswerSearchFrontier.soundness = .sound := rfl

#print axioms P05.Hodge.SearchEngine.certify
#print axioms P05.Hodge.CohomologyCoordinates.equal_sound
#print axioms P05.Hodge.verifyAnswerE_sound
#print axioms P05.Hodge.verifyAnswerE_complete
#print axioms P05.Hodge.certified_search_answers_close_R2
#print axioms P05.Hodge.five_answer_search_sound

end P05.Hodge
