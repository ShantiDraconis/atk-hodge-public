import MCore.P05.Hodge.CompressedFiveQuestions

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

universe u

/-- Executable first-hit search over a finite candidate list. -/
def findAccepted {C : Type u} (accept : C → Bool) : List C → Option C
  | [] => none
  | c :: cs => if accept c then some c else findAccepted accept cs

theorem findAccepted_sound
    {C : Type u}
    (accept : C → Bool)
    {cs : List C}
    {c : C}
    (h : findAccepted accept cs = some c) :
    accept c = true := by
  induction cs with
  | nil =>
      simp [findAccepted] at h
  | cons x xs ih =>
      unfold findAccepted at h
      by_cases hx : accept x = true
      · simp [hx] at h
        cases h
        exact hx
      · have hx' : accept x = false := by
          cases hax : accept x <;> simp_all
        simp [hx'] at h
        exact ih h

/-- A concrete bounded search result carries both the candidate and acceptance. -/
structure AcceptedCandidate {C : Type u} (accept : C → Bool) where
  candidate : C
  accepted : accept candidate = true

def searchList {C : Type u} (accept : C → Bool) (cs : List C) :
    Option (AcceptedCandidate accept) :=
  match h : findAccepted accept cs with
  | none => none
  | some c => some ⟨c, findAccepted_sound accept h⟩

/-- Candidate for A: an actual point and path, plus computable checks. -/
structure ACandidate
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  y : S.Base
  path : S.Path S.basepoint y
  hodgeCheck : Bool
  qbarCheck : Bool
  hodgeSound : hodgeCheck = true → S.isHodgeAlong path
  qbarSound :
    qbarCheck = true → S.fieldOfDefinition.isDefinedOverQbar y

def ACandidate.accept
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (c : ACandidate S) : Bool :=
  c.hodgeCheck && c.qbarCheck

theorem ACandidate.accept_sound
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (c : ACandidate S)
    (h : c.accept = true) :
    AnswerA S := by
  unfold ACandidate.accept at h
  cases hh : c.hodgeCheck <;> cases hq : c.qbarCheck
  · simp [hh, hq] at h
  · simp [hh, hq] at h
  · simp [hh, hq] at h
  · exact ⟨c.y, ⟨c.path, c.hodgeSound hh⟩, c.qbarSound hq⟩

def ACandidate.toContract
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (c : ACandidate S)
    (h : c.accept = true) :
    R1DescentPointContract S := by
  unfold ACandidate.accept at h
  cases hh : c.hodgeCheck <;> cases hq : c.qbarCheck
  · simp [hh, hq] at h
  · simp [hh, hq] at h
  · simp [hh, hq] at h
  · exact {
      point := {
        y := c.y
        path := c.path
        y_is_hodge := c.hodgeSound hh
        y_is_defined_over_Qbar := c.qbarSound hq
      }
    }

def searchA
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (pool : List (ACandidate S)) :
    Option (AcceptedCandidate (fun c : ACandidate S => c.accept)) :=
  searchList (fun c : ACandidate S => c.accept) pool

def searchA_toContract
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {pool : List (ACandidate S)}
    {hit : AcceptedCandidate (fun c : ACandidate S => c.accept)}
    (_h : searchA pool = some hit) :
    R1DescentPointContract S :=
  hit.candidate.toContract hit.accepted

/--
C-candidates are deliberately genuine AnswerC values. The search layer may
rank/filter them, but cannot fabricate a correspondence action.
-/



structure CCandidate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D0 : R1DescentPointContract S}
    (B : AnswerB D0) where
  action : AnswerC M B
  admissibleCheck : Bool
  admissibleSound : admissibleCheck = true → True

def CCandidate.accept
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
    (c : CCandidate M B) : Bool :=
  c.admissibleCheck

def searchC
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
    (pool : List (CCandidate M B)) :
    Option (AnswerC M B) :=
  match searchList CCandidate.accept pool with
  | none => none
  | some hit => some hit.candidate.action

/-- D-pool search. D itself is mechanically inhabited, but nonempty terms may
be supplied here when looking for a nontrivial E hit. -/
structure DCandidate
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
    (C : AnswerC M B) where
  source : AnswerD M C

/-- E-search evaluates every D candidate using the concrete coordinate model. -/
def searchE
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
    (K : CohomologyCoordinates
      (G.CohomologyQ (S.Family D0.point.y) (2 * p)))
    (pool : List (DCandidate M C)) :
    Option (DCandidate M C) :=
  findAccepted (fun d => verifyAnswerE d.source K) pool

theorem searchE_sound
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
    (K : CohomologyCoordinates
      (G.CohomologyQ (S.Family D0.point.y) (2 * p)))
    {pool : List (DCandidate M C)}
    {d : DCandidate M C}
    (h : searchE K pool = some d) :
    AnswerE d.source := by
  unfold searchE at h
  have ha :
      verifyAnswerE d.source K = true :=
    findAccepted_sound
      (fun x : DCandidate M C => verifyAnswerE x.source K) h
  exact verifyAnswerE_sound d.source K ha

#print axioms P05.Hodge.findAccepted_sound
#print axioms P05.Hodge.ACandidate.accept_sound
#print axioms P05.Hodge.searchE_sound

end P05.Hodge
