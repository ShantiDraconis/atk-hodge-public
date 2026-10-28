import MCore.P05.Hodge.ConcreteSearchEngine

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-- Concrete A candidate on the existing Bool countermodel. -/
def counterACandidate : ACandidate kernelQCounterSpread :=
  {
    y := ()
    path := ()
    hodgeCheck := true
    qbarCheck := true
    hodgeSound := by
      intro h
      exact True.intro
    qbarSound := by
      intro h
      exact True.intro
  }

def counterAPool : List (ACandidate kernelQCounterSpread) :=
  [counterACandidate]

theorem counterA_search_hits :
    (searchA counterAPool).isSome = true := by
  rfl

/-- Mechanical B for p=2 on the same countermodel. -/
def counterB : AnswerB kernelQCounterDescent :=
  canonicalAnswerB kernelQCounterDescent (by decide)

/-- Concrete correspondence action C, reusing the existing Q1 countermodel. -/
def counterC : AnswerC kernelQCounterM counterB :=
  {
    Correspondence := Unit
    pushDivisor := fun _ _ => ()
    pushClass := fun _ _ => false
    cycleClass_compat := by
      intro Γ z
      rfl
  }

def counterCCandidate : CCandidate kernelQCounterM counterB :=
  {
    action := counterC
    admissibleCheck := true
    admissibleSound := by
      intro h
      exact True.intro
  }

def counterCPool : List (CCandidate kernelQCounterM counterB) :=
  [counterCCandidate]

theorem counterC_search_hits :
    (searchC counterCPool).isSome = true := by
  rfl

/-- Injective decidable coordinates for Bool cohomology. -/
def counterCoordinates :
    CohomologyCoordinates Bool :=
  {
    Coord := Bool
    decEq := inferInstance
    encode := fun b => b
    encode_injective := by
      intro a b h
      exact h
  }

/-- Empty source is the canonical D candidate. Its evaluation is false. -/
def counterD : AnswerD kernelQCounterM counterC :=
  emptyAnswerD counterC

def counterDCandidate : DCandidate kernelQCounterM counterC :=
  { source := counterD }

def counterDPool : List (DCandidate kernelQCounterM counterC) :=
  [counterDCandidate]

theorem counterE_verifier_rejects :
    verifyAnswerE counterD counterCoordinates = false := by
  rfl

theorem counterE_search_rejects :
    searchE counterCoordinates counterDPool = none := by
  rfl

/--
End-to-end search sanity:
A is found, C is found, but E is rejected because all pushed cycle classes are
false while transportedAlpha is true. Therefore the executable search is
fail-closed rather than manufacturing a target hit.
-/
theorem executable_search_fail_closed :
    (searchA counterAPool).isSome = true ∧
    (searchC counterCPool).isSome = true ∧
    searchE counterCoordinates counterDPool = none := by
  exact ⟨counterA_search_hits, counterC_search_hits, counterE_search_rejects⟩

#print axioms P05.Hodge.counterA_search_hits
#print axioms P05.Hodge.counterC_search_hits
#print axioms P05.Hodge.counterE_verifier_rejects
#print axioms P05.Hodge.counterE_search_rejects
#print axioms P05.Hodge.executable_search_fail_closed

end P05.Hodge
