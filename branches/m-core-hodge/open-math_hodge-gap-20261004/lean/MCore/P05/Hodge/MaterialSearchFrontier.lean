import MCore.P05.Hodge.ExecutableSearchSmokeTest
import MCore.BackwardAudit.R1dBasepointFastPath
import MCore.BackwardAudit.R3Contract

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/--
Concrete A candidate for the already-proved basepoint fast path.
This does not assert that every spread has a Qbar basepoint.
-/
def basepointACandidate
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    ACandidate S :=
  {
    y := S.basepoint
    path := S.pathRefl S.basepoint
    hodgeCheck := true
    qbarCheck := true
    hodgeSound := by
      intro _
      exact basepoint_isHodgeAlong
        (canonicalTypePPCastCompatibility G) S
    qbarSound := by
      intro _
      exact hQbar
  }

def basepointAPool
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    List (ACandidate S) :=
  [basepointACandidate S hQbar]

theorem basepointA_search_hits
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    (searchA (basepointAPool S hQbar)).isSome = true := by
  rfl

/--
The actual material frontier after executable A/C/E compression.
R3 is included explicitly because A+C+E closes R2 only.
-/
inductive MaterialSearchGap where
  | qbarHodgePoint
  | correspondenceAction
  | targetHit
  | specializationTransport
  deriving Repr, DecidableEq

def materialSearchGaps : List MaterialSearchGap :=
  [.qbarHodgePoint, .correspondenceAction, .targetHit,
   .specializationTransport]

theorem materialSearchGaps_count :
    materialSearchGaps.length = 4 := by decide

structure MaterialSearchStatus where
  A_basepointFastPath : Bool
  C_universalProducer : Bool
  E_universalTargetHit : Bool
  R3_universalTransport : Bool
  A_C_E_to_R2 : Bool

def materialSearchStatus : MaterialSearchStatus :=
  {
    A_basepointFastPath := true
    C_universalProducer := false
    E_universalTargetHit := false
    R3_universalTransport := false
    A_C_E_to_R2 := true
  }

theorem basepoint_fast_path_green :
    materialSearchStatus.A_basepointFastPath = true := rfl

theorem C_still_material :
    materialSearchStatus.C_universalProducer = false := rfl

theorem E_still_material :
    materialSearchStatus.E_universalTargetHit = false := rfl

theorem R3_still_material :
    materialSearchStatus.R3_universalTransport = false := rfl

#print axioms P05.Hodge.basepointA_search_hits
#print axioms P05.Hodge.materialSearchGaps_count
#print axioms P05.Hodge.basepoint_fast_path_green
#print axioms P05.Hodge.C_still_material
#print axioms P05.Hodge.E_still_material
#print axioms P05.Hodge.R3_still_material

end P05.Hodge
