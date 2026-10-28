import MCore.P05.Hodge.KernelQuestionMatrix
import MCore.BackwardAudit.R2HardCore
import MCore.BackwardAudit.R1dArithmeticIntersection

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/--
Literal witness types for every remaining mathematical obligation.
No status label can close these types; only an inhabitant can.
-/
def Q5Witness
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  QbarIntersectsHodgeLocus S

def Q7Witness
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) : Type _ :=
  HodgeKernelQ1 M D

def Q8Witness
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) : Type _ :=
  HodgeKernelQ2 M D

def Q9Witness
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S)
    (Q2 : HodgeKernelQ2 M D) : Prop :=
  HodgeKernelQ3 M D Q2

/-- Q5 cannot be derived from SpreadData alone: the repo already has a spread
whose Hodge locus is nonempty but whose Qbar intersection is empty. -/
theorem Q5_not_forced_by_spread
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    ¬ Q5Witness (trivialSpreadNoQbar G X p α hX hα) := by
  exact trivialSpreadNoQbar_no_qbar_intersection

/-- Q7 and Q8 are merely data-production stages: their existence does not force
the target hit.  This is kernel-certified by the Bool countermodel. -/
theorem Q7_Q8_do_not_force_Q9 :
    Nonempty (Q7Witness kernelQCounterM kernelQCounterDescent) ∧
    Nonempty (Q8Witness kernelQCounterM kernelQCounterDescent) ∧
    ¬ Q9Witness kernelQCounterM kernelQCounterDescent kernelQCounterQ2 := by
  exact ⟨kernelQCounter_Q1_inhabited,
    kernelQCounter_Q2_inhabited,
    kernelQCounter_Q3_impossible⟩

/-- Q9 is sufficient for exact R2 once Q8 is inhabited. -/
theorem Q9_to_exact_R2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (Q2 : Q8Witness M D)
    (Q9 : Q9Witness M D Q2) :
    R2FiberAlgebraicityTarget M D :=
  hodgeKernelQ3_closes_R2 Q2 Q9

/--
The exact R2 target is not a hidden simplification in general: on the trivial
Qbar spread it is equivalent to the original concrete cycle-span endpoint.
-/
theorem exact_R2_can_be_endpoint
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    R2FiberAlgebraicityTarget M
      (trivialQbarDescent (G := G) (X := X) (p := p)
        (α := α) (hX := hX) (hα := hα)) ↔
      InConcreteCycleSpan M α := by
  exact r2_trivial_qbar_iff_original_span

inductive OpenWitnessKind where
  | arithmeticPoint
  | correspondenceGeometry
  | finiteAlgebraicSource
  | targetHit
  | universalHigherCodim
  deriving Repr, DecidableEq

def remainingWitnessKinds : List OpenWitnessKind :=
  [.arithmeticPoint, .correspondenceGeometry, .finiteAlgebraicSource,
   .targetHit, .universalHigherCodim]

theorem remainingWitnessKinds_count :
    remainingWitnessKinds.length = 5 := by decide

#print axioms P05.Hodge.Q5_not_forced_by_spread
#print axioms P05.Hodge.Q7_Q8_do_not_force_Q9
#print axioms P05.Hodge.Q9_to_exact_R2
#print axioms P05.Hodge.exact_R2_can_be_endpoint
#print axioms P05.Hodge.remainingWitnessKinds_count

end P05.Hodge
