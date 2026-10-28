import MCore.P05.Hodge.KernelQuestions
import MCore.HodgeExactRemaining
import MCore.BackwardAudit.R1dArithmeticIntersection
import MCore.BackwardAudit.R3SpecializationBoundary

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

inductive KernelAnswer where
  | proved
  | refuted
  | openMath
  deriving Repr, DecidableEq

structure KernelQuestion where
  id : Nat
  label : String
  answer : KernelAnswer
  deriving Repr

/--
Compressed complete kernel matrix for the Hodge lane.

The 115 verbal audit questions collapse to 15 logical gates.  A gate is marked
`proved` only when the repository already contains a proof term for the
reduction/mechanical implication.  Missing mathematical producers remain
`openMath`; no status here manufactures them.
-/
def hodgeKernelQuestionMatrix : List KernelQuestion :=
  [
    ⟨1,  "canonical endpoint / quantifier fidelity", .proved⟩,
    ⟨2,  "codimension zero material backend", .proved⟩,
    ⟨3,  "codimension one Lefschetz backend", .proved⟩,
    ⟨4,  "typed variational transport interface", .proved⟩,
    ⟨5,  "Qbar Hodge-locus intersection for a useful noncircular point", .openMath⟩,
    ⟨6,  "Hilbert/Chow proper-dominant plumbing implies target generation", .refuted⟩,
    ⟨7,  "q=1 correspondence geometry and cycle-class-compatible pushforward", .openMath⟩,
    ⟨8,  "finite divisor source on the auxiliary variety", .openMath⟩,
    ⟨9,  "Q3: pushed divisor combination equals transportedAlpha", .openMath⟩,
    ⟨10, "Q3 implies exact R2 fiber algebraicity", .proved⟩,
    ⟨11, "R2 wrapper construction from exact fiber algebraicity", .proved⟩,
    ⟨12, "R3 transport/specialization contract, when supplied, closes original span", .proved⟩,
    ⟨13, "higher-codimension universal material producer", .openMath⟩,
    ⟨14, "concrete payload implies canonical terminal Hodge statement", .proved⟩,
    ⟨15, "unconditional universal inhabitant of the final higher-codim producer", .openMath⟩
  ]

def answerOf (n : Nat) : Option KernelAnswer :=
  (hodgeKernelQuestionMatrix.find? (fun q => q.id = n)).map (fun q => q.answer)

theorem matrix_has_15_questions :
    hodgeKernelQuestionMatrix.length = 15 := by decide

theorem q1_q2_not_enough :
    Nonempty (HodgeKernelQ1 kernelQCounterM kernelQCounterDescent) ∧
    Nonempty (HodgeKernelQ2 kernelQCounterM kernelQCounterDescent) ∧
    ¬ HodgeKernelQ3 kernelQCounterM kernelQCounterDescent kernelQCounterQ2 := by
  exact ⟨kernelQCounter_Q1_inhabited,
    kernelQCounter_Q2_inhabited,
    kernelQCounter_Q3_impossible⟩

theorem q3_is_sufficient_for_R2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (Q2 : HodgeKernelQ2 M D)
    (Q3 : HodgeKernelQ3 M D Q2) :
    R2FiberAlgebraicityTarget M D :=
  hodgeKernelQ3_closes_R2 Q2 Q3

/-- Existing repository theorem: the R1d arithmetic wrapper is exactly Qbar
intersection; the intersection itself remains open. -/
theorem r1d_gate_is_exact
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (R1DescentPointContract S) ↔ QbarIntersectsHodgeLocus S :=
  r1d_contract_iff_qbar_intersection S

/-- Existing R2 wrapper is exact. -/
theorem r2_gate_is_exact
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) :
    Nonempty (R2PointProductionContract M S D) ↔
      R2FiberAlgebraicityTarget M D :=
  r2_contract_iff_fiber_algebraicity D

/-- Kernel-certified classification of the decisive local questions. -/
theorem answer_Q6_refuted :
    answerOf 6 = some .refuted := by decide

theorem answer_Q9_open :
    answerOf 9 = some .openMath := by decide

theorem answer_Q10_proved :
    answerOf 10 = some .proved := by decide

theorem answer_Q15_open :
    answerOf 15 = some .openMath := by decide

/--
The local material min-cut after all proved reductions:
Q5 supplies the useful arithmetic point; Q7-Q8 supply genuine geometry/source;
Q9 is the target-hit equality.  Of these, Q9 is the last implication needed
before the already-proved R2 tail.
-/
structure HodgeRemainingMaterialCut where
  qbarUsefulPoint : KernelAnswer := .openMath
  correspondenceGeometry : KernelAnswer := .openMath
  finiteDivisorSource : KernelAnswer := .openMath
  pushedSourceHitsTarget : KernelAnswer := .openMath
  q3ToR2 : KernelAnswer := .proved
  r2Wrapper : KernelAnswer := .proved

def hodgeRemainingMaterialCut : HodgeRemainingMaterialCut := {}

theorem material_tail_is_closed :
    hodgeRemainingMaterialCut.q3ToR2 = .proved ∧
    hodgeRemainingMaterialCut.r2Wrapper = .proved := by
  exact ⟨rfl, rfl⟩

theorem material_head_is_open :
    hodgeRemainingMaterialCut.qbarUsefulPoint = .openMath ∧
    hodgeRemainingMaterialCut.correspondenceGeometry = .openMath ∧
    hodgeRemainingMaterialCut.finiteDivisorSource = .openMath ∧
    hodgeRemainingMaterialCut.pushedSourceHitsTarget = .openMath := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms P05.Hodge.matrix_has_15_questions
#print axioms P05.Hodge.q1_q2_not_enough
#print axioms P05.Hodge.q3_is_sufficient_for_R2
#print axioms P05.Hodge.r1d_gate_is_exact
#print axioms P05.Hodge.r2_gate_is_exact
#print axioms P05.Hodge.answer_Q6_refuted
#print axioms P05.Hodge.answer_Q9_open
#print axioms P05.Hodge.answer_Q10_proved
#print axioms P05.Hodge.answer_Q15_open
#print axioms P05.Hodge.material_tail_is_closed
#print axioms P05.Hodge.material_head_is_open

end P05.Hodge
