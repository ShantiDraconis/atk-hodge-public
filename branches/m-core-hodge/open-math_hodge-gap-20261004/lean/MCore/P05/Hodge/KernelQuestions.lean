import MCore.P05.Hodge.DivisorCorrespondenceKernelPressure

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/-- Q1: correspondence geometry exists, but no finite source or target hit yet. -/
structure HodgeKernelQ1
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) where
  hp : 2 ≤ p
  sourceVariety : G.Variety
  sourceSmoothProjective : G.isSmoothProjective sourceVariety
  Correspondence : Type
  pushDivisor :
    Correspondence →
      G.CycleQ sourceVariety 1 →
      G.CycleQ (S.Family D.point.y) p
  pushClass :
    Correspondence →
      G.CohomologyQ sourceVariety (2 * 1) →
      G.CohomologyQ (S.Family D.point.y) (2 * p)
  cycleClass_compat :
    ∀ (Γ : Correspondence) (z : G.CycleQ sourceVariety 1),
      pushClass Γ (M.cycleClass 1 z) =
        M.cycleClass p (pushDivisor Γ z)

/-- Q2: Q1 plus an explicit finite algebraic source. -/
structure HodgeKernelQ2
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (D : R1DescentPointContract S) extends HodgeKernelQ1 M D where
  terms :
    List (M.Coeff × Correspondence × G.CycleQ sourceVariety 1)

/-- Q3: the finite pushed divisor source hits the transported Hodge class. -/
def HodgeKernelQ3
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
  (Q2.terms.map (fun t => (t.1, Q2.pushDivisor t.2.1 t.2.2))).foldr
      (fun t acc =>
        M.addClass (M.smul t.1 (M.cycleClass p t.2)) acc)
      M.zeroClass =
    S.transportedAlpha D.point.path

/-- Q1 + Q2 + Q3 are exactly sufficient to construct the pressure producer. -/
def hodgeKernelQuestions_toProducer
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
    DivisorCorrespondenceKernelProducer M D :=
  {
    hp := Q2.hp
    sourceVariety := Q2.sourceVariety
    sourceSmoothProjective := Q2.sourceSmoothProjective
    Correspondence := Q2.Correspondence
    pushDivisor := Q2.pushDivisor
    pushClass := Q2.pushClass
    cycleClass_compat := Q2.cycleClass_compat
    terms := Q2.terms
    hit := Q3
  }

/-- Therefore Q3 is the last question before exact R2. -/
theorem hodgeKernelQ3_closes_R2
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
  divisorCorrespondenceKernelProducer_closes_R2_target
    (hodgeKernelQuestions_toProducer Q2 Q3)

/-!
Fail-closed countermodel:
Q1 and Q2 are inhabited, but every algebraic cycle class is false while the
transported Hodge class is true.  Hence Q3 is impossible.
-/

def kernelQCounterG : GradedRationalHodgeData :=
  {
    Variety := Unit
    CohomologyQ := fun _ _ => Bool
    CycleQ := fun _ _ => Unit
    isSmoothProjective := fun _ => True
    isTypePP := fun _ _ => True
    inCycleClassSpan := fun _ _ => False
  }

def kernelQCounterM : CycleSpanMechanics kernelQCounterG :=
  {
    Coeff := Bool
    zero := false
    add := Bool.or
    smul := fun a b => a && b
    addClass := Bool.or
    zeroClass := false
    cycleClass := fun _ _ => false
  }

def kernelQCounterSpread :
    SpreadData kernelQCounterG () 2 true True.intro True.intro :=
  {
    Base := Unit
    basepoint := ()
    Family := fun _ => ()
    fiberAtBasepoint := rfl
    Path := fun _ _ => Unit
    pathRefl := fun _ => ()
    pathComp := fun _ _ => ()
    parallelTransport := fun _ b => b
    parallelTransport_refl := by intro b β; rfl
    parallelTransport_comp := by
      intro b0 b1 b2 γ01 γ12 β
      rfl
    fieldOfDefinition := {
      isDefinedOverQbar := fun _ => True
    }
  }

def kernelQCounterDescent :
    R1DescentPointContract kernelQCounterSpread :=
  {
    point := {
      y := ()
      path := ()
      y_is_hodge := True.intro
      y_is_defined_over_Qbar := True.intro
    }
  }

def kernelQCounterQ1 :
    HodgeKernelQ1 kernelQCounterM kernelQCounterDescent :=
  {
    hp := by decide
    sourceVariety := ()
    sourceSmoothProjective := True.intro
    Correspondence := Unit
    pushDivisor := fun _ _ => ()
    pushClass := fun _ _ => false
    cycleClass_compat := by
      intro Γ z
      rfl
  }

def kernelQCounterQ2 :
    HodgeKernelQ2 kernelQCounterM kernelQCounterDescent :=
  {
    toHodgeKernelQ1 := kernelQCounterQ1
    terms := []
  }

theorem kernelQCounter_Q1_inhabited :
    Nonempty (HodgeKernelQ1 kernelQCounterM kernelQCounterDescent) :=
  ⟨kernelQCounterQ1⟩

theorem kernelQCounter_Q2_inhabited :
    Nonempty (HodgeKernelQ2 kernelQCounterM kernelQCounterDescent) :=
  ⟨kernelQCounterQ2⟩

theorem kernelQCounter_Q3_impossible :
    ¬ HodgeKernelQ3 kernelQCounterM kernelQCounterDescent kernelQCounterQ2 := by
  intro h
  change false = true at h
  cases h

#print axioms P05.Hodge.hodgeKernelQ3_closes_R2
#print axioms P05.Hodge.kernelQCounter_Q1_inhabited
#print axioms P05.Hodge.kernelQCounter_Q2_inhabited
#print axioms P05.Hodge.kernelQCounter_Q3_impossible

end P05.Hodge
