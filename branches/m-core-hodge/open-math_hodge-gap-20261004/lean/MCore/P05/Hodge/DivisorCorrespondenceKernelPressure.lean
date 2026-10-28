import MCore.HodgeGeometricBackends
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary

namespace P05.Hodge

open MCore
open MCore.BackwardAudit

/--
Kernel-pressure form of the q=1 correspondence route.

This does not assert existence.  It forces the kernel to check that an
explicit finite family of pushed divisor cycles whose cycle classes reconstruct
the transported class is sufficient to build the exact R2 contract.
-/
structure DivisorCorrespondenceKernelProducer
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
  terms :
    List (M.Coeff × Correspondence × G.CycleQ sourceVariety 1)
  hit :
    (terms.map (fun t => (t.1, pushDivisor t.2.1 t.2.2))).foldr
        (fun t acc =>
          M.addClass (M.smul t.1 (M.cycleClass p t.2)) acc)
        M.zeroClass =
      S.transportedAlpha D.point.path

/-- The explicit pushed-divisor data gives the exact concrete fibre span. -/
theorem divisorCorrespondenceKernelProducer_closes_R2_target
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (K : DivisorCorrespondenceKernelProducer M D) :
    R2FiberAlgebraicityTarget M D := by
  refine ⟨
    ⟨K.terms.map (fun t => (t.1, K.pushDivisor t.2.1 t.2.2))⟩,
    ?_
  ⟩
  exact K.hit

/-- Stronger pressure: construct the actual R2 contract consumed downstream. -/
def DivisorCorrespondenceKernelProducer.toR2Contract
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (K : DivisorCorrespondenceKernelProducer M D) :
    R2PointProductionContract M S D := by
  let C : CycleCombination G M (S.Family D.point.y) p :=
    ⟨K.terms.map (fun t =>
      (t.1, K.pushDivisor t.2.1 t.2.2))⟩
  have hC : C.eval M = S.transportedAlpha D.point.path := by
    change
      (K.terms.map (fun t =>
        (t.1, K.pushDivisor t.2.1 t.2.2))).foldr
          (fun t acc =>
            M.addClass (M.smul t.1 (M.cycleClass p t.2)) acc)
          M.zeroClass =
        S.transportedAlpha D.point.path
    exact K.hit
  exact {
    produceCycle := {
      combination := C
      combination_class := hC
    }
  }

/-- q=1 is genuinely lower codimension for every pressure instance. -/
theorem divisorCorrespondenceKernelProducer_q1_lt_p
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (K : DivisorCorrespondenceKernelProducer M D) :
    1 < p :=
  Nat.lt_of_lt_of_le (by decide : 1 < 2) K.hp

/--
Lefschetz (1,1) can supply concrete algebraicity on the auxiliary source.
This theorem does not manufacture the correspondence or the target-hit equality.
-/
theorem divisorCorrespondenceKernelProducer_source_algebraic
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {D : R1DescentPointContract S}
    (K : DivisorCorrespondenceKernelProducer M D)
    (L : Lefschetz11DivisorBackend G M)
    (β : G.CohomologyQ K.sourceVariety (2 * 1))
    (hβ : G.isTypePP 1 β) :
    InConcreteCycleSpan M β :=
  L.toConcreteLaw.algebraic
    K.sourceVariety β K.sourceSmoothProjective hβ

#check DivisorCorrespondenceKernelProducer
#check DivisorCorrespondenceKernelProducer.hit
#check DivisorCorrespondenceKernelProducer.toR2Contract
#print axioms P05.Hodge.divisorCorrespondenceKernelProducer_closes_R2_target
#print axioms P05.Hodge.DivisorCorrespondenceKernelProducer.toR2Contract
#print axioms P05.Hodge.divisorCorrespondenceKernelProducer_q1_lt_p
#print axioms P05.Hodge.divisorCorrespondenceKernelProducer_source_algebraic

end P05.Hodge
