import MCore.BackwardAudit.R3AtomicSpecialization

namespace MCore.BackwardAudit

/-!
# R3 back-transport reduction

The cohomological recovery of the original class is not an independent
geometric residue.  Once pathwise parallel transport has an inverse along the
chosen path, back-transport of the transported input class is mechanically the
original class.  The remaining R3 geometry is cycle specialization plus
compatibility of its cycle class with this back-transport.
-/

theorem castCohomology_symm_cancel
    (G : GradedRationalHodgeData)
    {X Y : G.Variety} {n : Nat}
    (h : X = Y)
    (β : G.CohomologyQ Y n) :
    castCohomology G h (castCohomology G h.symm β) = β := by
  cases h
  rfl

/-- Standard path-groupoid/local-system input: reverse the chosen path and
    reverse parallel transport cancels forward transport. -/
structure ReverseTransportLaws
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  reverse :
    {b0 b1 : S.Base} →
    S.Path b0 b1 → S.Path b1 b0
  reverse_forward :
    ∀ {b0 b1 : S.Base}
      (γ : S.Path b0 b1)
      (β : G.CohomologyQ (S.Family b0) (2 * p)),
      S.parallelTransport (reverse γ)
        (S.parallelTransport γ β) = β

/-- Cohomological specialization/back-transport directly to the original
    variety X. -/
def backTransportToOriginal
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S)
    {y : S.Base}
    (γ : S.Path S.basepoint y)
    (β : G.CohomologyQ (S.Family y) (2 * p)) :
    G.CohomologyQ X (2 * p) :=
  castCohomology G S.fiberAtBasepoint
    (S.parallelTransport (R.reverse γ) β)

/-- Recovery of alpha is now proved, not assumed. -/
theorem backTransport_transportedAlpha
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S)
    {y : S.Base}
    (γ : S.Path S.basepoint y) :
    backTransportToOriginal R γ (S.transportedAlpha γ) = α := by
  unfold backTransportToOriginal
  unfold TypedVariationalGeometry.transportedAlpha
  rw [R.reverse_forward]
  unfold TypedVariationalGeometry.alphaAtBasepoint
  exact castCohomology_symm_cancel G S.fiberAtBasepoint α

/-- Linear laws for the standard cohomological back-transport.  These are
    logically separate from cycle specialization. -/
structure BackTransportLinearLaws
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S) : Prop where
  zero :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y),
      backTransportToOriginal R γ
        (M.zeroClass (X := S.Family y) (p := p)) =
      M.zeroClass
  add :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y)
      (a b : G.CohomologyQ (S.Family y) (2 * p)),
      backTransportToOriginal R γ (M.addClass a b) =
        M.addClass
          (backTransportToOriginal R γ a)
          (backTransportToOriginal R γ b)
  smul :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y)
      (r : M.Coeff)
      (a : G.CohomologyQ (S.Family y) (2 * p)),
      backTransportToOriginal R γ (M.smul r a) =
        M.smul r (backTransportToOriginal R γ a)

/-- The genuinely cycle-theoretic R3 input. -/
structure CycleSpecializationBackTransport
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S) where
  specializeCycle :
    {y : S.Base} →
    (γ : S.Path S.basepoint y) →
    G.CycleQ (S.Family y) p →
    G.CycleQ X p
  cycleClass_compat :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y)
      (Z : G.CycleQ (S.Family y) p),
      backTransportToOriginal R γ (M.cycleClass p Z) =
        M.cycleClass p (specializeCycle γ Z)

/-- The standard local-system laws plus cycle specialization construct the
    complete atomic R3 backend. -/
def atomicSpecializationOfBackTransport
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S)
    (L : BackTransportLinearLaws M R)
    (C : CycleSpecializationBackTransport M R) :
    DirectPathwiseSpecializationData M S :=
  {
    specializeClass := fun γ β => backTransportToOriginal R γ β
    specializeCycle := fun γ Z => C.specializeCycle γ Z
    zero_compat := L.zero
    add_compat := L.add
    smul_compat := L.smul
    cycleClass_compat := C.cycleClass_compat
    transportedAlpha_compat := backTransport_transportedAlpha R
  }

/-- R3 closes from the reduced standard backend. -/
theorem r3_transport_of_backTransport_backend
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S)
    (L : BackTransportLinearLaws M R)
    (C : CycleSpecializationBackTransport M R) :
    Nonempty (R3TransportContract M S) :=
  r3_transport_of_atomic_specialization
    (atomicSpecializationOfBackTransport R L C)

inductive R3ReducedResidueStatus where
  | provedInternal
  | standardLocalSystemInput
  | cycleGeometryInput
  deriving Repr, DecidableEq

structure R3ReducedFrontier where
  alphaRecovery : R3ReducedResidueStatus
  finiteCombinationLift : R3ReducedResidueStatus
  reverseTransport : R3ReducedResidueStatus
  transportLinearity : R3ReducedResidueStatus
  cycleSpecialization : R3ReducedResidueStatus
  cycleClassCompatibility : R3ReducedResidueStatus

def r3ReducedFrontier : R3ReducedFrontier :=
  {
    alphaRecovery := .provedInternal
    finiteCombinationLift := .provedInternal
    reverseTransport := .standardLocalSystemInput
    transportLinearity := .standardLocalSystemInput
    cycleSpecialization := .cycleGeometryInput
    cycleClassCompatibility := .cycleGeometryInput
  }

theorem r3_alpha_recovery_proved :
    r3ReducedFrontier.alphaRecovery = .provedInternal := rfl

#print axioms MCore.BackwardAudit.castCohomology_symm_cancel
#print axioms MCore.BackwardAudit.backTransport_transportedAlpha
#print axioms MCore.BackwardAudit.atomicSpecializationOfBackTransport
#print axioms MCore.BackwardAudit.r3_transport_of_backTransport_backend
#print axioms MCore.BackwardAudit.r3_alpha_recovery_proved

end MCore.BackwardAudit
