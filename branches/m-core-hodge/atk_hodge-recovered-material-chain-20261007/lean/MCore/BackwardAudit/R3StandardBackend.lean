import MCore.BackwardAudit.R3BackTransport

namespace MCore.BackwardAudit

/-!
# R3 standard backend reduction

This module removes two more R3 bookkeeping residues.

1. Inverse cohomological transport is derived from ordinary groupoid laws for
   paths together with the already-existing composition/refl laws of
   parallelTransport.
2. Linearity of back-transport is derived from linearity of parallelTransport
   plus equality-cast functoriality of the concrete span operations.

The genuinely geometric R3 residue is then only:
  * specialize algebraic cycles back to X;
  * prove cycle class commutes with that specialization/back-transport.
-/

structure PathGroupoidLaws
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
  comp_reverse :
    ∀ {b0 b1 : S.Base} (γ : S.Path b0 b1),
      S.pathComp γ (reverse γ) = S.pathRefl b0
  reverse_comp :
    ∀ {b0 b1 : S.Base} (γ : S.Path b0 b1),
      S.pathComp (reverse γ) γ = S.pathRefl b1

def reverseTransportOfPathGroupoid
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : PathGroupoidLaws S) :
    ReverseTransportLaws S :=
  {
    reverse := P.reverse
    reverse_forward := by
      intro b0 b1 γ β
      rw [← S.parallelTransport_comp γ (P.reverse γ) β]
      rw [P.comp_reverse γ]
      exact S.parallelTransport_refl b0 β
  }

structure ParallelTransportLinearLaws
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop where
  zero :
    ∀ {b0 b1 : S.Base} (γ : S.Path b0 b1),
      S.parallelTransport γ
        (M.zeroClass (X := S.Family b0) (p := p)) =
      M.zeroClass
  add :
    ∀ {b0 b1 : S.Base} (γ : S.Path b0 b1)
      (a b : G.CohomologyQ (S.Family b0) (2 * p)),
      S.parallelTransport γ (M.addClass a b) =
        M.addClass
          (S.parallelTransport γ a)
          (S.parallelTransport γ b)
  smul :
    ∀ {b0 b1 : S.Base} (γ : S.Path b0 b1)
      (r : M.Coeff)
      (a : G.CohomologyQ (S.Family b0) (2 * p)),
      S.parallelTransport γ (M.smul r a) =
        M.smul r (S.parallelTransport γ a)

theorem castCohomology_zeroClass
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X Y : G.Variety} {p : Nat}
    (h : X = Y) :
    castCohomology G h (M.zeroClass (X := X) (p := p)) =
      M.zeroClass := by
  cases h
  rfl

theorem castCohomology_addClass
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X Y : G.Variety} {p : Nat}
    (h : X = Y)
    (a b : G.CohomologyQ X (2 * p)) :
    castCohomology G h (M.addClass a b) =
      M.addClass
        (castCohomology G h a)
        (castCohomology G h b) := by
  cases h
  rfl

theorem castCohomology_smul
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X Y : G.Variety} {p : Nat}
    (h : X = Y)
    (r : M.Coeff)
    (a : G.CohomologyQ X (2 * p)) :
    castCohomology G h (M.smul r a) =
      M.smul r (castCohomology G h a) := by
  cases h
  rfl

def backTransportLinearOfParallel
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S)
    (L : ParallelTransportLinearLaws M S) :
    BackTransportLinearLaws M R :=
  {
    zero := by
      intro y γ
      unfold backTransportToOriginal
      rw [L.zero]
      exact castCohomology_zeroClass M S.fiberAtBasepoint
    add := by
      intro y γ a b
      unfold backTransportToOriginal
      rw [L.add]
      exact castCohomology_addClass M S.fiberAtBasepoint
        (S.parallelTransport (R.reverse γ) a)
        (S.parallelTransport (R.reverse γ) b)
    smul := by
      intro y γ r a
      unfold backTransportToOriginal
      rw [L.smul]
      exact castCohomology_smul M S.fiberAtBasepoint r
        (S.parallelTransport (R.reverse γ) a)
  }

/-- The remaining geometric backend after standard local-system structure has
    been factored out. -/
structure CycleSpecializationGeometry
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

def cycleSpecializationBackTransportOfGeometry
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    (C : CycleSpecializationGeometry M R) :
    CycleSpecializationBackTransport M R :=
  {
    specializeCycle := C.specializeCycle
    cycleClass_compat := C.cycleClass_compat
  }

/-- Standard local-system laws + the two genuinely geometric cycle laws close
    R3. -/
theorem r3_transport_of_standard_backend
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (P : PathGroupoidLaws S)
    (L : ParallelTransportLinearLaws M S)
    (C : CycleSpecializationGeometry M (reverseTransportOfPathGroupoid P)) :
    Nonempty (R3TransportContract M S) := by
  let R := reverseTransportOfPathGroupoid P
  exact r3_transport_of_backTransport_backend
    R
    (backTransportLinearOfParallel R L)
    (cycleSpecializationBackTransportOfGeometry C)

inductive R3StandardFrontierStatus where
  | provedInternal
  | standardLocalSystem
  | geometricCycleResidue
  deriving Repr, DecidableEq

structure R3StandardFrontier where
  inverseTransportDerivation : R3StandardFrontierStatus
  alphaRecovery : R3StandardFrontierStatus
  backTransportLinearityDerivation : R3StandardFrontierStatus
  pathGroupoidLaws : R3StandardFrontierStatus
  parallelTransportLinearity : R3StandardFrontierStatus
  cycleSpecialization : R3StandardFrontierStatus
  cycleClassCompatibility : R3StandardFrontierStatus

def r3StandardFrontier : R3StandardFrontier :=
  {
    inverseTransportDerivation := .provedInternal
    alphaRecovery := .provedInternal
    backTransportLinearityDerivation := .provedInternal
    pathGroupoidLaws := .standardLocalSystem
    parallelTransportLinearity := .standardLocalSystem
    cycleSpecialization := .geometricCycleResidue
    cycleClassCompatibility := .geometricCycleResidue
  }

theorem r3_standard_internal_reductions_proved :
    r3StandardFrontier.inverseTransportDerivation = .provedInternal ∧
    r3StandardFrontier.alphaRecovery = .provedInternal ∧
    r3StandardFrontier.backTransportLinearityDerivation = .provedInternal := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms MCore.BackwardAudit.reverseTransportOfPathGroupoid
#print axioms MCore.BackwardAudit.castCohomology_zeroClass
#print axioms MCore.BackwardAudit.castCohomology_addClass
#print axioms MCore.BackwardAudit.castCohomology_smul
#print axioms MCore.BackwardAudit.backTransportLinearOfParallel
#print axioms MCore.BackwardAudit.r3_transport_of_standard_backend
#print axioms MCore.BackwardAudit.r3_standard_internal_reductions_proved

end MCore.BackwardAudit
