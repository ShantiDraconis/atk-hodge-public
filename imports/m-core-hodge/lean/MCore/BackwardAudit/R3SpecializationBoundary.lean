import MCore.BackwardAudit.R3Contract

namespace MCore.BackwardAudit

/-!
# R3 specialization boundary

This file closes the missing *type-interface* part of R3 without claiming the
geometric specialization theorem.  The remaining mathematical input is made
explicit as a compatibility law between specialization of finite cycle
combinations and cohomological transport.
-/

/-- Pure transport of a cycle across equality of the variety index. -/
def castCycle
    (G : GradedRationalHodgeData)
    {X Y : G.Variety} {p : Nat}
    (h : X = Y) :
    G.CycleQ X p → G.CycleQ Y p := by
  cases h
  exact id

/-- Pure transport of a finite cycle combination across equality of varieties. -/
def castCycleCombination
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X Y : G.Variety} {p : Nat}
    (h : X = Y) :
    CycleCombination G M X p → CycleCombination G M Y p := by
  cases h
  exact id

/-- Typed specialization operation for cycle combinations along one branch of
    a spread.  Existence of a geometrically meaningful instance is NOT proved
    here; this structure is the exact interface that R3 needs. -/
structure CycleSpecializationInterface
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) where
  specializeToBase :
    {y : S.Base} →
    S.Path S.basepoint y →
    CycleCombination G M (S.Family y) p →
    CycleCombination G M (S.Family S.basepoint) p

/-- Exact mathematical residue for R3: specialization must be compatible with
    the cycle-class realization and the pathwise cohomological transport of
    THIS alpha. -/
structure CycleClassSpecializationCompatibility
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (Spec : CycleSpecializationInterface M S) : Prop where
  compatible :
    ∀ {y : S.Base}
      (γ : S.Path S.basepoint y)
      (C : CycleCombination G M (S.Family y) p),
      C.eval M = S.transportedAlpha γ →
      (castCycleCombination (G := G) (M := M)
        S.fiberAtBasepoint
        (Spec.specializeToBase γ C)).eval M = α

/-- The specialization operation plus the single compatibility law constructs
    the exact R3 contract. -/
def r3TransportOfSpecialization
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (Spec : CycleSpecializationInterface M S)
    (Compat : CycleClassSpecializationCompatibility Spec) :
    R3TransportContract M S :=
  {
    transport := by
      intro P
      refine ⟨
        castCycleCombination (G := G) (M := M)
          S.fiberAtBasepoint
          (Spec.specializeToBase P.path P.combination),
        ?_
      ⟩
      exact Compat.compatible P.path P.combination P.combination_class
  }

/-- The exact R3 mathematical payload after all bookkeeping has been typed. -/
def R3SpecializationPayload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ Spec : CycleSpecializationInterface M S,
    CycleClassSpecializationCompatibility Spec

/-- A genuine proof of the specialization payload closes R3 mechanically. -/
theorem r3_payload_closes_transport
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (h : R3SpecializationPayload M S) :
    Nonempty (R3TransportContract M S) := by
  rcases h with ⟨Spec, Compat⟩
  exact ⟨r3TransportOfSpecialization Spec Compat⟩

inductive R3SpecializationStatus where
  | typedInterfaceClosed
  | externalGeometryRequired
  | openMathematics
  deriving Repr, DecidableEq

structure R3SpecializationFrontier where
  cycleSpecializationType : R3SpecializationStatus
  cycleSpreadType : R3SpecializationStatus
  parameterSpaceType : R3SpecializationStatus
  flatnessPropernessType : R3SpecializationStatus
  specializationPayload : R3SpecializationStatus

/-- Type-level gaps are no longer ambiguous.  The actual existence/compatibility
    payload remains open mathematics. -/
def r3SpecializationFrontier : R3SpecializationFrontier :=
  {
    cycleSpecializationType := .typedInterfaceClosed
    cycleSpreadType := .typedInterfaceClosed
    parameterSpaceType := .typedInterfaceClosed
    flatnessPropernessType := .typedInterfaceClosed
    specializationPayload := .openMathematics
  }

theorem r3_specialization_types_closed :
    r3SpecializationFrontier.cycleSpecializationType = .typedInterfaceClosed ∧
    r3SpecializationFrontier.cycleSpreadType = .typedInterfaceClosed ∧
    r3SpecializationFrontier.parameterSpaceType = .typedInterfaceClosed ∧
    r3SpecializationFrontier.flatnessPropernessType = .typedInterfaceClosed := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem r3_specialization_payload_still_open :
    r3SpecializationFrontier.specializationPayload = .openMathematics := rfl

#print axioms MCore.BackwardAudit.castCycle
#print axioms MCore.BackwardAudit.castCycleCombination
#print axioms MCore.BackwardAudit.r3TransportOfSpecialization
#print axioms MCore.BackwardAudit.r3_payload_closes_transport
#print axioms MCore.BackwardAudit.r3_specialization_types_closed
#print axioms MCore.BackwardAudit.r3_specialization_payload_still_open

end MCore.BackwardAudit
