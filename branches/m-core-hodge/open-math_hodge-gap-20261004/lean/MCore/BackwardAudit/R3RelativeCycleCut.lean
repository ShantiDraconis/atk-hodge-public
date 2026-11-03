import MCore.BackwardAudit.R3StandardBackend

namespace MCore.BackwardAudit

/-!
# R3 relative-cycle cut

Classical specialization along a trait/DVR is not automatically a transport
between two arbitrary closed fibers connected only by a path.  The missing
geometric content is therefore split into two independent residues:

* R3a: the cycle on the selected fiber extends to relative cycle data that
  reaches the original fiber;
* R3b: the cycle-class map of that relative cycle is compatible with
  cohomological back-transport.

Once R3a and R3b are supplied, the previously certified standard backend closes
R3 mechanically.
-/

/-- Endpoint data for a relative cycle spanning the selected fiber and the
    original fiber.  This structure is only an interface; it asserts no
    existence theorem. -/
structure RelativeCycleEndpointData
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    (γ : S.Path S.basepoint y) where
  RelativeCycle : Type
  sourceCycle : RelativeCycle → G.CycleQ (S.Family y) p
  targetCycle : RelativeCycle → G.CycleQ X p

/-- R3a: every source-fiber cycle under consideration admits a relative
    extension whose source restriction is exactly that cycle. -/
structure RelativeCycleExtension
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    (E : RelativeCycleEndpointData (M := M) (S := S) (R := R) γ) where
  extendCycle :
    G.CycleQ (S.Family y) p → E.RelativeCycle
  source_extend :
    ∀ Z : G.CycleQ (S.Family y) p,
      E.sourceCycle (extendCycle Z) = Z

/-- R3b: cycle class of every relative cycle is compatible with the
    cohomological back-transport from the selected fiber to X. -/
structure RelativeCycleClassCompatibility
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    {y : S.Base}
    {γ : S.Path S.basepoint y}
    (E : RelativeCycleEndpointData (M := M) (S := S) (R := R) γ) : Prop where
  compatible :
    ∀ T : E.RelativeCycle,
      backTransportToOriginal R γ (M.cycleClass p (E.sourceCycle T)) =
        M.cycleClass p (E.targetCycle T)

/-- A pathwise relative-cycle backend packages the endpoint carrier together
    with the two exact geometric residues R3a and R3b. -/
structure RelativeCycleBackend
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    (R : ReverseTransportLaws S) where
  endpoint :
    {y : S.Base} →
    (γ : S.Path S.basepoint y) →
    RelativeCycleEndpointData (M := M) (S := S) (R := R) γ
  extension :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y),
      RelativeCycleExtension (endpoint γ)
  classCompatibility :
    ∀ {y : S.Base} (γ : S.Path S.basepoint y),
      RelativeCycleClassCompatibility (endpoint γ)

/-- R3a + R3b construct the exact cycle-specialization geometry required by
    the standard backend. -/
def cycleSpecializationGeometryOfRelativeBackend
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {R : ReverseTransportLaws S}
    (B : RelativeCycleBackend M R) :
    CycleSpecializationGeometry M R :=
  {
    specializeCycle := by
      intro y γ Z
      let E := B.endpoint γ
      let Ext := B.extension γ
      exact E.targetCycle (Ext.extendCycle Z)
    cycleClass_compat := by
      intro y γ Z
      let E := B.endpoint γ
      let Ext := B.extension γ
      let Compat := B.classCompatibility γ
      have h :=
        Compat.compatible (Ext.extendCycle Z)
      rw [Ext.source_extend Z] at h
      exact h
  }

/-- Relative-cycle extension + class compatibility close R3 once the standard
    local-system laws are available. -/
theorem r3_transport_of_relative_cycle_backend
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
    (B : RelativeCycleBackend M (reverseTransportOfPathGroupoid P)) :
    Nonempty (R3TransportContract M S) :=
  r3_transport_of_standard_backend
    P L (cycleSpecializationGeometryOfRelativeBackend B)

inductive R3RelativeCutStatus where
  | provedReduction
  | openCycleExtension
  | openClassCompatibility
  deriving Repr, DecidableEq

structure R3RelativeCutFrontier where
  reductionToRelativeCycles : R3RelativeCutStatus
  relativeCycleExtension : R3RelativeCutStatus
  cycleClassCompatibility : R3RelativeCutStatus

def r3RelativeCutFrontier : R3RelativeCutFrontier :=
  {
    reductionToRelativeCycles := .provedReduction
    relativeCycleExtension := .openCycleExtension
    cycleClassCompatibility := .openClassCompatibility
  }

theorem r3_relative_cut_reduction_proved :
    r3RelativeCutFrontier.reductionToRelativeCycles = .provedReduction := rfl

theorem r3_relative_cycle_extension_open :
    r3RelativeCutFrontier.relativeCycleExtension = .openCycleExtension := rfl

theorem r3_relative_cycle_class_compat_open :
    r3RelativeCutFrontier.cycleClassCompatibility = .openClassCompatibility := rfl

#print axioms MCore.BackwardAudit.cycleSpecializationGeometryOfRelativeBackend
#print axioms MCore.BackwardAudit.r3_transport_of_relative_cycle_backend
#print axioms MCore.BackwardAudit.r3_relative_cut_reduction_proved
#print axioms MCore.BackwardAudit.r3_relative_cycle_extension_open
#print axioms MCore.BackwardAudit.r3_relative_cycle_class_compat_open

end MCore.BackwardAudit
