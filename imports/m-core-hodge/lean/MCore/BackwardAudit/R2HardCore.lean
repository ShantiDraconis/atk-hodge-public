import MCore.K18
import MCore.BackwardAudit.R2FiberAlgebraicityBoundary

namespace MCore.BackwardAudit

/-!
# R2 hard-core regression

A constant Qbar spread shows that the R2 residue is not auxiliary bookkeeping.
For the trivial family, the selected-fiber algebraicity target reduces exactly
to algebraicity of the original class.  Therefore a generic R2 solver would
already solve the concrete Hodge endpoint for arbitrary input classes.
-/

def trivialSpreadQbar
    (G : GradedRationalHodgeData)
    (X : G.Variety)
    (p : Nat)
    (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X)
    (hα : G.isTypePP p α) :
    SpreadData G X p α hX hα :=
  {
    Base := Unit
    basepoint := ()
    Family := fun _ => X
    fiberAtBasepoint := rfl
    Path := fun _ _ => Unit
    pathRefl := fun _ => ()
    pathComp := fun _ _ => ()
    parallelTransport := fun _ β => β
    parallelTransport_refl := by
      intro b β
      rfl
    parallelTransport_comp := by
      intro b0 b1 b2 γ01 γ12 β
      rfl
    fieldOfDefinition :=
      { isDefinedOverQbar := fun _ => True }
  }

def trivialQbarDescent
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    R1DescentPointContract (trivialSpreadQbar G X p α hX hα) :=
  {
    point := {
      y := ()
      path := ()
      y_is_hodge := by
        exact hα
      y_is_defined_over_Qbar := True.intro
    }
  }

theorem trivial_qbar_transportedAlpha_eq
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    (trivialSpreadQbar G X p α hX hα).transportedAlpha
      (trivialQbarDescent (G := G) (X := X) (p := p)
        (α := α) (hX := hX) (hα := hα)).point.path = α := by
  rfl

/-- On a constant Qbar family, R2 is exactly the original concrete
    algebraicity endpoint. -/
theorem r2_trivial_qbar_iff_original_span
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
  unfold R2FiberAlgebraicityTarget
  rw [trivial_qbar_transportedAlpha_eq]

/-- Thus closing R2 uniformly would close the concrete algebraicity problem
    even on the constant-family regression instance. -/
theorem r2_solver_on_trivial_qbar_yields_original_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (hR2 :
      R2FiberAlgebraicityTarget M
        (trivialQbarDescent (G := G) (X := X) (p := p)
          (α := α) (hX := hX) (hα := hα))) :
    InConcreteCycleSpan M α :=
  (r2_trivial_qbar_iff_original_span).1 hR2


/-- Universal R2 payload restricted to the constant Qbar regression family. -/
def TrivialQbarR2Payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p))
    (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      R2FiberAlgebraicityTarget M
        (trivialQbarDescent (G := G) (X := X) (p := p)
          (α := α) (hX := hX) (hα := hα))

/-- Exact hard-core theorem: solving R2 even only on the constant Qbar
    regression instances is equivalent to the full concrete algebraicity
    payload. -/
theorem trivial_qbar_r2_payload_iff_concrete_payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    TrivialQbarR2Payload M ↔ ConcreteAlgebraicityPayload M := by
  constructor
  · intro h X p α hX hα
    exact (r2_trivial_qbar_iff_original_span).1 (h X p α hX hα)
  · intro h X p α hX hα
    exact (r2_trivial_qbar_iff_original_span).2 (h X p α hX hα)

inductive R2HardCoreStatus where
  | endpointEquivalent
  | openMathematics
  deriving Repr, DecidableEq

def r2HardCoreStatus : R2HardCoreStatus := .endpointEquivalent

theorem r2_hard_core_is_endpoint :
    r2HardCoreStatus = .endpointEquivalent := rfl

#print axioms MCore.BackwardAudit.trivial_qbar_transportedAlpha_eq
#print axioms MCore.BackwardAudit.r2_trivial_qbar_iff_original_span
#print axioms MCore.BackwardAudit.r2_solver_on_trivial_qbar_yields_original_span
#print axioms MCore.BackwardAudit.trivial_qbar_r2_payload_iff_concrete_payload
#print axioms MCore.BackwardAudit.r2_hard_core_is_endpoint

end MCore.BackwardAudit
