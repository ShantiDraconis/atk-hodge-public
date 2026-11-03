import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR1dAudit

open MCore
open MCore.BackwardAudit

/-- Exact logical residue carried by the frozen R1d contract. This is only an
    unfolding of the existing typed data: a Qbar point plus a path along which
    the transported input class is Hodge. -/
def R1dExactResidue
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ y : S.Base, ∃ γ : S.Path S.basepoint y,
    S.isHodgeAlong γ ∧ S.fieldOfDefinition.isDefinedOverQbar y

/-- R1d is exactly the existence of the witness already encoded by the frozen
    contract. No algebraic-cycle conclusion appears here. -/
theorem r1d_contract_iff_exact_residue
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (R1DescentPointContract S) ↔ R1dExactResidue S := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.point.y, C.point.path, C.point.y_is_hodge,
      C.point.y_is_defined_over_Qbar⟩
  · rintro ⟨y, γ, hHodge, hQbar⟩
    exact ⟨{
      point := {
        y := y
        path := γ
        y_is_hodge := hHodge
        y_is_defined_over_Qbar := hQbar
      }
    }⟩

/-- Type transport preserves the existing K13 Hodge predicate. -/
theorem isTypePP_castCohomology
    {G : GradedRationalHodgeData}
    {X Y : G.Variety}
    {p : Nat}
    {β : G.CohomologyQ X (2 * p)}
    (h : X = Y)
    (hβ : G.isTypePP p β) :
    G.isTypePP p (castCohomology G h β) := by
  cases h
  exact hβ

/-- The original input class is automatically Hodge along the reflexive path
    at the distinguished fiber. Thus the basepoint attack leaves only the
    field-of-definition predicate. -/
theorem basepoint_is_hodge
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    S.isHodgeAlong (S.pathRefl S.basepoint) := by
  unfold TypedVariationalGeometry.isHodgeAlong
  unfold TypedVariationalGeometry.transportedAlpha
  rw [S.parallelTransport_refl]
  exact isTypePP_castCohomology S.fiberAtBasepoint.symm hα

/-- Sufficient R1d closure at the basepoint. This does not assert that an
    arbitrary complex input variety has Qbar field of definition. -/
def r1dContractOfBasepointQbar
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    R1DescentPointContract S :=
  {
    point := {
      y := S.basepoint
      path := S.pathRefl S.basepoint
      y_is_hodge := basepoint_is_hodge S
      y_is_defined_over_Qbar := hQbar
    }
  }

/-- A-side: if the distinguished point is Qbar, R1d closes without any
    further Hodge-locus theorem. -/
theorem basepoint_qbar_closes_r1d
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (hQbar : S.fieldOfDefinition.isDefinedOverQbar S.basepoint) :
    Nonempty (R1DescentPointContract S) :=
  ⟨r1dContractOfBasepointQbar S hQbar⟩

/-- B-side: the frozen countermodel still blocks any theorem deriving R1d from
    SpreadData alone. -/
theorem trivial_spread_blocks_unconditional_r1d
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    ¬ Nonempty
      (R1DescentPointContract
        (trivialSpreadNoQbar G X p α hX hα)) := by
  intro h
  rcases h with ⟨C⟩
  exact
    (trivial_spread_has_no_qbar_hodge_point
      (G := G) (M := M) (X := X) (p := p) (α := α)
      (hX := hX) (hα := hα)) ⟨C.point⟩

/-- The first open condition exposed by the basepoint route. -/
def BasepointQbarResidue
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  S.fieldOfDefinition.isDefinedOverQbar S.basepoint

theorem basepoint_residue_suffices
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    BasepointQbarResidue S →
      Nonempty (R1DescentPointContract S) :=
  basepoint_qbar_closes_r1d S

#print axioms HodgeR1dAudit.r1d_contract_iff_exact_residue
#print axioms HodgeR1dAudit.isTypePP_castCohomology
#print axioms HodgeR1dAudit.basepoint_is_hodge
#print axioms HodgeR1dAudit.basepoint_qbar_closes_r1d
#print axioms HodgeR1dAudit.trivial_spread_blocks_unconditional_r1d
#print axioms HodgeR1dAudit.basepoint_residue_suffices

end HodgeR1dAudit
