import MCore.BackwardAudit.R2HardCore
import MCore.BackwardAudit.R3Contract

namespace MCore.BackwardAudit

/-!
# R3 on the constant Qbar regression spread

The constant Qbar spread already used by the R2 hard-core audit has no genuine
variation: the family is constantly X and parallel transport is the identity.
Consequently R3 transport is definitional bookkeeping on this route.
-/

def r3TransportTrivialQbar
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    R3TransportContract M
      (trivialSpreadQbar G X p α hX hα) :=
  {
    transport := by
      intro P
      rcases P with ⟨y, path, hy, hq, C, hC⟩
      cases y
      cases path
      exact ⟨C, hC⟩
  }

theorem r3_trivial_qbar_nonempty
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α} :
    Nonempty
      (R3TransportContract M
        (trivialSpreadQbar G X p α hX hα)) :=
  ⟨r3TransportTrivialQbar⟩

/-- On the constant-Qbar route, R1d and R3 are closed internally.  Therefore
the only material input still needed to recover the original concrete span is
R2 at the selected fiber. -/
theorem trivial_qbar_r2_is_sufficient
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (R2 :
      R2PointProductionContract M
        (trivialSpreadQbar G X p α hX hα)
        (trivialQbarDescent
          (G := G) (X := X) (p := p)
          (α := α) (hX := hX) (hα := hα))) :
    InConcreteCycleSpan M α :=
  r1d_r2_r3_yields_concrete_witness
    (trivialQbarDescent
      (G := G) (X := X) (p := p)
      (α := α) (hX := hX) (hα := hα))
    R2
    r3TransportTrivialQbar

#print axioms MCore.BackwardAudit.r3TransportTrivialQbar
#print axioms MCore.BackwardAudit.r3_trivial_qbar_nonempty
#print axioms MCore.BackwardAudit.trivial_qbar_r2_is_sufficient

end MCore.BackwardAudit
