import MCore.BackwardAudit.HodgeFastR2Mincut
import MCore.BackwardAudit.R2CandidateFirewall

namespace MCore.BackwardAudit

/--
Terminal no-reopen frontier for Hodge.

All structural stages before R2 are frozen.  The only remaining mathematical
obligation is the exact endpoint-equivalent R2 payload.
-/
def HodgeLastBit
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop :=
  HodgeFastR2OpenMath M

theorem hodge_last_bit_iff_concrete_payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeLastBit M ↔ ConcreteAlgebraicityPayload M :=
  hodge_fast_r2_iff_concrete_payload M

theorem hodge_last_bit_closes_terminal
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h : HodgeLastBit M) :
    ConcreteAlgebraicityPayload M :=
  (hodge_last_bit_iff_concrete_payload M).1 h

/--
No-reopen certificate: R1d and R3 are already inhabited on the fast Qbar
regression route.  Re-opening them cannot reduce the remaining endpoint.
-/
structure HodgeNoReopenCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop where
  r1d_closed :
    ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p))
      (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      Nonempty
        (R1DescentPointContract
          (trivialSpreadQbar G X p α hX hα))
  r3_closed :
    ∀ (X : G.Variety) (p : Nat) (α : G.CohomologyQ X (2 * p))
      (hX : G.isSmoothProjective X) (hα : G.isTypePP p α),
      Nonempty
        (R3TransportContract M
          (trivialSpreadQbar G X p α hX hα))

def hodgeNoReopenCertificate
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeNoReopenCertificate M :=
  {
    r1d_closed := by
      intro X p α hX hα
      exact hodge_fast_r1d_closed
    r3_closed := by
      intro X p α hX hα
      exact hodge_fast_r3_closed
  }

/--
The truncation is exact, not a weakening: solving LastBit solves exactly the
concrete Hodge endpoint, while structural candidates that survive the
countermodel remain rejected by the firewall.
-/
theorem hodge_terminal_truncation_exact
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    HodgeLastBit M ↔ ConcreteAlgebraicityPayload M :=
  hodge_last_bit_iff_concrete_payload M

#print axioms MCore.BackwardAudit.hodge_last_bit_iff_concrete_payload
#print axioms MCore.BackwardAudit.hodge_last_bit_closes_terminal
#print axioms MCore.BackwardAudit.hodgeNoReopenCertificate
#print axioms MCore.BackwardAudit.hodge_terminal_truncation_exact

end MCore.BackwardAudit
