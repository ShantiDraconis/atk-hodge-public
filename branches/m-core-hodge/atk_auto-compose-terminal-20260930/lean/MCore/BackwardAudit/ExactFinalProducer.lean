import MCore.BackwardAudit.FinalExternal
import MCore.BackwardAudit.CodimOneLefschetz11
import MCore.BackwardAudit.HodgeProducerFirst

namespace MCore.BackwardAudit
namespace Final

/-- A concrete Lefschetz (1,1) law is exactly the codimension-one payload. -/
theorem codimOnePayload_of_concrete_lefschetz
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : Lefschetz11ConcreteLaw M) :
    MCore.CodimensionOneAlgebraicityPayload M := by
  intro X alpha hX hAlpha
  exact L.algebraic X alpha hX hAlpha

/-- Higher-codimension H01 data already produces an explicit finite cycle
    combination; no semantic/concrete CycleSpanAdapter is required here. -/
theorem higherCodimConcrete_of_h01
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HigherCodimH01ForwardPayload G M) :
    HigherCodimensionAlgebraicityPayload M := by
  intro X p alpha hp hX hAlpha
  let Z :=
    hodgeCycleOfMinimalForwardPayload
      (H X p alpha hp) hX hAlpha
  exact ⟨Z,
    hodgeCycleOfMinimalForwardPayload_verified
      (H X p alpha hp) hX hAlpha⟩

/-- Shortest current positive producer:
    * codimension 0 concrete algebraicity,
    * codimension 1 concrete Lefschetz (1,1),
    * H01 forward production only in codimension >= 2.
    The old CycleSpanAdapter has been removed from this route. -/
def positiveProducer_of_minimal_concrete_inputs
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (L : Lefschetz11ConcreteLaw M)
    (H : HigherCodimH01ForwardPayload G M) :
    HodgePositiveTerminalProducer M :=
  .codimSplit h0
    (codimOnePayload_of_concrete_lefschetz L)
    (higherCodimConcrete_of_h01 H)

def finalExternal_of_minimal_concrete_inputs
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (L : Lefschetz11ConcreteLaw M)
    (H : HigherCodimH01ForwardPayload G M) :
    FinalExternalCertificate M :=
  {
    boundary := B
    producer := positiveProducer_of_minimal_concrete_inputs h0 L H
  }

theorem FINAL_ROOT_of_minimal_concrete_inputs
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (B : HodgeCertificationBoundary G M)
    (h0 : CodimensionZeroAlgebraicityPayload M)
    (L : Lefschetz11ConcreteLaw M)
    (H : HigherCodimH01ForwardPayload G M) :
    FINAL_ROOT G :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_minimal_concrete_inputs B h0 L H)

#print axioms MCore.BackwardAudit.Final.codimOnePayload_of_concrete_lefschetz
#print axioms MCore.BackwardAudit.Final.higherCodimConcrete_of_h01
#print axioms MCore.BackwardAudit.Final.positiveProducer_of_minimal_concrete_inputs
#print axioms MCore.BackwardAudit.Final.finalExternal_of_minimal_concrete_inputs
#print axioms MCore.BackwardAudit.Final.FINAL_ROOT_of_minimal_concrete_inputs

end Final
end MCore.BackwardAudit
