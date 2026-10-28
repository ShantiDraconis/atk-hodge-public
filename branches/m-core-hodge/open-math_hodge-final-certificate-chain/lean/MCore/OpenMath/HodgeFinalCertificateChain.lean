import MCore.Hodge
import MCore.HodgeBoundary
import MCore.HodgeReduction

namespace MCore

/-!
# Hodge OPEN_MATH final certificate chain

This file defines the complete typed promotion path from the existing semantic
interface to a final rational Hodge theorem certificate.

It is intentionally fail-closed:
* no axiom, sorry, admit, or synthetic status promotion is introduced;
* the final certificate can only be constructed from a real inhabitant of
  `H01MinimalForwardPayload`;
* `H01MinimalForwardPayload` is exactly the remaining pointwise algebraicity
  obligation already identified by the repository.
-/

/-- C0: the semantic interface exists and is the object to which all later
certificates are relative. This is a packaging certificate, not a proof of
Hodge. -/
structure HodgeSemanticInterfaceCertificate where
  data : HodgeSemanticData

/-- C1: the standard forward direction: algebraic cycle classes are Hodge
classes. This is useful audit evidence but does not imply surjectivity. -/
structure HodgeCycleClassDirectionCertificate
    (D : HodgeSemanticData) : Prop where
  proof : CycleClassIsHodge D

/-- C2: the reduction certificate. It records the already-proved equivalence
between the global conjecture and the pointwise algebraicity payload. -/
structure HodgeReductionCertificate
    (D : HodgeSemanticData) : Prop where
  proof : RationalHodgeConjecture D ↔ PointwiseHodgeAlgebraicity D

theorem hodgeReductionCertificate (D : HodgeSemanticData) :
    HodgeReductionCertificate D :=
  ⟨rationalHodge_iff_pointwise D⟩

/-- C3 / H01: the unique hard OPEN_MATH payload.

An inhabitant must prove, for every smooth projective object represented by
the semantic model and every rational Hodge class, that the class lies in the
rational span of algebraic cycle classes.

Nothing in this file constructs such an inhabitant. -/
structure H01MinimalForwardPayload
    (D : HodgeSemanticData) : Prop where
  pointwise : PointwiseHodgeAlgebraicity D

/-- C4: global algebraicity/surjectivity certificate. -/
structure HodgeAlgebraicitySurjectivityCertificate
    (D : HodgeSemanticData) : Prop where
  proof : RationalHodgeConjecture D

/-- H01 is sufficient to close the global semantic Hodge statement. -/
theorem h01_to_surjectivity
    {D : HodgeSemanticData}
    (h01 : H01MinimalForwardPayload D) :
    HodgeAlgebraicitySurjectivityCertificate D :=
  ⟨pointwise_closes_hodge h01.pointwise⟩

/-- C5: theorem certificate. The cycle-class direction is bundled as
independent audit evidence; the theorem itself is supplied by C4. -/
structure HodgeTheoremCertificate
    (D : HodgeSemanticData) : Prop where
  cycle_direction : CycleClassIsHodge D
  theorem_proof : RationalHodgeConjecture D

theorem surjectivity_to_theorem
    {D : HodgeSemanticData}
    (cycle : HodgeCycleClassDirectionCertificate D)
    (surj : HodgeAlgebraicitySurjectivityCertificate D) :
    HodgeTheoremCertificate D :=
  ⟨cycle.proof, surj.proof⟩

/-- C6: final external envelope. This is deliberately only a typed wrapper
around a kernel-checkable theorem certificate; provenance/CI metadata belongs
outside the theorem kernel. -/
structure HodgeFinalExternalCertificate
    (D : HodgeSemanticData) : Prop where
  theorem_certificate : HodgeTheoremCertificate D

theorem theorem_to_final_external
    {D : HodgeSemanticData}
    (h : HodgeTheoremCertificate D) :
    HodgeFinalExternalCertificate D :=
  ⟨h⟩

/-- Complete promotion route. This is the only positive constructor in this
file that reaches the final external certificate, and it visibly requires the
OPEN_MATH H01 payload. -/
theorem hodge_final_external_from_h01
    {D : HodgeSemanticData}
    (cycle : HodgeCycleClassDirectionCertificate D)
    (h01 : H01MinimalForwardPayload D) :
    HodgeFinalExternalCertificate D :=
  theorem_to_final_external
    (surjectivity_to_theorem cycle (h01_to_surjectivity h01))

/-- Consumer theorem for the final certificate. -/
theorem final_external_implies_rational_hodge
    {D : HodgeSemanticData}
    (cert : HodgeFinalExternalCertificate D) :
    RationalHodgeConjecture D :=
  cert.theorem_certificate.theorem_proof

/-- The exact hard mathematical target exposed without any certificate
wrapping. This is useful for theorem search and CI sentinels. -/
def HodgeOpenMathCore (D : HodgeSemanticData) : Prop :=
  PointwiseHodgeAlgebraicity D

theorem h01_iff_open_math_core (D : HodgeSemanticData) :
    H01MinimalForwardPayload D ↔ HodgeOpenMathCore D := by
  constructor
  · intro h
    exact h.pointwise
  · intro h
    exact ⟨h⟩

end MCore
