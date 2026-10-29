import MCore.HodgeCanonicalSemanticModel
import MCore.HodgeExactRemaining

/-! Source: open_math/P05_HODGE_GAP_ConcreteAlgebraicityPayload.lean
Blob: 34e47f8d9763bd472dd62dde741ac9327a288bd2.
This is an exact endpoint interface, not an unconditional inhabitant.
-/
namespace ATK.Hodge
open MCore

abbrev Material {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) : Prop := ConcreteAlgebraicityPayload M

theorem material_identity {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) (h : Material M) :
    ConcreteAlgebraicityPayload M := h

end ATK.Hodge
#print axioms ATK.Hodge.material_identity
