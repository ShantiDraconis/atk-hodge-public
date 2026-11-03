import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR1dVoisinAudit

open MCore
open MCore.BackwardAudit

/-- Minimal proposition actually needed by R1d: the relevant alpha-Hodge locus
    has at least one point satisfying the frozen Qbar field-of-definition hook.
    This deliberately does NOT identify "locus defined over Qbar" with
    "every complex point is Qbar". -/
def HasQbarPointOnRelevantHodgeLocus
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) : Prop :=
  ∃ y : S.Base,
    S.hodgeLocusForAlpha y ∧
    S.fieldOfDefinition.isDefinedOverQbar y

/-- The minimal Qbar-point proposition is exactly enough to construct the
    frozen R1d witness. -/
theorem has_qbar_point_on_locus_implies_r1d
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (h : HasQbarPointOnRelevantHodgeLocus S) :
    Nonempty (R1DescentPointContract S) := by
  rcases h with ⟨y, ⟨γ, hHodge⟩, hQbar⟩
  exact ⟨{
    point := {
      y := y
      path := γ
      y_is_hodge := hHodge
      y_is_defined_over_Qbar := hQbar
    }
  }⟩

/-- Conversely, an R1d witness supplies precisely such a Qbar Hodge-locus
    point. -/
theorem r1d_implies_has_qbar_point_on_locus
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (h : Nonempty (R1DescentPointContract S)) :
    HasQbarPointOnRelevantHodgeLocus S := by
  rcases h with ⟨D⟩
  exact ⟨D.point.y, ⟨D.point.path, D.point.y_is_hodge⟩,
    D.point.y_is_defined_over_Qbar⟩

theorem r1d_iff_has_qbar_point_on_locus
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα) :
    Nonempty (R1DescentPointContract S) ↔
      HasQbarPointOnRelevantHodgeLocus S :=
  ⟨r1d_implies_has_qbar_point_on_locus S,
   has_qbar_point_on_locus_implies_r1d S⟩

/-- Audit classification for the exact hypotheses of Voisin Theorem 0.5(2).
    These are statuses only; no missing geometric notion is replaced by an
    arbitrary mathematical Prop. -/
inductive VoisinRequirementStatus where
  | represented
  | semanticAdapterResidue
  | externalClassical
  | notImplied
  deriving Repr, DecidableEq

structure VoisinRequirement where
  name : String
  status : VoisinRequirementStatus
  note : String
  deriving Repr

def voisin05Part2Requirements : List VoisinRequirement :=
  [
    ⟨"SMOOTH_PROJECTIVE_FAMILY_DEFINED_OVER_QBAR",
      .semanticAdapterResidue,
      "The frozen Base/Family interface has no scheme/field-of-definition structure for the family itself."⟩,
    ⟨"PRIMITIVE_HODGE_CLASS",
      .semanticAdapterResidue,
      "K13 has isTypePP but no primitive-Lefschetz decomposition field in this interface."⟩,
    ⟨"IRREDUCIBLE_COMPONENT_OF_LOCUS_OF_HODGE_CLASSES_THROUGH_ALPHA",
      .semanticAdapterResidue,
      "The frozen hodgeLocusForAlpha is a predicate; irreducible scheme structure is not represented."⟩,
    ⟨"CONSTANT_SUB_VHS_ALL_TYPE_KK",
      .semanticAdapterResidue,
      "No polarizable VHS or constant sub-variation type is represented in the frozen corpus."⟩,
    ⟨"VOISIN_0_5_2_FIELD_OF_DEFINITION_CONCLUSION",
      .externalClassical,
      "Under the exact theorem hypotheses, the projected reduced Hodge-locus component is defined over Qbar and its Galois transforms remain Hodge-locus components."⟩,
    ⟨"QBAR_POINT_FROM_NONEMPTY_FINITE_TYPE_QBAR_MODEL",
      .externalClassical,
      "Requires an actual nonempty finite-type Qbar model; it is not encoded by the frozen Base : Type alone."⟩,
    ⟨"UNCONDITIONAL_R1D_FOR_ARBITRARY_ALPHA",
      .notImplied,
      "Voisin's criterion is sufficient, not universal, and does not settle isolated Hodge-locus points in general."⟩
  ]

def voisin05Part2SemanticMatchComplete : Bool := false
def r1dVoisinClosedForArbitraryInput : Bool := false

theorem voisin_semantic_match_still_open :
    voisin05Part2SemanticMatchComplete = false := by
  rfl

theorem r1d_voisin_general_case_still_open :
    r1dVoisinClosedForArbitraryInput = false := by
  rfl

#print axioms HodgeR1dVoisinAudit.has_qbar_point_on_locus_implies_r1d
#print axioms HodgeR1dVoisinAudit.r1d_implies_has_qbar_point_on_locus
#print axioms HodgeR1dVoisinAudit.r1d_iff_has_qbar_point_on_locus
#print axioms HodgeR1dVoisinAudit.voisin_semantic_match_still_open
#print axioms HodgeR1dVoisinAudit.r1d_voisin_general_case_still_open

end HodgeR1dVoisinAudit
