import MCore.Hodge
import MCore.HodgeReduction

namespace MCore

structure ClayLogicRefutationCertificate (D : ClayHodgeData) : Prop where
  claim : ClayLogicRefutationClaim D
  refutesOfficialStatement : ¬ ClayHodgeStatement D

theorem certify_clay_logic_refutation {D : ClayHodgeData}
    (h : HODGE_RESOLUTION_OPEN_MATH D) :
    ClayLogicRefutationCertificate D :=
  ⟨h, clay_logic_refutation_implies_not_statement h⟩

structure HodgeFinalRoot (D : ClayHodgeData) : Prop where
  refutation : ClayLogicRefutationCertificate D

structure HodgeFinalProof (D : ClayHodgeData) : Prop where
  root : HodgeFinalRoot D

structure HodgeExternalCertificate (D : ClayHodgeData) : Prop where
  finalProof : HodgeFinalProof D

theorem clay_refutation_to_final_root {D : ClayHodgeData}
    (h : HODGE_RESOLUTION_OPEN_MATH D) : HodgeFinalRoot D :=
  ⟨certify_clay_logic_refutation h⟩

theorem final_root_to_final_proof {D : ClayHodgeData}
    (h : HodgeFinalRoot D) : HodgeFinalProof D := ⟨h⟩

theorem final_proof_to_external {D : ClayHodgeData}
    (h : HodgeFinalProof D) : HodgeExternalCertificate D := ⟨h⟩

end MCore
