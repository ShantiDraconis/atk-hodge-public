import MCore.BackwardAudit.R1DescentBoundary

namespace HodgeR3FactorizationAudit

open MCore
open MCore.BackwardAudit

/-- Cohomological return map only. -/
structure CohomologyReturnData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  returnCohomology :
    G.CohomologyQ (S.Family Q.y) (2 * p) →
    G.CohomologyQ X (2 * p)

/-- Cycle-combination specialization map only. -/
structure CycleSpecializationData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  specializeCombination :
    CycleCombination G M (S.Family Q.y) p →
    CycleCombination G M X p

/-- Naturality of the cycle-class map with respect to the two maps above. -/
structure CycleClassNaturalityData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S)
    (R : CohomologyReturnData S Q)
    (Sp : CycleSpecializationData M S Q) where
  compat :
    ∀ c : CycleCombination G M (S.Family Q.y) p,
      (Sp.specializeCombination c).eval M =
        R.returnCohomology (c.eval M)

/-- Linearity properties needed for a cohomological return map to commute
    with evaluation of finite cycle combinations.  These laws are attached to
    the concrete return map, not assumed globally about M. -/
structure CohomologyReturnLinearityData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S)
    (R : CohomologyReturnData S Q) where
  zero_compat :
    R.returnCohomology
      (M.zeroClass :
        G.CohomologyQ (S.Family Q.y) (2 * p)) =
      (M.zeroClass : G.CohomologyQ X (2 * p))

  add_compat :
    ∀ (a b : G.CohomologyQ (S.Family Q.y) (2 * p)),
      R.returnCohomology (M.addClass a b) =
        M.addClass (R.returnCohomology a) (R.returnCohomology b)

  smul_compat :
    ∀ (k : M.Coeff)
      (a : G.CohomologyQ (S.Family Q.y) (2 * p)),
      R.returnCohomology (M.smul k a) =
        M.smul k (R.returnCohomology a)

/-- Geometric specialization on individual codimension-p cycle generators,
    together with compatibility of their cycle classes. -/
structure GeneratorSpecializationData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S)
    (R : CohomologyReturnData S Q) where
  specializeCycle :
    G.CycleQ (S.Family Q.y) p →
    G.CycleQ X p

  cycleClass_compat :
    ∀ Z : G.CycleQ (S.Family Q.y) p,
      R.returnCohomology (M.cycleClass p Z) =
        M.cycleClass p (specializeCycle Z)

/-- Extend generator-wise specialization to finite rational cycle
    combinations by mapping only the cycle generator and preserving the
    coefficient. -/
def specializeCombinationByGenerators
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnData S Q}
    (D : GeneratorSpecializationData M S Q R)
    (c : CycleCombination G M (S.Family Q.y) p) :
    CycleCombination G M X p :=
  {
    terms := c.terms.map (fun t => (t.1, D.specializeCycle t.2))
  }

/-- Evaluation commutes with generator-wise specialization once the return map
    is linear and individual cycle classes commute. -/
theorem eval_specializeCombinationByGenerators
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnData S Q}
    (L : CohomologyReturnLinearityData M S Q R)
    (D : GeneratorSpecializationData M S Q R)
    (c : CycleCombination G M (S.Family Q.y) p) :
    (specializeCombinationByGenerators D c).eval M =
      R.returnCohomology (c.eval M) := by
  cases c with
  | mk terms =>
      induction terms with
      | nil =>
          simpa [specializeCombinationByGenerators, CycleCombination.eval]
            using L.zero_compat.symm
      | cons t ts ih =>
          rcases t with ⟨k, Z⟩
          change
            M.addClass
              (M.smul k (M.cycleClass p (D.specializeCycle Z)))
              ((specializeCombinationByGenerators D
                { terms := ts }).eval M) =
            R.returnCohomology
              (M.addClass
                (M.smul k (M.cycleClass p Z))
                (({ terms := ts } :
                  CycleCombination G M (S.Family Q.y) p).eval M))
          rw [ih]
          rw [L.add_compat]
          rw [L.smul_compat]
          rw [D.cycleClass_compat]

/-- Generator-wise geometry therefore constructs the combination-level
    specialization interface. -/
def cycleSpecializationOfGenerators
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnData S Q}
    (D : GeneratorSpecializationData M S Q R) :
    CycleSpecializationData M S Q :=
  {
    specializeCombination := specializeCombinationByGenerators D
  }

/-- The same data constructs the exact combination-level naturality object
    consumed by GeometricCycleSpecializationDecomposed. -/
def cycleClassNaturalityOfGenerators
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {R : CohomologyReturnData S Q}
    (L : CohomologyReturnLinearityData M S Q R)
    (D : GeneratorSpecializationData M S Q R) :
    CycleClassNaturalityData M S Q R
      (cycleSpecializationOfGenerators D) :=
  {
    compat := eval_specializeCombinationByGenerators L D
  }

/-- Compatibility between cohomological return and the transported input
    class. -/
structure TransportReturnCompatibilityData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S)
    (R : CohomologyReturnData S Q) where
  return_transportedAlpha_eq_alpha :
    R.returnCohomology (S.transportedAlpha Q.path) = α

/-- Equality transport preserves the zero class because the variety index
    equality is eliminated definitionally. -/
theorem castCohomology_zeroClass
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X Y : G.Variety}
    {p : Nat}
    (h : X = Y) :
    castCohomology G h
      (M.zeroClass : G.CohomologyQ X (2 * p)) =
      (M.zeroClass : G.CohomologyQ Y (2 * p)) := by
  cases h
  rfl

/-- Equality transport preserves the abstract addition operation. -/
theorem castCohomology_addClass
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X Y : G.Variety}
    {p : Nat}
    (h : X = Y)
    (a b : G.CohomologyQ X (2 * p)) :
    castCohomology G h (M.addClass a b) =
      M.addClass
        (castCohomology G h a)
        (castCohomology G h b) := by
  cases h
  rfl

/-- Equality transport preserves scalar action. -/
theorem castCohomology_smul
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X Y : G.Variety}
    {p : Nat}
    (h : X = Y)
    (k : M.Coeff)
    (a : G.CohomologyQ X (2 * p)) :
    castCohomology G h (M.smul k a) =
      M.smul k (castCohomology G h a) := by
  cases h
  rfl

/-- Reverse-path datum sufficient to build the exact cohomological return
    and transport-return compatibility used by this factorization. -/
structure FactorReversePathData
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  reversePath : S.Path Q.y S.basepoint
  rightInverse :
    S.pathComp Q.path reversePath = S.pathRefl S.basepoint

theorem factor_castCohomology_roundtrip
    {G : GradedRationalHodgeData}
    {X Y : G.Variety}
    {n : Nat}
    (h : X = Y)
    (β : G.CohomologyQ Y n) :
    castCohomology G h
      (castCohomology G h.symm β) = β := by
  cases h
  rfl

/-- Linearity of the frozen parallel transport along the chosen reverse
    path.  This is the exact Gauss-Manin semantic obligation needed by G4;
    no algebraicity conclusion appears here. -/
structure ReverseTransportLinearityData
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S)
    (D : FactorReversePathData S Q) where

  zero_compat :
    S.parallelTransport D.reversePath
      (M.zeroClass :
        G.CohomologyQ (S.Family Q.y) (2 * p)) =
      (M.zeroClass :
        G.CohomologyQ (S.Family S.basepoint) (2 * p))

  add_compat :
    ∀ (a b : G.CohomologyQ (S.Family Q.y) (2 * p)),
      S.parallelTransport D.reversePath (M.addClass a b) =
        M.addClass
          (S.parallelTransport D.reversePath a)
          (S.parallelTransport D.reversePath b)

  smul_compat :
    ∀ (k : M.Coeff)
      (a : G.CohomologyQ (S.Family Q.y) (2 * p)),
      S.parallelTransport D.reversePath (M.smul k a) =
        M.smul k (S.parallelTransport D.reversePath a)

/-- The return map is no longer arbitrary once a reverse path is supplied. -/
def cohomologyReturnOfReversePath
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : FactorReversePathData S Q) :
    CohomologyReturnData S Q :=
  {
    returnCohomology := fun β =>
      castCohomology G S.fiberAtBasepoint
        (S.parallelTransport D.reversePath β)
  }

/-- Gauss-Manin linearity along the reverse path induces all linearity laws
    needed by the cohomological return map. -/
def cohomologyReturnLinearityOfReverseTransport
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    {D : FactorReversePathData S Q}
    (L : ReverseTransportLinearityData M S Q D) :
    CohomologyReturnLinearityData M S Q
      (cohomologyReturnOfReversePath D) := by
  refine {
    zero_compat := ?_
    add_compat := ?_
    smul_compat := ?_
  }
  · change
      castCohomology G S.fiberAtBasepoint
        (S.parallelTransport D.reversePath
          (M.zeroClass :
            G.CohomologyQ (S.Family Q.y) (2 * p))) =
        (M.zeroClass : G.CohomologyQ X (2 * p))
    rw [L.zero_compat]
    exact castCohomology_zeroClass M S.fiberAtBasepoint
  · intro a b
    change
      castCohomology G S.fiberAtBasepoint
        (S.parallelTransport D.reversePath (M.addClass a b)) =
      M.addClass
        (castCohomology G S.fiberAtBasepoint
          (S.parallelTransport D.reversePath a))
        (castCohomology G S.fiberAtBasepoint
          (S.parallelTransport D.reversePath b))
    rw [L.add_compat]
    exact castCohomology_addClass M S.fiberAtBasepoint _ _
  · intro k a
    change
      castCohomology G S.fiberAtBasepoint
        (S.parallelTransport D.reversePath (M.smul k a)) =
      M.smul k
        (castCohomology G S.fiberAtBasepoint
          (S.parallelTransport D.reversePath a))
    rw [L.smul_compat]
    exact castCohomology_smul M S.fiberAtBasepoint k _

/-- The exact TransportReturnCompatibilityData is derived from path
    cancellation and the frozen parallel-transport composition law. -/
def transportReturnOfReversePath
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : FactorReversePathData S Q) :
    TransportReturnCompatibilityData S Q
      (cohomologyReturnOfReversePath D) := by
  refine {
    return_transportedAlpha_eq_alpha := ?_
  }
  change
    castCohomology G S.fiberAtBasepoint
      (S.parallelTransport D.reversePath
        (S.parallelTransport Q.path S.alphaAtBasepoint)) = α
  rw [← S.parallelTransport_comp
    Q.path D.reversePath S.alphaAtBasepoint]
  rw [D.rightInverse]
  rw [S.parallelTransport_refl]
  exact factor_castCohomology_roundtrip
    S.fiberAtBasepoint α

/-- Fully factorized non-circular R3 interface.  Properness, flatness and
    relative Chow/Hilbert geometry are not faked as arbitrary Props; they
    remain semantic-adapter requirements for constructing these four pieces. -/
structure GeometricCycleSpecializationDecomposed
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : SpreadData G X p α hX hα)
    (Q : QbarHodgePointData S) where
  returnData : CohomologyReturnData S Q
  specializationData : CycleSpecializationData M S Q
  naturality :
    CycleClassNaturalityData M S Q returnData specializationData
  transportReturn :
    TransportReturnCompatibilityData S Q returnData

/-- Reverse-path transport plus its Gauss-Manin linearity and generator-wise
    cycle specialization construct the entire non-circular G4 decomposition. -/
def decompositionOfGeneratorGeometry
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : FactorReversePathData S Q)
    (L : ReverseTransportLinearityData M S Q D)
    (C : GeneratorSpecializationData M S Q
      (cohomologyReturnOfReversePath D)) :
    GeometricCycleSpecializationDecomposed M S Q := by
  let LR :
      CohomologyReturnLinearityData M S Q
        (cohomologyReturnOfReversePath D) :=
    cohomologyReturnLinearityOfReverseTransport L
  let Sp : CycleSpecializationData M S Q :=
    cycleSpecializationOfGenerators C
  let N :
      CycleClassNaturalityData M S Q
        (cohomologyReturnOfReversePath D) Sp :=
    cycleClassNaturalityOfGenerators LR C
  exact {
    returnData := cohomologyReturnOfReversePath D
    specializationData := Sp
    naturality := N
    transportReturn := transportReturnOfReversePath D
  }

/-- Once specialization/naturality are supplied, a reverse path constructs
    the full non-circular decomposition; transport-return is no longer an
    independent open field. -/
def decompositionOfReversePath
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : FactorReversePathData S Q)
    (Sp : CycleSpecializationData M S Q)
    (N : CycleClassNaturalityData M S Q
      (cohomologyReturnOfReversePath D) Sp) :
    GeometricCycleSpecializationDecomposed M S Q :=
  {
    returnData := cohomologyReturnOfReversePath D
    specializationData := Sp
    naturality := N
    transportReturn := transportReturnOfReversePath D
  }

/-- The factorization proves the same raw class equality as the earlier
    geometric interface, without mentioning any final Hodge target. -/
theorem decomposed_specialization_has_original_class
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : SpreadData G X p α hX hα}
    {Q : QbarHodgePointData S}
    (D : GeometricCycleSpecializationDecomposed M S Q)
    (C : R2FiberCycleData M S Q) :
    (D.specializationData.specializeCombination C.combination).eval M = α := by
  calc
    (D.specializationData.specializeCombination C.combination).eval M =
        D.returnData.returnCohomology (C.combination.eval M) :=
      D.naturality.compat C.combination
    _ = D.returnData.returnCohomology (S.transportedAlpha Q.path) := by
      rw [C.combination_class]
    _ = α :=
      D.transportReturn.return_transportedAlpha_eq_alpha

inductive R3FactorRequirementStatus where
  | typed
  | semanticAdapterResidue
  | openGeometry
  deriving Repr, DecidableEq

structure R3FactorRequirement where
  name : String
  status : R3FactorRequirementStatus
  note : String
  deriving Repr

def r3FactorRequirements : List R3FactorRequirement :=
  [
    ⟨"COHOMOLOGY_RETURN_MAP", .typed,
      "Constructed from reverse-path parallel transport and base-fiber identification."⟩,
    ⟨"CYCLE_SPECIALIZATION_MAP", .typed,
      "Constructed mechanically from generator-wise cycle specialization."⟩,
    ⟨"CYCLE_CLASS_NATURALITY", .typed,
      "Derived by induction on CycleCombination from return-map linearity plus generator cycle-class compatibility."⟩,
    ⟨"TRANSPORT_RETURN_COMPATIBILITY", .typed,
      "Derived internally from a chosen reverse path and the frozen transport composition law; only reverse-path semantics remain in the adapter."⟩,
    ⟨"RELATIVE_CHOW_HILBERT", .semanticAdapterResidue,
      "No relative Chow/Hilbert object exists in the frozen corpus."⟩,
    ⟨"GAUSS_MANIN_LINEARITY", .semanticAdapterResidue,
      "Only zero/add/smul preservation of parallel transport along the chosen reverse path remains to be supplied by genuine local-system semantics."⟩,
    ⟨"GENERATOR_CYCLE_SPECIALIZATION", .openGeometry,
      "Must construct specialization of individual cycle generators with cycle-class compatibility."⟩,
    ⟨"PROPER_FLAT_GEOMETRY", .semanticAdapterResidue,
      "No scheme-theoretic proper/flat family object exists in the frozen corpus."⟩
  ]

def r3FactorSemanticMatchComplete : Bool := false

theorem r3_factor_semantic_match_still_open :
    r3FactorSemanticMatchComplete = false := by
  rfl

#print axioms HodgeR3FactorizationAudit.castCohomology_zeroClass
#print axioms HodgeR3FactorizationAudit.castCohomology_addClass
#print axioms HodgeR3FactorizationAudit.castCohomology_smul
#print axioms HodgeR3FactorizationAudit.specializeCombinationByGenerators
#print axioms HodgeR3FactorizationAudit.eval_specializeCombinationByGenerators
#print axioms HodgeR3FactorizationAudit.cycleSpecializationOfGenerators
#print axioms HodgeR3FactorizationAudit.cycleClassNaturalityOfGenerators
#print axioms HodgeR3FactorizationAudit.factor_castCohomology_roundtrip
#print axioms HodgeR3FactorizationAudit.cohomologyReturnOfReversePath
#print axioms HodgeR3FactorizationAudit.cohomologyReturnLinearityOfReverseTransport
#print axioms HodgeR3FactorizationAudit.transportReturnOfReversePath
#print axioms HodgeR3FactorizationAudit.decompositionOfReversePath
#print axioms HodgeR3FactorizationAudit.decompositionOfGeneratorGeometry
#print axioms HodgeR3FactorizationAudit.decomposed_specialization_has_original_class
#print axioms HodgeR3FactorizationAudit.r3_factor_semantic_match_still_open

end HodgeR3FactorizationAudit
