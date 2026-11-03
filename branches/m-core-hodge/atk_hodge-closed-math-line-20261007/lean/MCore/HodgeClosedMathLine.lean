import MCore.HodgeMaterialFrontier
import MCore.HodgeMaterialInhabitant
import MCore.HodgeExactRemaining
import MCore.HodgeCanonicalSemanticModel
import MCore.BackwardAudit.HodgeHabitantConstructors
import MCore.BackwardAudit.HodgeProducerFirst
import MCore.BackwardAudit.HodgeRecoveredMaterialBridge
import MCore.BackwardAudit.HodgeFastR2Mincut

namespace MCore

/-!
# Hodge CLOSED_MATH line

This file aggregates only kernel-proved transformations and explicit local
constructors.  It does not instantiate any open universal material producer
and does not promote the Hodge endpoint.

CLOSED_MATH here means: every declaration below has a complete Lean proof
from its explicit arguments, with no added theorem-carrying axiom, placeholder proof, or
hidden terminal assumption.
-/

/-- CLOSED: exact decomposition of the terminal payload by codimension. -/
theorem closed_material_split
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    ConcreteAlgebraicityPayload M ↔
      CodimZeroConcretePayload M ∧
      CodimOneConcretePayload M ∧
      HigherCodimConcretePayload M :=
  concretePayload_iff_materialSplit M

/-- CLOSED: a concrete codimension-one producer mechanically yields the
Lefschetz concrete law. -/
def closed_codimOne_producer_to_law
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : CodimOneCycleProducer G M) :
    BackwardAudit.Lefschetz11ConcreteLaw M :=
  P.toLefschetz11ConcreteLaw

/-- CLOSED: a complete higher material run yields the original finite-cycle
witness. -/
theorem closed_higher_run_to_span
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (W : HigherMaterialRun M X p α hX hα) :
    InConcreteCycleSpan M α :=
  higherMaterialRun_yields_concreteSpan W

/-- CLOSED: supplied low/high constructive producers assemble the exact
concrete payload. -/
theorem closed_material_producers_to_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (h0 : CodimZeroConcretePayload M)
    (L : BackwardAudit.Lefschetz11ConcreteLaw M)
    (h2 : HigherCodimConcretePayload M) :
    ConcreteAlgebraicityPayload M :=
  concretePayload_of_materialProducers h0 L h2

/-- CLOSED: the constructive material package projects to the exact payload. -/
theorem closed_constructive_material_to_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (H : HodgeConstructiveMaterial G M) :
    ConcreteAlgebraicityPayload M :=
  H.toConcretePayload

/-- CLOSED: exact R1d cut. -/
theorem closed_exact_r1d_cut
    {G : GradedRationalHodgeData}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    (S : BackwardAudit.SpreadData G X p α hX hα) :
    Nonempty (BackwardAudit.R1DescentPointContract S) ↔
      BackwardAudit.QbarIntersectsHodgeLocus S :=
  exact_r1d_cut S

/-- CLOSED: exact R2 cut. -/
theorem closed_exact_r2_cut
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : BackwardAudit.SpreadData G X p α hX hα}
    (D : BackwardAudit.R1DescentPointContract S) :
    Nonempty (BackwardAudit.R2PointProductionContract M S D) ↔
      BackwardAudit.R2FiberAlgebraicityTarget M D :=
  exact_r2_cut D

/-- CLOSED: exact R3 cut. -/
theorem closed_exact_r3_cut
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : BackwardAudit.SpreadData G X p α hX hα} :
    Nonempty (BackwardAudit.R3TransportContract M S) ↔
      BackwardAudit.R3VariationalAlgebraicityPayload M S :=
  exact_r3_cut

/-- CLOSED: canonical semantic endpoint is exactly the concrete payload. -/
theorem closed_canonical_terminal_iff_payload
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) :
    HodgeTerminalCertifies (canonicalHodgeSemanticData G M) ↔
      ConcreteAlgebraicityPayload M :=
  canonicalTerminal_iff_concretePayload G M

/-- CLOSED: explicit local zero-class cycle constructor. -/
theorem closed_zero_cycle_constructor
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat) :
    ∃ Z : CycleCombination G M X p,
      Z.eval M = (M.zeroClass : G.CohomologyQ X (2 * p)) :=
  BackwardAudit.realize_zeroClass M X p

/-- CLOSED: exact local producer extracted from a complete R1d/R2/R3 run. -/
noncomputable def closed_exact_local_producer
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    {hX : G.isSmoothProjective X}
    {hα : G.isTypePP p α}
    {S : BackwardAudit.SpreadData G X p α hX hα}
    (D : BackwardAudit.R1DescentPointContract S)
    (R2 : BackwardAudit.R2PointProductionContract M S D)
    (R3 : BackwardAudit.R3TransportContract M S) :
    CycleCombination G M X p :=
  BackwardAudit.hodgeExactLocalProducer D R2 R3

/-- CLOSED: recovered universal-forward implication.  This theorem does not
assert existence of the universal producer; it proves the forward map from
that explicit producer to the endpoint. -/
theorem closed_universalForward_to_payload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : ∀ (X : G.Variety) (p : Nat)
      (α : G.CohomologyQ X (2 * p)),
      BackwardAudit.H01MinimalForwardPayload G M X p α) :
    ConcreteAlgebraicityPayload M :=
  BackwardAudit.recovered_universalForward_closes_concrete P

#print axioms MCore.closed_material_split
#print axioms MCore.closed_codimOne_producer_to_law
#print axioms MCore.closed_higher_run_to_span
#print axioms MCore.closed_material_producers_to_payload
#print axioms MCore.closed_constructive_material_to_payload
#print axioms MCore.closed_exact_r1d_cut
#print axioms MCore.closed_exact_r2_cut
#print axioms MCore.closed_exact_r3_cut
#print axioms MCore.closed_canonical_terminal_iff_payload
#print axioms MCore.closed_zero_cycle_constructor
#print axioms MCore.closed_exact_local_producer
#print axioms MCore.closed_universalForward_to_payload

end MCore


namespace MCore

open BackwardAudit

/-- Exact Type-valued material producer for the compressed fast-Qbar route. -/
structure HodgeR2MaterialProducer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  produce :
    ∀ (X : G.Variety) (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      R2PointProductionContract M
        (trivialSpreadQbar G X p α hX hα)
        (trivialQbarDescent
          (G := G) (X := X) (p := p)
          (α := α) (hX := hX) (hα := hα))

/-- A genuine universal R2 producer closes the exact material endpoint. -/
theorem HodgeR2MaterialProducer.toConcretePayload
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgeR2MaterialProducer G M) :
    ConcreteAlgebraicityPayload M := by
  intro X p α hX hα
  exact hodge_fast_r2_pointwise_sufficient
    (P.produce X p α hX hα)

/-- The same producer closes the canonical semantic terminal. -/
theorem HodgeR2MaterialProducer.toCanonicalTerminal
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgeR2MaterialProducer G M) :
    HodgeTerminalCertifies (canonicalHodgeSemanticData G M) :=
  (canonicalTerminal_iff_concretePayload G M).2 P.toConcretePayload

#print axioms MCore.HodgeR2MaterialProducer.toConcretePayload
/-- Exact terminal mincut: inhabitance of the universal R2 producer is
equivalent to the concrete Hodge payload.  The reverse direction uses
Classical.choice only to extract the Type-valued R2 witness from its
propositionally certified existence. -/
theorem nonempty_hodgeR2MaterialProducer_iff_payload
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Nonempty (HodgeR2MaterialProducer G M) ↔
      ConcreteAlgebraicityPayload M := by
  constructor
  · rintro ⟨P⟩
    exact P.toConcretePayload
  · intro h
    refine ⟨{ produce := ?_ }⟩
    intro X p α hX hα
    have hFiber :
        R2FiberAlgebraicityTarget M
          (trivialQbarDescent
            (G := G) (X := X) (p := p)
            (α := α) (hX := hX) (hα := hα)) :=
      (r2_trivial_qbar_iff_original_span).2 (h X p α hX hα)
    exact Classical.choice
      (r2_nonempty_of_fiber_algebraicity
        (trivialQbarDescent
          (G := G) (X := X) (p := p)
          (α := α) (hX := hX) (hα := hα))
        hFiber)

/-- Equivalent terminal statement in the canonical semantic model. -/
theorem nonempty_hodgeR2MaterialProducer_iff_terminal
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Nonempty (HodgeR2MaterialProducer G M) ↔
      HodgeTerminalCertifies (canonicalHodgeSemanticData G M) := by
  rw [nonempty_hodgeR2MaterialProducer_iff_payload M]
  exact (canonicalTerminal_iff_concretePayload G M).symm

#print axioms MCore.HodgeR2MaterialProducer.toConcretePayload
#print axioms MCore.HodgeR2MaterialProducer.toCanonicalTerminal
#print axioms MCore.nonempty_hodgeR2MaterialProducer_iff_payload
/-- The compressed R2 producer and the recovered historical Hodge habitant
carry exactly the same terminal mathematical content. -/
theorem nonempty_hodgeR2MaterialProducer_iff_habitant
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Nonempty (HodgeR2MaterialProducer G M) ↔
      Nonempty (BackwardAudit.HodgeHabitant M) := by
  constructor
  · intro hR2
    have hPayload : ConcreteAlgebraicityPayload M :=
      (nonempty_hodgeR2MaterialProducer_iff_payload M).1 hR2
    exact ⟨BackwardAudit.habitant_of_concretePayload hPayload⟩
  · intro hHab
    let H : BackwardAudit.HodgeHabitant M := Classical.choice hHab
    have hPayload : ConcreteAlgebraicityPayload M :=
      BackwardAudit.concretePayload_of_habitant H
    exact (nonempty_hodgeR2MaterialProducer_iff_payload M).2 hPayload

#print axioms MCore.HodgeR2MaterialProducer.toConcretePayload
#print axioms MCore.HodgeR2MaterialProducer.toCanonicalTerminal
#print axioms MCore.nonempty_hodgeR2MaterialProducer_iff_payload
#print axioms MCore.nonempty_hodgeR2MaterialProducer_iff_terminal
/-- Minimal Type-valued material source: directly construct the finite rational
cycle combination representing every admissible Hodge class. -/
structure HodgeDirectCycleProducer
    (G : GradedRationalHodgeData)
    (M : CycleSpanMechanics G) where
  produce :
    ∀ (X : G.Variety) (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      CycleCombination G M X p
  produce_eval :
    ∀ (X : G.Variety) (p : Nat)
      (α : G.CohomologyQ X (2 * p))
      (hX : G.isSmoothProjective X)
      (hα : G.isTypePP p α),
      (produce X p α hX hα).eval M = α

/-- A direct cycle producer gives the compressed R2 producer on the constant
Qbar family, definitionally except for the transported-alpha identity. -/
def HodgeDirectCycleProducer.toR2
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgeDirectCycleProducer G M) :
    HodgeR2MaterialProducer G M where
  produce := by
    intro X p α hX hα
    exact {
      produceCycle := {
        combination := P.produce X p α hX hα
        combination_class := by
          rw [trivial_qbar_transportedAlpha_eq]
          exact P.produce_eval X p α hX hα
      }
    }

/-- Conversely, the compressed R2 producer directly returns the required
cycle combination because the constant-Qbar transport is the identity. -/
def HodgeR2MaterialProducer.toDirectCycle
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (P : HodgeR2MaterialProducer G M) :
    HodgeDirectCycleProducer G M where
  produce := fun X p α hX hα =>
    (P.produce X p α hX hα).produceCycle.combination
  produce_eval := by
    intro X p α hX hα
    have h :=
      (P.produce X p α hX hα).produceCycle.combination_class
    simpa [trivial_qbar_transportedAlpha_eq] using h

/-- Exact Type-level equivalence of the final material source and R2 producer. -/
theorem nonempty_directCycleProducer_iff_r2Producer
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G) :
    Nonempty (HodgeDirectCycleProducer G M) ↔
      Nonempty (HodgeR2MaterialProducer G M) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.toR2⟩
  · rintro ⟨P⟩
    exact ⟨P.toDirectCycle⟩

#print axioms MCore.HodgeR2MaterialProducer.toConcretePayload
#print axioms MCore.HodgeR2MaterialProducer.toCanonicalTerminal
#print axioms MCore.nonempty_hodgeR2MaterialProducer_iff_payload
#print axioms MCore.nonempty_hodgeR2MaterialProducer_iff_terminal
#print axioms MCore.nonempty_hodgeR2MaterialProducer_iff_habitant
#print axioms MCore.HodgeDirectCycleProducer.toR2
#print axioms MCore.HodgeR2MaterialProducer.toDirectCycle
/-- Genuine material base case: the zero class is represented by the empty
finite cycle combination. -/
theorem directCycle_zero_witness
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    (X : G.Variety)
    (p : Nat) :
    ∃ C : CycleCombination G M X p,
      C.eval M = (M.zeroClass : G.CohomologyQ X (2 * p)) :=
  BackwardAudit.realize_zeroClass M X p

/-- Genuine material base case: a scalar multiple of an actual cycle class is
represented by a singleton finite cycle combination. -/
theorem directCycle_single_witness
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M)
    {X : G.Variety}
    (p : Nat)
    (a : M.Coeff)
    (z : G.CycleQ X p) :
    ∃ C : CycleCombination G M X p,
      C.eval M = M.smul a (M.cycleClass p z) :=
  BackwardAudit.realize_smul_cycleClass L p a z

/-- Pointwise zero-class adapter into the exact direct-cycle target. -/
theorem directCycle_of_eq_zero
    {G : GradedRationalHodgeData}
    (M : CycleSpanMechanics G)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (hα0 : α = M.zeroClass) :
    ∃ C : CycleCombination G M X p, C.eval M = α :=
  BackwardAudit.realize_hodgeClass_eq_zero M hα0

/-- Pointwise singleton adapter into the exact direct-cycle target. -/
theorem directCycle_of_eq_single
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M)
    {X : G.Variety}
    {p : Nat}
    {α : G.CohomologyQ X (2 * p)}
    (a : M.Coeff)
    (z : G.CycleQ X p)
    (hrep : α = M.smul a (M.cycleClass p z)) :
    ∃ C : CycleCombination G M X p, C.eval M = α :=
  BackwardAudit.realize_hodgeClass_eq_smul_cycleClass L a z hrep

#print axioms MCore.HodgeDirectCycleProducer.toR2
#print axioms MCore.HodgeR2MaterialProducer.toDirectCycle
#print axioms MCore.nonempty_directCycleProducer_iff_r2Producer
#print axioms MCore.directCycle_zero_witness
#print axioms MCore.directCycle_single_witness
#print axioms MCore.directCycle_of_eq_zero
/-- Evaluation of concatenated concrete combinations is addition of evaluations,
under the explicitly supplied additive laws. -/
theorem cycleCombination_eval_append
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M)
    {X : G.Variety}
    {p : Nat}
    (c₁ c₂ : CycleCombination G M X p) :
    (CycleCombination.mk (c₁.terms ++ c₂.terms)).eval M =
      M.addClass (c₁.eval M) (c₂.eval M) := by
  cases c₁ with
  | mk xs =>
      cases c₂ with
      | mk ys =>
          induction xs with
          | nil =>
              simp [CycleCombination.eval, L.zero_add]
          | cons t ts ih =>
              simp [CycleCombination.eval, ih, L.add_assoc]

/-- Concrete cycle-span witnesses are closed under addition. -/
theorem directCycle_add_witness
    {G : GradedRationalHodgeData}
    {M : CycleSpanMechanics G}
    (L : CycleSpanLaws G M)
    {X : G.Variety}
    {p : Nat}
    {α β : G.CohomologyQ X (2 * p)}
    (hα : ∃ c : CycleCombination G M X p, c.eval M = α)
    (hβ : ∃ c : CycleCombination G M X p, c.eval M = β) :
    ∃ c : CycleCombination G M X p,
      c.eval M = M.addClass α β := by
  rcases hα with ⟨cα, hcα⟩
  rcases hβ with ⟨cβ, hcβ⟩
  refine ⟨CycleCombination.mk (cα.terms ++ cβ.terms), ?_⟩
  rw [cycleCombination_eval_append L cα cβ, hcα, hcβ]

#print axioms MCore.HodgeDirectCycleProducer.toR2
#print axioms MCore.HodgeR2MaterialProducer.toDirectCycle
#print axioms MCore.nonempty_directCycleProducer_iff_r2Producer
#print axioms MCore.directCycle_zero_witness
#print axioms MCore.directCycle_single_witness
#print axioms MCore.directCycle_of_eq_zero
#print axioms MCore.directCycle_of_eq_single
#print axioms MCore.cycleCombination_eval_append
#print axioms MCore.directCycle_add_witness

end MCore
