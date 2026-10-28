import MCore.BackwardAudit.HodgeLastBitFrontier

namespace MCore.BackwardAudit

/--
Abstract algebraic criterion for the proposed "Hodge = -Hodge" closure.

The operation called `opp` is intentionally abstract here because the current
CycleSpanMechanics interface does not expose a quotient-space negation.
-/
structure OppositionSpace (A : Type) where
  zero : A
  opp : A → A
  opp_involutive : ∀ x, opp (opp x) = x

def SelfOpposed {A : Type} (O : OppositionSpace A) (x : A) : Prop :=
  x = O.opp x

def Vanishes {A : Type} (O : OppositionSpace A) (x : A) : Prop :=
  x = O.zero

/--
The exact extra algebraic law needed for self-opposition to force vanishing.
In a rational vector-space quotient this follows from absence of 2-torsion,
but that vector-space quotient is not yet part of CycleSpanMechanics.
-/
def SelfOppositionCollapses {A : Type} (O : OppositionSpace A) : Prop :=
  ∀ x, SelfOpposed O x → Vanishes O x

theorem self_opposition_closes
    {A : Type} {O : OppositionSpace A}
    (C : SelfOppositionCollapses O)
    {x : A} (h : SelfOpposed O x) :
    Vanishes O x :=
  C x h

/--
Involution alone is insufficient.  The identity involution on Bool has a
nonzero self-opposed point.
-/
def boolIdentityOpposition : OppositionSpace Bool :=
  {
    zero := false
    opp := id
    opp_involutive := by intro x; rfl
  }

theorem involution_alone_does_not_force_vanishing :
    SelfOpposed boolIdentityOpposition true ∧
    ¬ Vanishes boolIdentityOpposition true := by
  constructor
  · rfl
  · intro h
    cases h

/--
Therefore a proposed Hodge obstruction self-opposition proof has two genuine
obligations: construct the obstruction in an opposition space with collapse,
and prove the obstruction is self-opposed.  Neither follows from involution
alone.
-/
structure HodgeOppositionClosureWitness where
  A : Type
  O : OppositionSpace A
  obstruction : A
  collapse : SelfOppositionCollapses O
  selfOpposed : SelfOpposed O obstruction

def HodgeOppositionClosureWitness.vanishes
    (W : HodgeOppositionClosureWitness) :
    Vanishes W.O W.obstruction :=
  W.collapse W.obstruction W.selfOpposed

#print axioms MCore.BackwardAudit.self_opposition_closes
#print axioms MCore.BackwardAudit.involution_alone_does_not_force_vanishing
#print axioms MCore.BackwardAudit.HodgeOppositionClosureWitness.vanishes

end MCore.BackwardAudit
