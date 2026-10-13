/-!
# Auditoria de vacuidade — `MCore.GradedRationalHodgeData` / `GradedRationalHodgeConjecture`

Cópia verbatim das definições de `m-core-hodge/lean/MCore/K13.lean` (só Lean core).

Resultado certificado pelo kernel: o enunciado abstrato `GradedRationalHodgeConjecture G` é
**verdadeiro para alguns `G` e falso para outros**. Ele é uma interface: só diz algo sobre a
conjectura de Hodge quando `G` é instanciado com a geometria real (variedades projetivas lisas
complexas, `H^{2p}(X, ℚ)`, tipo `(p,p)` da decomposição de Hodge, mapa de classe de ciclos).
Essa instância não existe na Mathlib v4.34.1. Por isso todo resultado do repositório formulado
sobre `G` arbitrário (K13–K26, `ConcreteAlgebraicityPayload`) é **CONDICIONAL** à construção
desse `G` real — e o próprio repositório já marca `hodge` como `openBridge`.
-/

namespace Audit.Hodge

structure GradedRationalHodgeData where
  Variety : Type
  CohomologyQ : Variety → Nat → Type
  CycleQ : Variety → Nat → Type
  isSmoothProjective : Variety → Prop
  isTypePP : {X : Variety} → (p : Nat) → CohomologyQ X (2 * p) → Prop
  inCycleClassSpan : {X : Variety} → (p : Nat) → CohomologyQ X (2 * p) → Prop

def GradedRationalHodgeConjecture (G : GradedRationalHodgeData) : Prop :=
  ∀ (X : G.Variety), G.isSmoothProjective X →
    ∀ (p : Nat) (α : G.CohomologyQ X (2 * p)),
      G.isTypePP p α → G.inCycleClassSpan p α

/-- Modelo sem variedades. -/
def emptyModel : GradedRationalHodgeData where
  Variety := Empty
  CohomologyQ := fun _ _ => Unit
  CycleQ := fun _ _ => Unit
  isSmoothProjective := fun _ => True
  isTypePP := fun _ _ => True
  inCycleClassSpan := fun _ _ => False

/-- Modelo com uma "variedade" e uma classe (p,p) fora do span. -/
def badModel : GradedRationalHodgeData where
  Variety := Unit
  CohomologyQ := fun _ _ => Unit
  CycleQ := fun _ _ => Unit
  isSmoothProjective := fun _ => True
  isTypePP := fun _ _ => True
  inCycleClassSpan := fun _ _ => False

/-- Verdadeiro (vacuamente) no modelo vazio. -/
theorem hodge_emptyModel : GradedRationalHodgeConjecture emptyModel :=
  fun X => Empty.elim X

/-- Falso no modelo ruim. -/
theorem not_hodge_badModel : ¬ GradedRationalHodgeConjecture badModel :=
  fun h => h () trivial 0 () trivial

/-- Logo o enunciado abstrato não é teorema nem negação de teorema: depende só de `G`. -/
theorem abstract_statement_independent :
    (∃ G, GradedRationalHodgeConjecture G) ∧ (∃ G, ¬ GradedRationalHodgeConjecture G) :=
  ⟨⟨emptyModel, hodge_emptyModel⟩, ⟨badModel, not_hodge_badModel⟩⟩

/-! ## Linha de explosão (formato NS: testemunha / refutação / dicotomia)

A explosão de Hodge é uma classe de Hodge racional que NÃO é algébrica. Sobre a interface `G`
o formato é exato; para valer sobre a conjectura de Hodge, `G` tem de ser a geometria real
(não disponível na Mathlib v4.34.1). -/

/-- Testemunha de explosão: classe de tipo `(p,p)` fora do span das classes de ciclos. -/
structure HodgeExplosion (G : GradedRationalHodgeData) where
  X : G.Variety
  smooth : G.isSmoothProjective X
  p : Nat
  α : G.CohomologyQ X (2 * p)
  typePP : G.isTypePP p α
  notAlgebraic : ¬ G.inCycleClassSpan p α

theorem explosion_refutes {G : GradedRationalHodgeData} (w : HodgeExplosion G) :
    ¬ GradedRationalHodgeConjecture G :=
  fun h => w.notAlgebraic (h w.X w.smooth w.p w.α w.typePP)

/-- Dicotomia: Hodge (sobre `G`) ⇔ não existe explosão. -/
theorem hodge_iff_no_explosion (G : GradedRationalHodgeData) :
    GradedRationalHodgeConjecture G ↔ ¬ Nonempty (HodgeExplosion G) := by
  constructor
  · intro h ⟨w⟩
    exact explosion_refutes w h
  · intro h X hX p α hpp
    exact Classical.byContradiction fun hn => h ⟨⟨X, hX, p, α, hpp, hn⟩⟩

/-- No modelo ruim a explosão existe — o formato não é vazio. -/
theorem badModel_explodes : Nonempty (HodgeExplosion badModel) :=
  ⟨⟨(), trivial, 0, (), trivial, fun h => h⟩⟩

end Audit.Hodge

#print axioms Audit.Hodge.hodge_emptyModel
#print axioms Audit.Hodge.not_hodge_badModel
#print axioms Audit.Hodge.abstract_statement_independent
#print axioms Audit.Hodge.explosion_refutes
#print axioms Audit.Hodge.hodge_iff_no_explosion
#print axioms Audit.Hodge.badModel_explodes
