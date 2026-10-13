# Estado: CONDICIONAL — Conjectura de Hodge

Auditoria de 13/10/2026 sobre o commit `c95d908` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

Para toda variedade projetiva lisa complexa `X` e todo `p`, toda classe em
`H^{2p}(X, ℚ) ∩ H^{p,p}(X)` é combinação linear **racional** de classes de subvariedades
algébricas de codimensão `p`.

A Mathlib v4.34.1 não tem a decomposição de Hodge da cohomologia de variedades projetivas
complexas nem o mapa de classe de ciclos. **Estado no portão: NÃO_ENUNCIÁVEL.**

## 2. Varredura do conteúdo

11 arquivos Lean · 0 `axiom` · 0 `sorry`/`admit`. Os módulos K18–K26 já se declaram
`openBridge` para geometria, algebricidade e Hodge — correto.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Por que é condicional | O que fechar |
|---|---|---|---|
| H1 | `GradedRationalHodgeData` / `GradedRationalHodgeConjecture G` (K13) | **Certificado pelo kernel** (`audit/Vacuity.lean`): o enunciado abstrato vale num modelo (`hodge_emptyModel`) e falha noutro (`not_hodge_badModel`) — `abstract_statement_independent`. Só a instância geométrica real importa | Construir o `G` real (variedades, `H^{2p}(X,ℚ)`, tipo `(p,p)`, classe de ciclo) |
| H2 | `ConcreteAlgebraicityPayload M` (P05, K18–K26) | `hodge_iff_concretePayload` mostra que, com o adaptador `CycleSpanAdapter`, ele é **equivalente** ao enunciado sobre `G` — reformulação (o próprio repositório registra `k26_equivalent_reformulation_is_circular`) | Mesmo que H1, mais um `M` (coeficientes e operações) fiel a `ℚ` |
| H3 | Coeficientes | A versão **inteira** da conjectura é falsa (Atiyah–Hirzebruch); por isso o modelo de coeficientes tem de ser `ℚ` de verdade. K23/K24 (`FaithfulRationalCoefficientInterface`) apontam nessa direção | Instanciar com `ℚ` da Mathlib e provar a fidelidade |
| H4 | Caso `p = 1` | É teorema (Lefschetz (1,1)); serve de teste de sanidade do modelo quando o `G` real existir | Provar o caso `p = 1` no modelo como verificação |
| H5 | Compilação | Os arquivos importam `MCore.K17`, `MCore.HodgeCanonicalSemanticModel` etc., ausentes aqui. (`audit/Vacuity.lean` compila só com Lean core — workflow `vacuity-check`) | CI a partir do commit de origem (`provenance/`) |

## 3b. Linha de explosão — certificada no kernel (Lean core)

`audit/Vacuity.lean`: `HodgeExplosion G` (classe `(p,p)` fora do span das classes de ciclos),
`explosion_refutes`, `hodge_iff_no_explosion : Hodge(G) ↔ ¬ Nonempty (HodgeExplosion G)` e
`badModel_explodes` (o formato não é vazio). Vale sobre a interface `G`; sobre a conjectura real
exige o `G` geométrico (H1). Nenhuma explosão conhecida; a versão **inteira** explode
(Atiyah–Hirzebruch) — por isso os coeficientes têm de ser `ℚ`.

## 3c. Linha de fechamento

Alvo exato **não enunciável** na Mathlib v4.34.1 ⇒ não existe declaração que o portão possa
aceitar ⇒ **CLOSED_MATH = false** necessariamente. A linha passa a funcionar como nos outros
problemas quando a fundação existir (H1/Y2): então o alvo vira um tipo Lean e o mesmo
`closure_gate.py` calcula a bandeira.

## 4. Falsificador exato

Uma classe de Hodge racional em `H^{2p}(X, ℚ) ∩ H^{p,p}` de uma variedade projetiva lisa que não
é combinação racional de classes de ciclos algébricos. Não enunciável na Mathlib v4.34.1.

## 5. Condição para mudar o estado

NÃO_ENUNCIÁVEL → ABERTO quando o `G` geométrico real for formalizado; só então um fechamento pode
ser avaliado pelo portão.

---

**English summary.** Status CONDITIONAL / gate NOT STATABLE. Kernel-certified finding: the
abstract `GradedRationalHodgeConjecture G` is true for some interfaces `G` and false for others,
so every result stated over an arbitrary `G` (K13–K26, `ConcreteAlgebraicityPayload`) is
conditional on building the genuine geometric instance, which Mathlib does not yet have.
