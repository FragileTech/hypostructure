import Hypostructure.Graph.Statements.Route8RateFailsJoin
import Hypostructure.Graph.Route8Census

/-!
# Statements: the failed rate in deficit currency, the carrier injection, the exact slack

G audit of `Route8RateFailsOutcome` (coordinates H07, H06, H08).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **The integral stub-to-deficit flow at G (`H07`).**  Every cut incidence
`(v, w)`, `v ∈ R`, `w ∈ W`, is one unit of flow delivered to the remainder
vertex `v`; a vertex receives `d_G(v) − d_R(v) ≥ max{0, δ − d_R(v)}` and at most
`max{0, δ − d_R(v)} + (d_G(v) − δ)`.  Summed over `R` and over each canonical piece:

* `def⁺(X) ≤ |∂X| ≤ def⁺(X) + σ(X)` for `R` and for every piece `X` of `R`;
* against the exact window join: `δ·order·p + σ_W ≤ 2(order−1)p + X + def⁺(R) + σ(R)`
  (the window stub capacity is delivered, up to the cross-window incidences, to
  the deficit and the surplus of `R`);
* the failed rate in deficit currency:
  `δ·|R| ≤ (δs+1)·(def⁺(R) + σ(R)) + δ·F·s·T(n)`. -/
noncomputable def Route8RateFailsFlowStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  (object.positiveDeficiency remainder data.threshold ≤
        object.boundaryIncidence remainder ∧
      object.boundaryIncidence remainder ≤
        object.positiveDeficiency remainder data.threshold +
          object.ambientSurplus remainder data.threshold) ∧
    (∀ piece ∈ object.canonicalPieces remainder,
      object.positiveDeficiency (object.pieceSupport remainder piece) data.threshold ≤
          object.boundaryIncidence (object.pieceSupport remainder piece) ∧
        object.boundaryIncidence (object.pieceSupport remainder piece) ≤
          object.positiveDeficiency (object.pieceSupport remainder piece)
              data.threshold +
            object.ambientSurplus (object.pieceSupport remainder piece)
              data.threshold) ∧
    data.threshold * (data.windowOrder * packing.card) +
        object.ambientSurplus (object.windowSupport packing) data.threshold ≤
      2 * (data.windowOrder - 1) * packing.card +
        (object.crossWindowIncidences packing).card +
        object.positiveDeficiency remainder data.threshold +
        object.ambientSurplus remainder data.threshold ∧
    data.threshold * remainder.card ≤
      (data.threshold * data.dischargeScale + 1) *
          (object.positiveDeficiency remainder data.threshold +
            object.ambientSurplus remainder data.threshold) +
        data.threshold * (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount)

section Injection

attribute [local instance] Graph.Route8.vertexDecEq

/-- **The carriers-to-cut injection at G (`H06`).**  The canonical route-`8`
entries of `P₀` (`Route8Census.entries`), with their canonical essential cores:
every core lies in the cut of `R`, the private essential carriers of distinct
entries are disjoint, and their total is at most the cut, `|supply| = |∂R|`. -/
noncomputable def Route8CarrierInjectionStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let entries := Graph.Route8Census.entries object packing data.threshold
    data.dischargeScale
  let core := Graph.Route8Census.core object data.threshold data.LengthOK
  (∀ index ∈ entries, core index ⊆ Graph.Route8Census.supply object packing) ∧
    (∑ index ∈ entries,
        Graph.Route8.indexedPrivateCoreCount entries core index ≤
      (Graph.Route8Census.supply object packing).card) ∧
    (Graph.Route8Census.supply object packing).card =
      object.boundaryIncidence (object.remainderSupport packing)

end Injection

/-- **The rate at G's exact surplus, next to the ceiling version (`H08`).**
`Rate` carries the ceiling `T(n)` of `σ(G)`; with `σ(G)` itself:

* if the exact-slack rate `(δs+1)|∂R| + δ·F·s·σ(G) < δ|R|` holds, then it holds
  strictly inside the failed ceiling rate, `σ(G) < T(n)` and
  `δ·|R| − (δs+1)|∂R| ∈ (δ·F·s·σ(G), δ·F·s·T(n)]`;
* otherwise the exact-slack rate fails: `δ|R| ≤ (δs+1)|∂R| + δ·F·s·σ(G)`. -/
noncomputable def Route8RateExactSlackStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let F := data.bridgeMassFactor * data.dischargeScale
  let c := data.threshold * data.dischargeScale + 1
  (c * object.boundaryIncidence remainder +
        data.threshold * (F * object.degreeSurplus data.threshold) <
      data.threshold * remainder.card ∧
    data.threshold * (F * object.degreeSurplus data.threshold) <
      data.threshold * (F * data.surplusThreshold object.vertexCount) ∧
    data.threshold * remainder.card ≤
      c * object.boundaryIncidence remainder +
        data.threshold * (F * data.surplusThreshold object.vertexCount)) ∨
    data.threshold * remainder.card ≤
      c * object.boundaryIncidence remainder +
        data.threshold * (F * object.degreeSurplus data.threshold)

end Hypostructure.Graph.Strategy.Spine
