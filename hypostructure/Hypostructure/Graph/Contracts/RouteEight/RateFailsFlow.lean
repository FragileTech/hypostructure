import Hypostructure.Graph.Contracts.RouteEight.RateFailsJoin
import Hypostructure.Graph.Contracts.RouteEight.RateFailsPiece
import Hypostructure.Graph.Statements.Route8RateFailsFlow

/-!
# Contracts: the failed rate in deficit currency, the carrier injection, the exact slack
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- `e(X, G−X) ≤ def⁺(X) + σ(X)`: a vertex receives at most its deficiency plus
its surplus. -/
theorem boundaryIncidence_le_deficiency_add_surplus (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.boundaryIncidence support ≤
      object.positiveDeficiency support threshold +
        object.ambientSurplus support threshold := by
  unfold FiniteObject.boundaryIncidence FiniteObject.positiveDeficiency
    FiniteObject.ambientSurplus
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun vertex _ => ?_
  have := object.internalDegree_le_degree support vertex
  have := baseline vertex
  omega

/-- **The failed rate in deficit currency and the flow at G.** -/
theorem route8RateFailsFlow (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (fails : Route8RateFailsStatement data object)
    (join : Route8RateFailsJoinStatement data object) :
    Route8RateFailsFlowStatement data object := by
  have baselineAll : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  have supplyEq := Graph.Route8Census.card_supply object
    (canonicalWindowPacking data object)
  change ¬ ((data.threshold * data.dischargeScale + 1) *
      (Graph.Route8Census.supply object (canonicalWindowPacking data object)).card +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.remainderSupport (canonicalWindowPacking data object)).card)
    at fails
  rw [supplyEq] at fails
  have failsLe := Nat.not_lt.mp fails
  have lower := object.positiveDeficiency_le_boundaryIncidence
    (object.remainderSupport (canonicalWindowPacking data object))
    data.threshold baselineAll
  have upper := boundaryIncidence_le_deficiency_add_surplus object
    (object.remainderSupport (canonicalWindowPacking data object))
    data.threshold baselineAll
  have joinEq := join.1
  unfold Route8RateFailsFlowStatement
  dsimp only
  refine ⟨⟨lower, upper⟩, ?_, ?_, ?_⟩
  · intro piece _
    exact ⟨object.positiveDeficiency_le_boundaryIncidence _ data.threshold baselineAll,
      boundaryIncidence_le_deficiency_add_surplus object _ data.threshold baselineAll⟩
  · omega
  · exact le_trans failsLe (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ upper) _)

section Injection

attribute [local instance] Route8.vertexDecEq

/-- **The carriers-to-cut injection at G.** -/
theorem route8CarrierInjection (data : Parameters) (object : FiniteObject.{u}) :
    Route8CarrierInjectionStatement data object := by
  unfold Route8CarrierInjectionStatement
  have subset := Route8Census.core_subset_supply object
    (canonicalWindowPacking data object) data.threshold data.dischargeScale
    data.LengthOK
  refine ⟨subset, ?_, Route8Census.card_supply object _⟩
  exact Route8.indexedPrivateCoreCarriers_card_sum_le_supply _ _ _ subset

end Injection

/-- **The rate at G's exact surplus.** -/
theorem route8RateExactSlack (data : Parameters) (object : FiniteObject.{u})
    (fails : Route8RateFailsStatement data object) :
    Route8RateExactSlackStatement data object := by
  set packing := canonicalWindowPacking data object with hpack
  have supplyEq := Graph.Route8Census.card_supply object packing
  change ¬ ((data.threshold * data.dischargeScale + 1) *
      (Graph.Route8Census.supply object packing).card +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.remainderSupport packing).card) at fails
  rw [supplyEq] at fails
  have failsLe := Nat.not_lt.mp fails
  unfold Route8RateExactSlackStatement
  by_cases exact : (data.threshold * data.dischargeScale + 1) *
      object.boundaryIncidence (object.remainderSupport packing) +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        object.degreeSurplus data.threshold) <
      data.threshold * (object.remainderSupport packing).card
  · left
    refine ⟨exact, ?_, ?_⟩
    · have e1 : data.threshold * (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount) =
          data.threshold * ((data.bridgeMassFactor * data.dischargeScale) *
          data.surplusThreshold object.vertexCount) := rfl
      omega
    · exact failsLe
  · right
    exact Nat.not_lt.mp exact

end Hypostructure.Graph.Contracts.RouteEight
