import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Statements.Route8RateFailsJoin

/-!
# Contracts: the failed rate is the thin remainder, which implies the old failed rate
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The failed strong rate is the thin remainder `|R| ≤ s|∂R| + F·s·T(n)`. -/
theorem route8Thin_of_fails (data : Parameters) (object : FiniteObject.{u})
    (fails : Route8RateFailsStatement data object) :
    (object.remainderSupport (canonicalWindowPacking data object)).card ≤
      data.dischargeScale * object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount := by
  have supplyEq := Graph.Route8Census.card_supply object (canonicalWindowPacking data object)
  change ¬ (data.dischargeScale *
      (Graph.Route8Census.supply object (canonicalWindowPacking data object)).card +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount <
      (object.remainderSupport (canonicalWindowPacking data object)).card) at fails
  rw [supplyEq] at fails
  exact Nat.le_of_not_lt fails

/-- The thin remainder implies the manuscript's failed rate
`δ|R| ≤ (δs+1)|∂R| + δ·F·s·T(n)`. -/
theorem route8RateFails_oldLe (data : Parameters) (object : FiniteObject.{u})
    (fails : Route8RateFailsStatement data object) :
    data.threshold * (object.remainderSupport (canonicalWindowPacking data object)).card ≤
      (data.threshold * data.dischargeScale + 1) * object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
        data.threshold * (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount) := by
  have thin := route8Thin_of_fails data object fails
  have scaled := Nat.mul_le_mul_left data.threshold thin
  have e1 : (data.threshold * data.dischargeScale + 1) * object.boundaryIncidence
      (object.remainderSupport (canonicalWindowPacking data object)) =
      data.threshold * data.dischargeScale * object.boundaryIncidence
        (object.remainderSupport (canonicalWindowPacking data object)) +
        object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) := by ring
  have e2 : data.threshold * (data.dischargeScale * object.boundaryIncidence
      (object.remainderSupport (canonicalWindowPacking data object)) +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) =
      data.threshold * data.dischargeScale * object.boundaryIncidence
        (object.remainderSupport (canonicalWindowPacking data object)) +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) := by ring
  omega

end Hypostructure.Graph.Contracts.RouteEight
