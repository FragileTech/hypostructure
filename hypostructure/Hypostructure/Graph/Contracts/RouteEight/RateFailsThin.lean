import Hypostructure.Graph.Contracts.RouteEight.Basic
import Hypostructure.Graph.Statements.Route8RateFailsJoin

/-!
# Contracts: the failed private-carrier rate, read on the boundary incidence

(g-pieces-constructed: `K .route8Rate` is the manuscript rate again, so the failed rate
is `δ|R| ≤ (δs+1)|∂R| + δ·F·s·T(n)`; the thin remainder `|R| ≤ s|∂R| + F·s·T(n)` is a
sub-case of it, not its reading.)
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- The failed rate, with the supply read as the boundary incidence of the remainder:
`δ|R| ≤ (δs+1)|∂R| + δ·F·s·T(n)`. -/
theorem route8RateFails_oldLe (data : Parameters) (object : FiniteObject.{u})
    (fails : Route8RateFailsStatement data object) :
    data.threshold * (object.remainderSupport (canonicalWindowPacking data object)).card ≤
      (data.threshold * data.dischargeScale + 1) * object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
        data.threshold * (data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount) := by
  have supplyEq := Graph.Route8Census.card_supply object (canonicalWindowPacking data object)
  change ¬ ((data.threshold * data.dischargeScale + 1) *
      (Graph.Route8Census.supply object (canonicalWindowPacking data object)).card +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.remainderSupport (canonicalWindowPacking data object)).card)
    at fails
  rw [supplyEq] at fails
  exact Nat.le_of_not_lt fails

end Hypostructure.Graph.Contracts.RouteEight
