import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: the failed exact collision against the private-carrier rate

`lem:exact-collision-test` (node `[173]`, tex 7883) against
`lem:dense-deficiency-routing` / `rem:route8-carrier-margin` (node `[160]`,
nodes `[120]`--`[122]`).  At the remainder `R₀` of the fixed maximum packing
`P₀`, a nonnegative net charge reads `τ ≥ 1/4`, a passing private-carrier rate
reads `τ < 3/13`, and `3/13 < 1/4`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[173]` no-arm against the private-carrier rate.**  At `R₀`:
the failed collision `|R₀| + s·σ(R₀) ≤ s·def⁺(R₀)`, the boundary demand
`def⁺(R₀) ≤ e(R₀,W)` of node `[29]`, and the census rate
`(δs+1)·e(R₀,W) + δ·slack < δ·|R₀|` give
`δ·|R₀| ≤ δs·def⁺(R₀) ≤ δs·e(R₀,W) ≤ (δs+1)·e(R₀,W) < δ·|R₀|`. -/
theorem exactCollisionFails_route8Rate_false (data : Parameters)
    (object : FiniteObject.{u})
    (demand : BoundaryDemandStatement data object)
    (rate : Route8RateStatement data object)
    (fails : ExactCollisionFailsStatement data object) : False := by
  have nonnegative : _ := fails
  simp only [ExactCollisionFailsStatement,
    Graph.FiniteObject.NonNegativeNetCharge] at nonnegative
  have census : _ := rate
  unfold Route8RateStatement Graph.Route8Census.StrongRate at census
  rw [Graph.Route8Census.card_supply] at census
  have deficiencyLe := demand.1
  have scaled := Nat.mul_le_mul_left data.dischargeScale deficiencyLe
  omega

end Hypostructure.Graph.Contracts.RouteEight
