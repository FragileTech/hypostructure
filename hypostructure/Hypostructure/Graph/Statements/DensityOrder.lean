import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.DensityOrder

/-!
# Statements: the density order at `[146]`-no, made exact

On the no arm of node `[146]` (`θ ≥ 1/78`) the route-8 rate reading gives the
linear lower bound `δ·n ≤ A·p + D·T(n)` on G's canonical packing `P₀`, with

  `A = δ·order + (δs+1)·(δ·order − 2(order−1))`,  `D = (δs+1) + δ·F·s`

(the manuscript's `234` and `109`).  Against it stand the two log-scaled density
caps of the manuscript's `θ ≤ θ_win + o(1)`: the entropy count of a realized
window package (`[158]` yes, `lem:p13-window-package`, no slack), and node
`[24]`'s density cap on the bounded arm of `[153]` (`prop:p13-density`, slack
`densitySlack·rate`).  Each pair gives the single combined bound
`Graph.DensityOrderBound`; the explicit cutoff `Graph.densityOrderCutoff` is the
`N₀` past which that bound is false.  The two size predicates below are the
exact dichotomy `N₀ ≤ n` / `n < N₀` at G's order.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- `A = δ·order + (δs+1)·(δ·order − 2(order−1))`: the packing coefficient of
the `[146]`-no lower bound (the manuscript's `234`). -/
def densityOrderPackingCoeff (data : Parameters) : Nat :=
  data.threshold * data.windowOrder +
    (data.threshold * data.dischargeScale + 1) * coldExternalStubCount data

/-- `D = (δs+1) + δ·F·s`: the surplus coefficient of the `[146]`-no lower
bound (the manuscript's `109`). -/
def densityOrderSurplusCoeff (data : Parameters) : Nat :=
  (data.threshold * data.dischargeScale + 1) +
    data.threshold * (data.bridgeMassFactor * data.dischargeScale)

/-- The slack of node `[24]`'s density cap: `densitySlack·rate`. -/
noncomputable def boundedDensityOrderSlack (data : Parameters) : Nat :=
  data.densitySlack * data.windowRate

/-- **Realized package against `[146]` no: the combined bound at G.**  The
entropy count of the realized package, `2·rate·log₂n·p ≤ (log₂n+1)(δn+T)`, and
the `[146]`-no lower bound `δn ≤ A·p + D·T`, combined at `P₀`. -/
def RealizedDensityOrderStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.DensityOrderBound (densityOrderPackingCoeff data) (densityOrderSurplusCoeff data)
    data.windowRate 0 data.threshold object.vertexCount (Nat.log2 object.vertexCount)
    (data.surplusThreshold object.vertexCount)

/-- **`N₀ ≤ n` for the realized arm.** -/
def RealizedOrderLargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.SufficientlyLargeForDensityOrder (densityOrderPackingCoeff data)
    (densityOrderSurplusCoeff data) data.windowRate 0 data.spineScale data.threshold
    object.vertexCount

/-- **`n < N₀` for the realized arm**: G is a counterexample below the cutoff
(the exact complement of `RealizedOrderLargeStatement`). -/
def RealizedOrderSmallStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ RealizedOrderLargeStatement data object

/-- **`[24]` against `[146]` no: the combined bound at G.**  Node `[24]`'s
density cap `2·rate·log₂n·p ≤ (log₂n+1)(δn+T) + densitySlack·rate·log₂n·T` and
the `[146]`-no lower bound, combined at `P₀`. -/
noncomputable def BoundedDensityOrderStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.DensityOrderBound (densityOrderPackingCoeff data) (densityOrderSurplusCoeff data)
    data.windowRate (boundedDensityOrderSlack data) data.threshold object.vertexCount
    (Nat.log2 object.vertexCount) (data.surplusThreshold object.vertexCount)

/-- **`N₀ ≤ n` for the `[24]` arm.** -/
noncomputable def BoundedOrderLargeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.SufficientlyLargeForDensityOrder (densityOrderPackingCoeff data)
    (densityOrderSurplusCoeff data) data.windowRate (boundedDensityOrderSlack data)
    data.spineScale data.threshold object.vertexCount

/-- **`n < N₀` for the `[24]` arm** (the exact complement). -/
noncomputable def BoundedOrderSmallStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ¬ BoundedOrderLargeStatement data object

end Hypostructure.Graph.Strategy.Spine
