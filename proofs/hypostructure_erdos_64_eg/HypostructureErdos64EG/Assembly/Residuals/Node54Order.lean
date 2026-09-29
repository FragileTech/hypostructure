import HypostructureErdos64EG.Assembly.Basic
import Hypostructure.Graph.Statements.DensityOrder

/-!
# Assembly: Residuals / Node54Order

The exact order of the bounded `[54]` subtypes at the registered presentation.

`K .realizedOrderSmall` and `K .boundedOrderSmall` are published as the
negation of `SufficientlyLargeForDensityOrder`, the conjunction of the rate
margin `A < 2r`, `0 < δ` and `N₀ ≤ n`.  The first two conjuncts are registered
constants.  This module evaluates them at `spineData` (`A = 234`, `D = 109`,
`2r = 236`, `δ = 3`) and reads the fact as its exact content about G:
`n < N₀` with `N₀ = densityOrderCutoff 234 109 118 S C_sp 3`, `S = 0`
(realized) or `S = densitySlack·118` (`[24]`).  This is a statement of the
fact, not a new fact.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

theorem spineData_densityOrderPackingCoeff :
    densityOrderPackingCoeff (spineData.{u}).toParameters = 234 := by
  have t : (spineData.{u}).toParameters.threshold = 3 := rfl
  have s : (spineData.{u}).toParameters.dischargeScale = 4 := rfl
  have o : (spineData.{u}).toParameters.windowOrder = 13 := rfl
  unfold densityOrderPackingCoeff coldExternalStubCount
  rw [t, s, o]

theorem spineData_densityOrderSurplusCoeff :
    densityOrderSurplusCoeff (spineData.{u}).toParameters = 109 := by
  have t : (spineData.{u}).toParameters.threshold = 3 := rfl
  have s : (spineData.{u}).toParameters.dischargeScale = 4 := rfl
  have b : (spineData.{u}).toParameters.bridgeMassFactor = 8 := rfl
  unfold densityOrderSurplusCoeff
  rw [t, s, b]

theorem spineData_windowRate_eq : (spineData.{u}).toParameters.windowRate = 118 :=
  (spineData.{u}).windowRate_eq_barrier.trans FiniteChecks.P13Barrier.windowRate_eq

/-- **`K .realizedOrderSmall` at the registered presentation: `n < N₀`.** -/
theorem realizedOrderSmall_lt_cutoff (object : Graph.FiniteObject.{u})
    (small : RealizedOrderSmallStatement (spineData.{u}).toParameters object) :
    object.vertexCount <
      Graph.densityOrderCutoff 234 109 118 0
        (spineData.{u}).toParameters.spineScale 3 := by
  unfold RealizedOrderSmallStatement RealizedOrderLargeStatement
    Graph.SufficientlyLargeForDensityOrder at small
  rw [spineData_densityOrderPackingCoeff, spineData_densityOrderSurplusCoeff,
    spineData_windowRate_eq] at small
  have t : (spineData.{u}).toParameters.threshold = 3 := rfl
  rw [t] at small
  by_contra notLt
  exact small ⟨by norm_num, by norm_num, not_lt.mp notLt⟩

/-- **`K .boundedOrderSmall` at the registered presentation: `n < N₀`.** -/
theorem boundedOrderSmall_lt_cutoff (object : Graph.FiniteObject.{u})
    (small : BoundedOrderSmallStatement (spineData.{u}).toParameters object) :
    object.vertexCount <
      Graph.densityOrderCutoff 234 109 118
        (boundedDensityOrderSlack (spineData.{u}).toParameters)
        (spineData.{u}).toParameters.spineScale 3 := by
  unfold BoundedOrderSmallStatement BoundedOrderLargeStatement
    Graph.SufficientlyLargeForDensityOrder at small
  rw [spineData_densityOrderPackingCoeff, spineData_densityOrderSurplusCoeff,
    spineData_windowRate_eq] at small
  have t : (spineData.{u}).toParameters.threshold = 3 := rfl
  rw [t] at small
  by_contra notLt
  exact small ⟨by norm_num, by norm_num, not_lt.mp notLt⟩

end HypostructureErdos64EG
