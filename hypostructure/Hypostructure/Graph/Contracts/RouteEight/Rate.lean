import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: the private-carrier rate on the cold `[147]` arm

`rem:route8-carrier-margin` with `lem:surplus-aware-window-stub`: on the cold
arm below the route-`8` rate threshold the census rate reading holds.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`rem:route8-carrier-margin` on the `[147]` arm**: `|∂R| = e(R,W) ≤
stubs·p + σ_W ≤ stubs·p + T(n)`, so the cold route-`8` bound gives the census
rate `(δs+1)·|∂R| + δ·F·s·T(n) < δ·|R|`. -/
theorem route8RateFromColdBelow (data : Parameters) (object : FiniteObject.{u})
    (baseline : data.threshold ≤ object.minDegree)
    (threeLe : 3 ≤ data.threshold)
    (below : ColdRoute8BelowStatement data object)
    (ceiling : SurplusAtOrBelowStatement data object) :
    Route8RateStatement data object := by
  set packing := canonicalWindowPacking data object with hpack
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    degree_ge_of_minDegree data object baseline
  -- `lem:surplus-aware-window-stub`'s capacity link, read off the object
  -- (the same derivation node `[28]` publishes).
  have capacity := object.boundaryIncidence_add_internal_mass_le valid baseline
  have windowSurplus :
      object.ambientSurplus (Graph.FiniteObject.windowSupport packing)
          data.threshold ≤ data.surplusThreshold object.vertexCount :=
    le_trans (object.ambientSurplus_le_degreeSurplus _ data.threshold baseline)
      ceiling
  have supplyEq := Graph.Route8Census.card_supply object packing
  have remainder := object.remainderSupport_card_add_eq valid
  change (data.threshold * data.dischargeScale + 1) *
      (coldExternalStubCount data * packing.card +
        data.surplusThreshold object.vertexCount) +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.vertexCount - data.windowOrder * packing.card) at below
  suffices old : (data.threshold * data.dischargeScale + 1) *
      (Graph.Route8Census.supply object packing).card +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
    data.threshold * (object.remainderSupport packing).card by
    exact Graph.Route8Census.strongRate_of_rate object packing data.threshold
      data.dischargeScale _ old
  rw [supplyEq]
  have remEq : object.vertexCount - data.windowOrder * packing.card =
      (object.remainderSupport packing).card := by omega
  rw [remEq] at below
  have debit : 2 * (data.windowOrder - 1) ≤ data.threshold * data.windowOrder := by
    have := threeLe
    have := Nat.mul_le_mul_right data.windowOrder this
    omega
  have prod : coldExternalStubCount data * packing.card =
      data.threshold * (data.windowOrder * packing.card) -
        2 * (data.windowOrder - 1) * packing.card := by
    simp only [coldExternalStubCount]
    rw [Nat.sub_mul, Nat.mul_assoc]
  have debit' : 2 * (data.windowOrder - 1) * packing.card ≤
      data.threshold * (data.windowOrder * packing.card) := by
    have := Nat.mul_le_mul_right packing.card debit
    rw [Nat.mul_assoc data.threshold] at this
    exact this
  have supplyLe : object.boundaryIncidence (object.remainderSupport packing) ≤
      coldExternalStubCount data * packing.card +
        data.surplusThreshold object.vertexCount := by
    rw [prod]
    omega
  have := Nat.mul_le_mul_left (data.threshold * data.dischargeScale + 1) supplyLe
  omega

end Hypostructure.Graph.Contracts.RouteEight
