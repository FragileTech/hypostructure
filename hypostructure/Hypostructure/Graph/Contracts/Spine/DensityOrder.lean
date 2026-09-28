import Hypostructure.Graph.Statements.DensityOrder
import Hypostructure.Graph.SkeletonBudget

/-!
# Contracts: the density order on the `[146]`-no arm

Proof-agnostic contract lemmas.  Each is stated over a `Graph.FiniteObject`
with the registered `Parameters` as a parameter and every paper hypothesis
explicit:

* `densityOrderLower_of_coldRoute8AtOrAbove`: node `[146]`'s no arm
  (`θ ≥ 1/78`, `def:cold-window-ledger`'s route-8 comparison failing) is the
  linear lower bound `δ·n ≤ A·p + D·T(n)` at the canonical packing;
* `realizedDensityOrder_of_realized`: with a realized window package
  (`[158]` yes; `lem:p13-window-package`, `lem:skeleton-dominates`) the
  combined order bound at G;
* `boundedDensityOrder_of_densityCap`: with node `[24]`'s density cap
  (`prop:p13-density` on the bounded arm of `[153]`) the combined order bound
  at G;
* `densityOrder_false_of_large`: the combined bound is false at every order
  past the explicit cutoff `N₀` (`Graph.densityOrderBound_false_of_large`).

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[146]`, no arm, as a linear lower bound.**  The route-8 comparison
`(δs+1)(β·p + T) + δ·F·s·T < δ·(n − order·p)` fails at the canonical packing
(`β = δ·order − 2(order−1)`), so

  `δ·n ≤ (δ·order + (δs+1)·β)·p + ((δs+1) + δ·F·s)·T(n)`,

the manuscript's `3n ≤ 234·p₁₃ + 109·T` (`θ ≥ 1/78` with its `O(√n)` terms
exact). -/
theorem densityOrderLower_of_coldRoute8AtOrAbove (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (above : ColdRoute8AtOrAboveStatement data object) :
    data.threshold * object.vertexCount ≤
      densityOrderPackingCoeff data * (canonicalWindowPacking data object).card +
        densityOrderSurplusCoeff data * data.surplusThreshold object.vertexCount := by
  have valid := (canonicalWindowPacking_spec data object).1
  have sizes := object.remainderSupport_card_add_eq valid
  unfold ColdRoute8AtOrAboveStatement ColdRoute8BelowStatement at above
  unfold densityOrderPackingCoeff densityOrderSurplusCoeff
  set p := (canonicalWindowPacking data object).card
  set R := (object.remainderSupport (canonicalWindowPacking data object)).card
  set n := object.vertexCount
  set T := data.surplusThreshold n
  set δ := data.threshold
  set k := data.windowOrder
  set β := coldExternalStubCount data
  set c := δ * data.dischargeScale + 1
  set F := data.bridgeMassFactor * data.dischargeScale
  have remainder : n - k * p = R := by omega
  rw [remainder] at above
  have le : δ * R ≤ c * (β * p + T) + δ * (F * T) := by
    omega
  have split : δ * n = δ * R + δ * (k * p) := by
    rw [← sizes]; ring
  calc δ * n = δ * R + δ * (k * p) := split
    _ ≤ c * (β * p + T) + δ * (F * T) + δ * (k * p) := by omega
    _ = (δ * k + c * β) * p + (c + δ * F) * T := by ring

/-- **The realized package against `[146]` no.**  `lem:skeleton-dominates`'
exact count turns `2^{bits·p} ≤ |𝒢_{n,m}|` with `rate·log₂n ≤ bits`, `δ ≥ 3`
and the near-cubic edge count into `2·rate·log₂n·p ≤ (log₂n+1)(δn + T)`
(`Graph.two_mul_exponent_le_scale_mul_edgeBudget`); with the `[146]`-no lower
bound this is the combined order bound at G. -/
theorem realizedDensityOrder_of_realized (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (three : 3 ≤ data.threshold)
    (scaleCount : data.separatedScaleCount object.vertexCount =
      Nat.log2 object.vertexCount)
    (bits : data.windowRate * data.separatedScaleCount object.vertexCount ≤
      windowPackageBits data object)
    (realized : WindowPackageRealizedStatement data object)
    (surplus : SurplusAtOrBelowStatement data object)
    (above : ColdRoute8AtOrAboveStatement data object) :
    RealizedDensityOrderStatement data object := by
  have lower := densityOrderLower_of_coldRoute8AtOrAbove data object above
  have lowerDegree : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => baseline.trans (object.minDegree_le_degree vertex)
  have spine := Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
    data.threshold lowerDegree
  have entropy := Graph.two_mul_exponent_le_scale_mul_edgeBudget object
    (windowPackageBits data object * (canonicalWindowPacking data object).card)
    data.threshold (data.surplusThreshold object.vertexCount) realized spine three surplus
  have scaled : data.windowRate * Nat.log2 object.vertexCount *
      (canonicalWindowPacking data object).card ≤
      windowPackageBits data object * (canonicalWindowPacking data object).card := by
    rw [← scaleCount]; exact Nat.mul_le_mul_right _ bits
  have cap : 2 * (data.windowRate * Nat.log2 object.vertexCount *
      (canonicalWindowPacking data object).card) ≤
      (Nat.log2 object.vertexCount + 1) *
        (data.threshold * object.vertexCount + data.surplusThreshold object.vertexCount) +
      0 * Nat.log2 object.vertexCount * data.surplusThreshold object.vertexCount := by
    have := Nat.mul_le_mul_left 2 scaled
    simp only [Graph.dyadicScaleCount] at entropy
    omega
  exact Graph.densityOrderBound_of_lower_cap lower cap

/-- **Node `[24]` against `[146]` no.**  `prop:p13-density`'s cap on the
bounded arm of `[153]`, read at the canonical packing (which attains the
packing number) and the registered dyadic scale count, with the `[146]`-no
lower bound: the combined order bound at G. -/
theorem boundedDensityOrder_of_densityCap (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (scaleCount : data.separatedScaleCount object.vertexCount =
      Nat.log2 object.vertexCount)
    (densityCap : DensityCapStatement data object)
    (above : ColdRoute8AtOrAboveStatement data object) :
    BoundedDensityOrderStatement data object := by
  have lower := densityOrderLower_of_coldRoute8AtOrAbove data object above
  have cardinality := (canonicalWindowPacking_spec data object).2.1
  have cap0 := densityCap.1
  rw [← cardinality, scaleCount] at cap0
  simp only [Graph.dyadicScaleCount] at cap0
  have cap : 2 * (data.windowRate * Nat.log2 object.vertexCount *
      (canonicalWindowPacking data object).card) ≤
      (Nat.log2 object.vertexCount + 1) *
        (data.threshold * object.vertexCount + data.surplusThreshold object.vertexCount) +
      boundedDensityOrderSlack data * Nat.log2 object.vertexCount *
        data.surplusThreshold object.vertexCount := by
    have e : boundedDensityOrderSlack data * Nat.log2 object.vertexCount *
        data.surplusThreshold object.vertexCount =
        data.densitySlack * (data.windowRate * Nat.log2 object.vertexCount) *
          data.surplusThreshold object.vertexCount := by
      unfold boundedDensityOrderSlack; ring
    rw [e]; exact cap0
  exact Graph.densityOrderBound_of_lower_cap lower cap

/-- **The realized order bound is false past its cutoff.** -/
theorem realizedDensityOrder_false_of_large (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (bound : RealizedDensityOrderStatement data object)
    (large : RealizedOrderLargeStatement data object) : False :=
  Graph.densityOrderBound_false_of_large bound large

/-- **The `[24]` order bound is false past its cutoff.** -/
theorem boundedDensityOrder_false_of_large (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (bound : BoundedDensityOrderStatement data object)
    (large : BoundedOrderLargeStatement data object) : False :=
  Graph.densityOrderBound_false_of_large bound large

end Hypostructure.Graph.Contracts.Spine
