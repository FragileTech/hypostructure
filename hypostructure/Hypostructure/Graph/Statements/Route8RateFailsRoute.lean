import Hypostructure.Graph.Statements.Route8RateFailsAccounting
import Hypostructure.Graph.NetCharge

/-!
# Statements: cores empty at G, the strong rate, the thin remainder

G audit of `Route8RateFailsOutcome`.  At a target-avoiding G every route-`8` entry has an
empty essential core (`PresentedEntry.ofTraceBasin_alpha_eq_zero`), so an entry is a
two-carrier entry as soon as it exists.  The census therefore needs no rate of `3/13`: it
needs `|R| > s·|∂R| + F·s·T(n)` (the strong rate), and its complement is the exact thin
remainder `|R| ≤ s·|∂R| + F·s·T(n)`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **Every route-`8` core is empty at G**: each graph-owned entry of the census has
`𝓒_ess(ξ) = ∅` (`α(ξ) = 0`, completeness read in `G − B_u`). -/
noncomputable def Route8CoreEmptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ index : Graph.Route8Census.Index object,
    Graph.Route8Census.core object data.threshold data.LengthOK index = ∅

/-- **The strong rate, or the thin remainder.**  With empty cores the private-carrier
census needs only `s·|∂R| + F·s·T(n) < |R|`: then, if the large-budget deficit test `[113]`
holds, the route-`8` collection has a two-carrier entry with no use of `3/13`; the
complement is `|R| ≤ s·|∂R| + F·s·T(n)`. -/
noncomputable def Route8StrongRateStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let support := object.remainderSupport (canonicalWindowPacking data object)
  (data.dischargeScale * object.boundaryIncidence support +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount < support.card ∧
      (Route8LargeBudgetDeficit data object → Route8TwoCarrierEntryStatement data object)) ∨
    support.card ≤ data.dischargeScale * object.boundaryIncidence support +
      data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount

/-- **The thin remainder isolates the windows.**  When the net cap applies, the thin
remainder `|R| ≤ s·|∂R| + F·s·T(n)` against the cap
`s(δ·order·p + T) < s·2(order−1)p + |R|` and the exact window join leaves
`X + T(n) < σ_W + F·T(n)`: the cross-window incidences are at most the surplus of `W`
plus `(F−1)·T(n)`. -/
noncomputable def Route8ThinIsolationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold data.dischargeScale
      data.windowOrder data.windowRate data.spineScale data.densitySlack
      object.vertexCount →
    (object.remainderSupport (canonicalWindowPacking data object)).card ≤
        data.dischargeScale * object.boundaryIncidence
          (object.remainderSupport (canonicalWindowPacking data object)) +
          data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold object.vertexCount →
      (object.crossWindowIncidences (canonicalWindowPacking data object)).card +
          data.surplusThreshold object.vertexCount <
        object.ambientSurplus (object.windowSupport (canonicalWindowPacking data object))
            data.threshold +
          data.bridgeMassFactor * data.surplusThreshold object.vertexCount

/-- **The exact stub count of each window of `P₀` and its distribution.**  Every
incidence leaving a window `P` goes to the remainder or to another window
(`d_G = d_P + d_{W∖P} + d_R` at each vertex), and `P` is an induced path, so

* `exits_R(P) + exits_W(P) + 2(order−1) = δ·order + σ(P)` (`= 15 + σ(P)` stubs);
* summed over the packing, `Σ_P exits_W(P) = X` and `Σ_P exits_R(P) = |∂R|`;
* the window stubs land on at least `(|∂R| − σ(R))/δ` distinct remainder vertices
  (`|∂R| ≤ δ·|A| + σ(R)`, `A` the remainder vertices with a neighbour in `W`);

at `σ_W = 0` every window has exactly `δ·order − 2(order−1)` stubs. -/
noncomputable def Route8WindowStubStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  (∀ window ∈ packing,
      (∑ vertex ∈ window,
          object.internalDegree (object.remainderSupport packing) vertex) +
        (∑ vertex ∈ window,
          object.internalDegree (object.windowSupportOutside packing window) vertex) +
        2 * (data.windowOrder - 1) =
      data.threshold * data.windowOrder +
        object.ambientSurplus window data.threshold) ∧
    (∑ window ∈ packing, ∑ vertex ∈ window,
        object.internalDegree (object.windowSupportOutside packing window) vertex =
      (object.crossWindowIncidences packing).card) ∧
    (∑ window ∈ packing, ∑ vertex ∈ window,
        object.internalDegree (object.remainderSupport packing) vertex =
      object.boundaryIncidence (object.remainderSupport packing)) ∧
    (object.boundaryIncidence (object.remainderSupport packing) ≤
      data.threshold *
          ((object.remainderSupport packing).filter fun vertex =>
            object.internalDegree (object.remainderSupport packing) vertex <
              object.degree vertex).card +
        object.ambientSurplus (object.remainderSupport packing) data.threshold)

/-- `A' = δ·(order + s·β)`: the packing coefficient of the thin-remainder order bound
(the manuscript's `3·73 = 219`, `73 = order + s·15`). -/
def thinPackingCoeff (data : Parameters) : Nat :=
  data.threshold * (data.windowOrder + data.dischargeScale * coldExternalStubCount data)

/-- `D' = δ·s·(1 + F)`: the surplus coefficient of the thin-remainder order bound. -/
def thinSurplusCoeff (data : Parameters) : Nat :=
  data.threshold * data.dischargeScale * (1 + data.bridgeMassFactor)

/-- **The thin remainder forces a small order.**  `|R| ≤ s·|∂R| + F·s·T(n)`, the window
join (`|∂R| ≤ β·p + σ_W`, `σ_W ≤ T`) and the density cap combine into
`Graph.DensityOrderBound (thinPackingCoeff) (thinSurplusCoeff)`, which is false past its
cutoff: the order of G is below `N₀' = densityOrderCutoff` of the thin coefficients. -/
noncomputable def Route8ThinSmallStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  (object.remainderSupport (canonicalWindowPacking data object)).card ≤
      data.dischargeScale * object.boundaryIncidence
        (object.remainderSupport (canonicalWindowPacking data object)) +
        data.bridgeMassFactor * data.dischargeScale *
          data.surplusThreshold object.vertexCount →
    ¬ Graph.SufficientlyLargeForDensityOrder (thinPackingCoeff data)
      (thinSurplusCoeff data) data.windowRate (boundedDensityOrderSlack data)
      data.spineScale data.threshold object.vertexCount

end Hypostructure.Graph.Strategy.Spine
