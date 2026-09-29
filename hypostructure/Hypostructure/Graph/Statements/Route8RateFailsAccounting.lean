import Hypostructure.Graph.Statements.Route8RateFailsFlow
import Hypostructure.Graph.OrdinaryDeficiencyReserve
import Hypostructure.Graph.Statements.RouteEight
import Hypostructure.Graph.StubDeficit

/-!
# Statements: the stub-deficit identity, the window/deficit dichotomy, the entry count

G audit of `Route8RateFailsOutcome`: what would close the rate arm (an upper bound
on `def⁺(R)` below `15p`, a lower bound on the cross-window incidences, a lower
bound on the route-8 entries), built as facts about G and stated as the fact or its
exact quantitative negation.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- `exc(X) = Σ_{v∈X} max{0, d_X(v) − δ}`: the internal degree above the baseline. -/
noncomputable def remainderInternalExcess (object : Graph.FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) : Nat :=
  object.internalExcess support threshold

/-- **The stub-deficit identity at G.**  Each cut incidence `(v, w)` is charged to
the deficit unit `(v, j)` of `v` (`FiniteObject.positiveDeficiencyUnits`), or is
surplus of `v`, or is repaid by an internal excess edge: with `R = V − W(P₀)`

* `e(R,W) + exc(R) = σ(R) + def⁺(R)` and `exc(R) ≤ σ(R)`;
* the deficit units of `R` are `def⁺(R)` many and inject into the cut incidences;
* against the exact window join,
  `def⁺(R) + X + σ(R) + 2(order−1)p = δ·order·p + σ_W + exc(R)`. -/
noncomputable def Route8StubDeficitStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  (object.boundaryIncidence remainder +
        remainderInternalExcess object remainder data.threshold =
      object.positiveDeficiency remainder data.threshold +
        object.ambientSurplus remainder data.threshold) ∧
    remainderInternalExcess object remainder data.threshold ≤
      object.ambientSurplus remainder data.threshold ∧
    ((object.positiveDeficiencyUnits remainder data.threshold).card =
        object.positiveDeficiency remainder data.threshold ∧
      (object.positiveDeficiencyUnits remainder data.threshold).card ≤
        (object.windowRemainderIncidences packing).card) ∧
    object.positiveDeficiency remainder data.threshold +
        (object.crossWindowIncidences packing).card +
        object.ambientSurplus remainder data.threshold +
        2 * (data.windowOrder - 1) * packing.card =
      data.threshold * (data.windowOrder * packing.card) +
        object.ambientSurplus (object.windowSupport packing) data.threshold +
        remainderInternalExcess object remainder data.threshold

/-- **The deficit against the window stubs, or the isolated windows.**  With
`β·p = (δ·order − 2(order−1))·p` the window stub capacity (`15p`), `d = def⁺(R)`:
either `d` reaches the whole stub capacity, and then `d ≤ β·p + σ_W` and the
cross-window incidences are at most the surplus of `W` (`X + σ(R) ≤ σ_W + exc`),
or `d < β·p` and the windows feed each other, `σ_W + exc < X + σ(R)`. -/
noncomputable def Route8DeficitVsStubsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let packing := canonicalWindowPacking data object
  let remainder := object.remainderSupport packing
  let d := object.positiveDeficiency remainder data.threshold
  let σR := object.ambientSurplus remainder data.threshold
  let σW := object.ambientSurplus (object.windowSupport packing) data.threshold
  let exc := remainderInternalExcess object remainder data.threshold
  let X := (object.crossWindowIncidences packing).card
  (coldExternalStubCount data * packing.card ≤ d ∧
      d ≤ coldExternalStubCount data * packing.card + σW ∧
      X + σR ≤ σW + exc) ∨
    (d < coldExternalStubCount data * packing.card ∧ σW + exc < X + σR)

/-- **The route-8 entries from a source before the rate.**  `lem:typeA-route8-burden`
(`s·D_A(𝒳_A) ≤ N_basin`, which needs only the normalized remainder) against the
large-budget deficit test `[113]`: either the deficit test holds and the entries
number at least the remainder less the stub supply,
`|R| + s·(X + 2(order−1)p) ≤ N_basin + s·(δ·order·p + σ_W) + slack`, or it fails and
`D_A` is strictly below `|R| − s·|∂R| − slack`. -/
noncomputable def Route8EntryLowerBoundStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let routeEight : Finset
      (Graph.SupportComponents.Connected.Component object support) := by
    classical
    exact (object.canonicalPieces support).filter
      (Route8Survives data object packing)
  ∃ basinCount : Nat,
    basinCount =
      ∑ component ∈ routeEight,
        ∑ receiver ∈ Graph.VisibleEntry.saturatedReceivers object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale,
          (Graph.VisibleEntry.silentExcess object
            (object.pieceSupport support component) data.threshold
            data.dischargeScale receiver).card ∧
    Graph.TypeBEnvelopeCharge.route8Deficit object support
        data.threshold data.dischargeScale routeEight ≤ basinCount ∧
    ((support.card ≤
          Graph.TypeBEnvelopeCharge.route8Deficit object support
              data.threshold data.dischargeScale routeEight +
            data.dischargeScale * object.boundaryIncidence support +
            data.bridgeMassFactor * data.dischargeScale *
              data.surplusThreshold object.vertexCount ∧
        support.card + data.dischargeScale *
            ((object.crossWindowIncidences packing).card +
              2 * (data.windowOrder - 1) * packing.card) ≤
          basinCount + data.dischargeScale *
              (data.threshold * (data.windowOrder * packing.card) +
                object.ambientSurplus (object.windowSupport packing) data.threshold) +
            data.bridgeMassFactor * data.dischargeScale *
              data.surplusThreshold object.vertexCount) ∨
      Graph.TypeBEnvelopeCharge.route8Deficit object support
            data.threshold data.dischargeScale routeEight +
          data.dischargeScale * object.boundaryIncidence support +
          data.bridgeMassFactor * data.dischargeScale *
            data.surplusThreshold object.vertexCount <
        support.card)

end Hypostructure.Graph.Strategy.Spine
