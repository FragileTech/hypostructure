import Hypostructure.Graph.Statements.SurplusPair

/-!
# Contract lemmas: the entropy counts of `[131]` and `[137]`

`prop:sparse-entropy-sandwich` and `prop:sparse-entropy-sandwich-with-blockers`
rest on one count: the mixed family of the baseline spine demand and the pair
coordinates realizes its code among the labelled skeletons of the object.
When that count fails, the baseline realization and the first failed pair
extension are what the pair-code chain `[178]` consumes.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- `prop:sparse-entropy-sandwich` at the full pair schedule, cleared of
logarithms: if the mixed family of a baseline spine family `family` and all
`C(σ,2)` pair coordinates realizes its code, then
`2^{C(σ,2)} ≤ 2^{E_spine} n^{m - m₀}`. -/
theorem freePairSandwich_of_count {Coordinate : Type u}
    (family : Finset Coordinate)
    (demand : Graph.cubicBaselineBudget object.vertexCount data.threshold ≤
      2 ^ (family.card + Graph.spineDeficit object.vertexCount
        data.threshold family.card))
    (room : IncrementalSkeletonRoomStatement data object)
    (count : 2 ^ (family.card + (object.degreeSurplus data.threshold).choose 2) ≤
      Graph.skeletonBudget object) :
    2 ^ (object.degreeSurplus data.threshold).choose 2 ≤
      2 ^ Graph.spineDeficit object.vertexCount data.threshold family.card *
        object.vertexCount ^
          (object.edgeCount -
            Graph.cubicBaselineEdgeCount object.vertexCount data.threshold) := by
  have chain :
      2 ^ family.card * 2 ^ (object.degreeSurplus data.threshold).choose 2 ≤
        2 ^ family.card *
          (2 ^ Graph.spineDeficit object.vertexCount data.threshold family.card *
            object.vertexCount ^
              (object.edgeCount -
                Graph.cubicBaselineEdgeCount object.vertexCount
                  data.threshold)) := by
    calc
      2 ^ family.card * 2 ^ (object.degreeSurplus data.threshold).choose 2
          = 2 ^ (family.card + (object.degreeSurplus data.threshold).choose 2) := by
            rw [pow_add]
      _ ≤ Graph.skeletonBudget object := count
      _ ≤ Graph.cubicBaselineBudget object.vertexCount data.threshold *
            object.vertexCount ^
              (object.edgeCount -
                Graph.cubicBaselineEdgeCount object.vertexCount
                  data.threshold) := room.1
      _ ≤ 2 ^ (family.card + Graph.spineDeficit object.vertexCount
              data.threshold family.card) *
            object.vertexCount ^
              (object.edgeCount -
                Graph.cubicBaselineEdgeCount object.vertexCount
                  data.threshold) := Nat.mul_le_mul_right _ demand
      _ = 2 ^ family.card *
            (2 ^ Graph.spineDeficit object.vertexCount data.threshold
                family.card *
              object.vertexCount ^
                (object.edgeCount -
                  Graph.cubicBaselineEdgeCount object.vertexCount
                    data.threshold)) := by
            rw [pow_add, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left chain (Nat.two_pow_pos family.card)

/-- Node `[131]`, count fails: on an object at the baseline carrying the
node-`[129]` baseline spine demand, the incremental skeleton room, and a
blocker-free full pair schedule, the failure of the free-pair entropy count is
the failure for the baseline family itself, with its first failed pair
extension on the literal pair schedule. -/
theorem freePairCodeUnrealized_of_countFails
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (fails : FreePairCountFailsStatement data object)
    (baselineDemand : BaselineSpineDemandStatement data object)
    (independent : IndependentPairFamilyStatement data object)
    (room : IncrementalSkeletonRoomStatement data object) :
    FreePairCodeUnrealizedStatement data object := by
  classical
  obtain ⟨active, Coordinate, family, coordinateSupport, survives,
    realization, demand, deficitBound⟩ := baselineDemand
  have scheduleCard : (object.portPairSchedule data.threshold).card =
      (object.degreeSurplus data.threshold).choose 2 :=
    object.card_portPairSchedule fun vertex =>
      le_trans atBaseline (object.minDegree_le_degree vertex)
  have countFailure :
      ¬ 2 ^ (family.card + (object.portPairSchedule data.threshold).card) ≤
        Graph.skeletonBudget object := by
    intro count
    rw [scheduleCard] at count
    exact fails ⟨Coordinate, family, coordinateSupport, survives, realization,
      demand, deficitBound, count,
      freePairSandwich_of_count family demand room count⟩
  have blockerFree : ¬ Graph.HasSparsePairDEBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
        (object.portPairSchedule data.threshold) :=
    fun blocked => independent ⟨active, blocked⟩
  let baselineRealization := Classical.choice realization
  exact ⟨active, Coordinate, family, coordinateSupport, blockerFree,
    survives, realization, demand, deficitBound, scheduleCard, countFailure,
    freeSide_nonempty_of_baseline_realized baselineRealization countFailure,
    ⟨firstFailedPairExtensionOf baselineRealization countFailure⟩⟩

/-- Node `[137]`, free-side count fails: at the object's capacity-token ledger
and canonical pair ledger, with the node-`[129]` baseline spine demand, the
failure of the free-side entropy count is the failure for that presentation
and the baseline family, with its first failed free-pair extension. -/
theorem blockedPairCodeUnrealized_of_countFails
    (fails : BlockedPairCountFailsStatement data object)
    (capacityLedger : CapacityTokenLedgerStatement data object)
    (pairLedger : CanonicalPairLedgerStatement data object)
    (baselineDemand : BaselineSpineDemandStatement data object) :
    BlockedPairCodeUnrealizedStatement data object := by
  classical
  obtain ⟨active, capacity, activationEq, primitiveEq, primitiveLe, concrete,
    _connected⟩ := capacityLedger
  obtain ⟨_pairActive, _certificate, _pairsEq, scheduleCard, _partition,
    _incidence, _multiplicity, _blocked⟩ := pairLedger
  obtain ⟨_baselineActive, Coordinate, family, coordinateSupport, survives,
    realization, demand, deficitBound⟩ := baselineDemand
  have countFailure :
      ¬ 2 ^ (family.card +
          (Graph.freeSide object.vertexPairDecidableEq
            (object.portPairSchedule data.threshold)
            capacity.tokenOrder capacity.Eligible
            capacity.eligibleDecidable).card) ≤
        Graph.skeletonBudget object := fun count =>
    fails ⟨active, capacity, activationEq, primitiveEq, primitiveLe, concrete,
      scheduleCard, Coordinate, family, coordinateSupport, survives,
      realization, demand, deficitBound, count⟩
  let baselineRealization := Classical.choice realization
  exact ⟨active, capacity, activationEq, primitiveEq, primitiveLe, concrete,
    scheduleCard, Coordinate, family, coordinateSupport, survives, realization,
    demand, deficitBound, countFailure,
    freeSide_nonempty_of_baseline_realized baselineRealization countFailure,
    ⟨firstFailedPairExtensionOf baselineRealization countFailure⟩⟩

end Hypostructure.Graph.Contracts.SurplusPair
