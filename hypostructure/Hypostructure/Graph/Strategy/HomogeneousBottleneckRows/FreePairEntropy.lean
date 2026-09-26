import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Nodes `[131]`, `[137]` and `[138]`: the entropy count, the certified capacity
ledger, and the square-root surplus estimate

`prop:sparse-entropy-sandwich-with-blockers` rests on one count —
`lem:independent-target-entropy` with `lem:skeleton-dominates`: the mixed family
`ℐ_spine ∪ ℛ_Π` realizes its full code among the labelled skeletons of the
current object.  Per the methodology it is a decision on the literal residual:
the yes arm carries the count and continues the manuscript's chain, the no arm is
the residual on which it fails, carried as its own branch.  On the yes arm the
rest is arithmetic already proved in `Graph.SparsePressureLedger`. -/

/-- Node `[131]`: the entropy count of `prop:sparse-entropy-sandwich` at the full
pair schedule — decided on the literal independent residual of `[130]`. -/
noncomputable def freePairEntropyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .independentPairFamily) known]
    [FactKeys.Has (K .incrementalSkeletonRoom) known]
    (sandwichFresh : K .freePairEntropySandwich ∉ known)
    (unrealizedFresh : K .freePairCodeUnrealized ∉ known) :
    Decision (K .freePairEntropySandwich) (K .freePairCodeUnrealized) previous := by
  classical
  let baseline := (previous.get (K .baselineSpineDemand)).down
  let Coordinate := Classical.choose baseline.2
  let coordinatePackage := Classical.choose_spec baseline.2
  let family := Classical.choose coordinatePackage
  let supportPackage := Classical.choose_spec coordinatePackage
  let coordinateSupport := Classical.choose supportPackage
  let properties := Classical.choose_spec supportPackage
  have survives := properties.1
  have realization : Nonempty
      (Graph.BaselineCodeRealization current.object family) := properties.2.1
  have demand : Graph.cubicBaselineBudget current.object.vertexCount
      data.threshold ≤ 2 ^ (family.card + Graph.spineDeficit
        current.object.vertexCount data.threshold family.card) := properties.2.2.1
  have deficitBound : Graph.spineDeficit current.object.vertexCount
      data.threshold family.card ≤ data.surplusScale * current.object.vertexCount :=
    properties.2.2.2
  let pairFacts := (previous.get (K .independentPairFamily)).down
  let active := Classical.choose pairFacts
  let activation := Graph.pairResponseActivation active
  let pairs := current.object.portPairSchedule data.threshold
  let responses := activation.pairFamily pairs
  have pairBlockerFree : ¬ Graph.HasSparsePairDEBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation pairs :=
    Classical.choose_spec pairFacts
  have responseCard : responses.card =
      (current.object.degreeSurplus data.threshold).choose 2 := by
    rw [Graph.FiniteObject.DemandActivation.card_pairFamily]
    exact current.object.card_portPairSchedule fun vertex =>
      le_trans current.baseline (current.object.minDegree_le_degree vertex)
  let entropy : Prop :=
    2 ^ (family.card + responses.card) ≤ Graph.skeletonBudget current.object
  exact Decision.run previous (K .freePairEntropySandwich)
    (K .freePairCodeUnrealized)
    `Hypostructure.Graph.Strategy.Spine.freePairEntropyDichotomy
    (if realized : entropy then
      let count :
          2 ^ (family.card +
              (current.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget current.object := by
        simpa only [entropy, responseCard] using realized
      let room := (previous.get (K .incrementalSkeletonRoom)).down.1
      let sandwich :
          2 ^ (current.object.degreeSurplus data.threshold).choose 2 ≤
            2 ^ Graph.spineDeficit current.object.vertexCount data.threshold
                family.card *
              current.object.vertexCount ^
                (current.object.edgeCount -
                  Graph.cubicBaselineEdgeCount current.object.vertexCount
                    data.threshold) := by
        have chain :
            2 ^ family.card *
                2 ^ (current.object.degreeSurplus data.threshold).choose 2 ≤
              2 ^ family.card *
                (2 ^ Graph.spineDeficit current.object.vertexCount
                    data.threshold family.card *
                  current.object.vertexCount ^
                    (current.object.edgeCount -
                      Graph.cubicBaselineEdgeCount current.object.vertexCount
                        data.threshold)) := by
          calc
            2 ^ family.card *
                  2 ^ (current.object.degreeSurplus data.threshold).choose 2
                = 2 ^ (family.card +
                    (current.object.degreeSurplus data.threshold).choose 2) := by
                    rw [pow_add]
            _ ≤ Graph.skeletonBudget current.object := count
            _ ≤ Graph.cubicBaselineBudget current.object.vertexCount
                    data.threshold *
                  current.object.vertexCount ^
                    (current.object.edgeCount -
                      Graph.cubicBaselineEdgeCount current.object.vertexCount
                        data.threshold) := room
            _ ≤ 2 ^ (family.card + Graph.spineDeficit
                    current.object.vertexCount data.threshold family.card) *
                  current.object.vertexCount ^
                    (current.object.edgeCount -
                      Graph.cubicBaselineEdgeCount current.object.vertexCount
                        data.threshold) :=
                Nat.mul_le_mul_right _ demand
            _ = 2 ^ family.card *
                  (2 ^ Graph.spineDeficit current.object.vertexCount
                      data.threshold family.card *
                    current.object.vertexCount ^
                      (current.object.edgeCount -
                        Graph.cubicBaselineEdgeCount current.object.vertexCount
                          data.threshold)) := by
                rw [pow_add, Nat.mul_assoc]
        exact Nat.le_of_mul_le_mul_left chain
          (Nat.two_pow_pos family.card)
      let result : FreePairEntropySandwichStatement data current.object :=
        ⟨Coordinate, family, coordinateSupport, survives, realization, demand,
          deficitBound, count, sandwich⟩
      .inl ⟨result⟩
    else
      let countFailure :
          ¬ 2 ^ (family.card +
              (current.object.degreeSurplus data.threshold).choose 2) ≤
            Graph.skeletonBudget current.object := by
        simpa only [entropy, responseCard] using realized
      have scheduleCard : pairs.card =
          (current.object.degreeSurplus data.threshold).choose 2 :=
        current.object.card_portPairSchedule fun vertex =>
          le_trans current.baseline
            (current.object.minDegree_le_degree vertex)
      have countFailureOnSchedule :
          ¬ 2 ^ (family.card + pairs.card) ≤
            Graph.skeletonBudget current.object := by
        simpa only [scheduleCard] using countFailure
      let baselineRealization := Classical.choice realization
      have pairsNonempty : pairs.Nonempty :=
        freeSide_nonempty_of_baseline_realized baselineRealization
          countFailureOnSchedule
      let firstWitness :
          FirstFailedPairExtension current.object family pairs :=
        firstFailedPairExtensionOf baselineRealization countFailureOnSchedule
      let result : FreePairCodeUnrealizedStatement data current.object :=
        ⟨active, Coordinate, family, coordinateSupport, pairBlockerFree,
          survives, realization, demand, deficitBound, scheduleCard,
          countFailureOnSchedule, pairsNonempty, ⟨firstWitness⟩⟩
      .inr ⟨result⟩)
    sandwichFresh unrealizedFresh

end Hypostructure.Graph.Strategy.Spine
