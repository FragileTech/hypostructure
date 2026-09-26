import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.SparseUpperEnvelope

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[137]` on the free-pair arm, entered by `[131]`'s "count holds" edge:
the coupled excess test `D_all > 0?` of
`prop:single-graph-sparse-pressure-routing`.  The yes arm is the object's own
capacity-token ledger with positive coupled excess, the same key as on the
blocked side.  On the no arm every scheduled pair is free, so the realized
`[131]` count `C(σ,2) ≤ E_spine + (σ/2+1)log₂ n` is the explicit quadratic bound
of `[138]` and `cor:spine-lower-bound-surplus-estimates` gives
`σ(G) ≤ C_sp ⌈√n⌉`. -/
noncomputable def freePairCoupledExcessDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .freePairEntropySandwich) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .surplusAbove) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) previous := by
  classical
  exact Decision.run previous (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    `Hypostructure.Graph.Strategy.Spine.freePairCoupledExcessDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePressureNearCubic).At current ⊕
          (K .sparsePressureOverload).At current) from by
      by_cases overload : Holds BranchState Presentation presentation data
          .sparsePressureOverload current.object
      · exact ⟨.inr ⟨overload⟩⟩
      · exact ⟨.inl ⟨by
          let object := current.object
          obtain ⟨_Coordinate, family, _coordinateSupport, _survives,
            _realization, demand, deficitLe, entropy, _sandwich⟩ :=
            (previous.get (K .freePairEntropySandwich)).down
          have slack : 2 * object.edgeCount =
              data.threshold * object.vertexCount +
                object.degreeSurplus data.threshold :=
            (previous.get (K .sparseSlackSurplus)).down
          have above : data.surplusThreshold object.vertexCount <
              object.degreeSurplus data.threshold :=
            (previous.get (K .surplusAbove)).down
          have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
              data.threshold ≤ object.edgeCount := by
            unfold Graph.cubicBaselineEdgeCount; omega
          have surplusPos : 0 < object.degreeSurplus data.threshold :=
            lt_of_le_of_lt (Nat.zero_le _) above
          have slackLe : object.edgeCount - Graph.cubicBaselineEdgeCount
              object.vertexCount data.threshold ≤
                object.degreeSurplus data.threshold := by
            unfold Graph.cubicBaselineEdgeCount; omega
          have sizePos : 0 < object.vertexCount :=
            object.vertexCount_pos_of_degreeSurplus_pos surplusPos
          have safety := data.quadraticSafetyScale_le_spineScale
          have estimate := Graph.surplus_le_scale_of_pairSandwich object
            (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
            (le_trans (by norm_num) data.three_le_threshold) aboveEdges family.card
            (Graph.spineDeficit object.vertexCount data.threshold family.card) demand
            deficitLe slackLe entropy sizePos safety
          change object.degreeSurplus data.threshold ≤
            data.spineScale * Core.ceilSqrt object.vertexCount
          exact estimate⟩⟩))
    nearCubicFresh overloadFresh

/-- Node `[137]`, positive coupled excess on the free-pair arm: the same `[131]`
count, `lem:sparse-slack-surplus` and the baseline demand give
`σ(G) ≤ C_sp ⌈√n⌉` (`cor:spine-lower-bound-surplus-estimates`), which is
incompatible with node `[19]`'s strict lower bound, so this arm is empty. -/
@[reducible] noncomputable def freePairSurplusEstimateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairSurplusEstimate
    { Requires := [K .freePairEntropySandwich, K .sparseSlackSurplus, K .surplusAbove]
      Produces := [K .spineSurplusEstimate]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .spineSurplusEstimate)
        (show Value BranchState Presentation presentation data
            .spineSurplusEstimate inputs.current from
          ⟨by
            classical
            let object := inputs.current.object
            obtain ⟨Coordinate, family, coordinateSupport, _survives,
              _realization, demand, deficitLe, entropy, _sandwich⟩ :=
              (inputs.get (K .freePairEntropySandwich)).down
            have slack : 2 * object.edgeCount =
                data.threshold * object.vertexCount + object.degreeSurplus data.threshold :=
              (inputs.get (K .sparseSlackSurplus)).down
            have above : data.surplusThreshold object.vertexCount <
                object.degreeSurplus data.threshold :=
              (inputs.get (K .surplusAbove)).down
            have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
                data.threshold ≤ object.edgeCount := by
              unfold Graph.cubicBaselineEdgeCount; omega
            have surplusPos : 0 < object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _) above
            have slackLe : object.edgeCount - Graph.cubicBaselineEdgeCount
                object.vertexCount data.threshold ≤ object.degreeSurplus data.threshold := by
              unfold Graph.cubicBaselineEdgeCount; omega
            have sizePos : 0 < object.vertexCount :=
              object.vertexCount_pos_of_degreeSurplus_pos surplusPos
            have safety := data.quadraticSafetyScale_le_spineScale
            have estimate := Graph.surplus_le_scale_of_pairSandwich object
              (Graph.SameTokenBlockerRoles.homogeneousTokenCap data.routingLabelBound)
              (le_trans (by norm_num) data.three_le_threshold) aboveEdges family.card
              (Graph.spineDeficit object.vertexCount data.threshold family.card) demand
              deficitLe slackLe entropy sizePos safety
            change object.degreeSurplus data.threshold ≤
              data.spineScale * Core.ceilSqrt object.vertexCount
            exact estimate⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
