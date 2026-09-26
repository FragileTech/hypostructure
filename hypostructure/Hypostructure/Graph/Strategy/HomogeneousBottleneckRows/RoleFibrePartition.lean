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

/-- Node `[137]`, first production: `lem:exact-surplus-pair-charge-partition`
with `thm:sharp-classwise-homogeneous-token-budget` (a)--(c) and
`thm:sharp-surplus-overload-audit` (b)--(c), for the literal presentation and
free-side entropy count already written to the incoming ledger. -/
@[reducible] noncomputable def roleFibrePartitionRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.roleFibrePartition
    { Requires := [K .blockedPairEntropySandwich, K .sparseSlackSurplus,
        K .surplusAbove]
      Produces := [K .roleFibrePartition]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .roleFibrePartition)
        (show Value BranchState Presentation presentation data
            .roleFibrePartition inputs.current from
          ⟨by
            classical
            let object := inputs.current.object
            obtain ⟨active, capacity, activationEq, _primitiveEq,
                _primitiveLe, concrete,
                scheduleCard, Coordinate, family, coordinateSupport,
                _survives, _realization, demand, deficitLe, entropy⟩ :=
              (inputs.get (K .blockedPairEntropySandwich)).down
            have slack : 2 * object.edgeCount =
                data.threshold * object.vertexCount +
                  object.degreeSurplus data.threshold :=
              (inputs.get (K .sparseSlackSurplus)).down
            have above : data.surplusThreshold object.vertexCount <
                object.degreeSurplus data.threshold :=
              (inputs.get (K .surplusAbove)).down
            have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount
                data.threshold ≤ object.edgeCount := by
              unfold Graph.cubicBaselineEdgeCount
              omega
            have surplusPos : 0 < object.degreeSurplus data.threshold :=
              lt_of_le_of_lt (Nat.zero_le _) above
            have slackLe : object.edgeCount -
                Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
                  object.degreeSurplus data.threshold := by
              unfold Graph.cubicBaselineEdgeCount
              omega
            have sizePos : 0 < object.vertexCount :=
              object.vertexCount_pos_of_degreeSurplus_pos surplusPos
            obtain ⟨vertex, _vertexMem⟩ : object.vertexFinset.Nonempty :=
              Finset.card_pos.mp (by
                rw [object.card_vertexFinset]
                exact sizePos)
            let certified : Graph.CertifiedObjectCapacityLedger object
                data.threshold data.windowOrder data.surplusScale capacity :=
              Graph.certifiedLedger_of_sandwich capacity
                (le_trans (by norm_num) data.three_le_threshold) aboveEdges
                family.card
                (Graph.spineDeficit object.vertexCount data.threshold family.card)
                demand deficitLe slackLe entropy scheduleCard
                (object.capacityTokens_nonempty data.threshold capacity.packing vertex)
                concrete.2.1
            let ledger := certified.ledger
            refine ⟨active, capacity, activationEq, certified, ?_⟩
            refine ⟨ledger.presented.choose_two_eq_free_add_sum_roleFibre
                ledger.presented.tokenClass,
              fun token => ledger.presented.load_eq_sum_roleFibre token,
              ledger.presented.classwise_split.1.1,
              ledger.presented.classwise_split.1.2,
              ledger.presented.classwise_split.2,
              ledger.presented.subtype_split.1.1,
              ledger.presented.subtype_split.2, ?_⟩
            intro patternBound positive value noMatching noStar
            exact ledger.presented.grainLoad_le_of_no_homogeneous
              ledger.presented.tokenClass value patternBound positive
              noMatching noStar⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
