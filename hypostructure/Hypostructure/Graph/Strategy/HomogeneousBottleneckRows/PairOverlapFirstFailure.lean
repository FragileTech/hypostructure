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

/-! ## Node `[178]`: normalize the first failed pair extension

The two count-failure routes retain different pair sets, but both now carry
the same mathematical datum: an actually realized baseline code and the least
pair extension at which the mixed count fails.  These rows read that witness
from the route's exact key and attach the failed pair's canonical connected
response support `X_π`. -/

/-- Node `[178]` on the full pair schedule selected at `[131]`. -/
@[reducible] noncomputable def freePairOverlapFirstFailureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.freePairOverlapFirstFailure
    { Requires := [K .freePairCodeUnrealized, K .noProperBaseline]
      Produces := [K .pairOverlapFirstFailure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapFirstFailure)
        (show Value BranchState Presentation presentation data
            .pairOverlapFirstFailure inputs.current from
          ⟨by
            obtain ⟨active, Coordinate, family, coordinateSupport,
                blockerFree, _survives, realizationExists, _demand, _deficitBound,
                _scheduleCard, _countFailure, pairSetNonempty,
                firstFailureExists⟩ :=
              (inputs.get (K .freePairCodeUnrealized)).down
            let realization := Classical.choice realizationExists
            let firstFailure := Classical.choice firstFailureExists
            exact ⟨PairOverlapFirstFailure.of data.toParameters inputs.current.object active
              Coordinate family coordinateSupport realization
              (inputs.current.object.portPairSchedule data.threshold)
              pairSetNonempty (by intro pair member; exact member)
              (by
                intro pair pairMem
                constructor
                · intro obstruction
                  exact blockerFree ⟨pair, pairMem, Or.inl obstruction⟩
                · intro obstruction
                  exact blockerFree ⟨pair, pairMem, Or.inr obstruction⟩)
              firstFailure
              (inputs.get (K .noProperBaseline)).down.2⟩⟩)
        .nil)

/-- Node `[178]` on the literal capacity-free side selected at `[137]`. -/
@[reducible] noncomputable def blockedPairOverlapFirstFailureRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.blockedPairOverlapFirstFailure
    { Requires := [K .blockedPairCodeUnrealized, K .noProperBaseline]
      Produces := [K .pairOverlapFirstFailure]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairOverlapFirstFailure)
        (show Value BranchState Presentation presentation data
            .pairOverlapFirstFailure inputs.current from
          ⟨by
            obtain ⟨active, capacity, activationEq, _primitiveEq,
                _primitiveLe, _concrete, _scheduleCard, Coordinate, family,
                coordinateSupport, _survives, realizationExists, _demand,
                _deficitBound, _countFailure, pairSetNonempty,
                firstFailureExists⟩ :=
              (inputs.get (K .blockedPairCodeUnrealized)).down
            let pairSet := Graph.freeSide
              inputs.current.object.vertexPairDecidableEq
              (inputs.current.object.portPairSchedule data.threshold)
              capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable
            let realization := Classical.choice realizationExists
            let firstFailure := Classical.choice firstFailureExists
            let activation := Graph.pairResponseActivation active
            let recorded := Graph.recordSparsePairDEBlockers
              (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
              (LengthOK := data.LengthOK) activation
              (inputs.current.object.portPairSchedule data.threshold)
            have pairSetBlockerFree : ∀ pair, pair ∈ pairSet →
                ¬ Graph.SparsePairDEProfileObstructionAt
                    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                    (LengthOK := data.LengthOK) activation
                      (inputs.current.object.portPairSchedule data.threshold) pair ∧
                  ¬ Graph.SparsePairDEResponseObstructionAt
                    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
                    (LengthOK := data.LengthOK) activation
                      (inputs.current.object.portPairSchedule data.threshold) pair := by
              intro pair pairMem
              have freeRecorded : pair ∈ capacity.activation.freePairs
                  data.threshold :=
                capacity.freeSide_subset_activationFree pairMem
              have freeParts :
                  pair ∈ inputs.current.object.portPairSchedule data.threshold ∧
                    ¬ (Graph.CanonicalFibreLedger.canonicalLabel
                      Graph.SameTokenBlockerRoles.canonicalBlockerOrder
                      capacity.activation.Blocks pair).isSome := by
                simpa [Graph.FiniteObject.DemandActivation.freePairs,
                  Graph.FiniteObject.freePairs,
                  Graph.CanonicalFibreLedger.unassigned] using freeRecorded
              have noRecordedBlocker :
                  ¬ (recorded.blockers pair).Nonempty := by
                have noCapacityBlocker :
                    ¬ (capacity.activation.blockers pair).Nonempty := by
                  intro blocked
                  obtain ⟨kind, blocks⟩ :=
                    (capacity.activation.exists_blocks_iff_blockers_nonempty
                      pair).mpr blocked
                  apply freeParts.2
                  exact (Graph.CanonicalFibreLedger.isSome_canonicalLabel_iff
                    Graph.SameTokenBlockerRoles.canonicalBlockerOrder
                    capacity.activation.Blocks pair).mpr
                      ⟨kind, capacity.activation.blocks_mem_canonicalBlockerOrder
                        blocks, blocks⟩
                simpa [recorded, activation, activationEq] using
                  (show ¬ (capacity.activation.blockers pair).Nonempty from
                    noCapacityBlocker)
              constructor
              · intro obstruction
                apply noRecordedBlocker
                let coordinate :=
                  Graph.FiniteObject.DemandActivation.pairCoordinate pair
                    ((activation.pairSupport pair).getD ∅)
                have member : coordinate ∈
                    recorded.profileObstructions pair := by
                  simp [recorded, Graph.recordSparsePairDEBlockers,
                    obstruction, coordinate]
                exact (recorded.exists_blocks_iff_blockers_nonempty pair).mp
                  ⟨.boundaryProfile, recorded.blocks_boundaryProfile member⟩
              · intro obstruction
                apply noRecordedBlocker
                let coordinate :=
                  Graph.FiniteObject.DemandActivation.pairCoordinate pair
                    ((activation.pairSupport pair).getD ∅)
                have member : coordinate ∈
                    recorded.responseObstructions pair := by
                  simp [recorded, Graph.recordSparsePairDEBlockers,
                    obstruction, coordinate]
                exact (recorded.exists_blocks_iff_blockers_nonempty pair).mp
                  ⟨.targetResponse, recorded.blocks_targetResponse member⟩
            exact ⟨PairOverlapFirstFailure.of data.toParameters inputs.current.object active
              Coordinate family coordinateSupport realization pairSet
              pairSetNonempty (by
                intro pair member
                have membership :
                    pair ∈ inputs.current.object.portPairSchedule data.threshold ∧
                      Graph.CanonicalFibreLedger.canonicalLabel
                        capacity.tokenOrder capacity.Eligible pair = none := by
                  simpa [pairSet, Graph.freeSide,
                    Graph.CanonicalFibreLedger.unassigned] using member
                exact membership.1) pairSetBlockerFree firstFailure
              (inputs.get (K .noProperBaseline)).down.2⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine
