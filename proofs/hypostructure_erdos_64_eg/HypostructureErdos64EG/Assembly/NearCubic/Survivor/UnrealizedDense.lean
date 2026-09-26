import Hypostructure.Graph.Strategy.SpineRows.HotColdPartition
import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow

/-! A branch of the near-cubic survivor, retaining its full literal ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicUnrealizedDense
    {selected : EGInput.{u}}
    (denseHistory : ExactLedger EGInput.{u} selected
      [K .denseDeficiencyAtOrAbove, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[162]` on the `τ(θ) ≥ 1/4` complement of `[160]`: the dense hot/cold
  -- pass runs `[22]` -- the canonical hot/cold partition and its live-hot
  -- cap decision -- and then the cold branch `[145]`--`[157]` on this
  -- literal residual.
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      denseHistory (by key_fresh)
  match selectedBarrierDichotomy partitioned
      (by key_fresh) (by key_fresh) with
  | .right overflowHistory =>
      exact (selectedBarrierOverflowCloses overflowHistory
        (by key_fresh) (by key_fresh)).elim
  | .left capHistory =>
  -- `[145]` carries no assertion: pass the literal `[22]` cap ledger to `[146]`.
  match coldRoute8Dichotomy (data := spineData) capHistory
      (by key_fresh) (by key_fresh) with
  | .left belowHistory =>
      exact Assembly.Internal.nearCubicDenseBelow belowHistory
  | .right atOrAboveHistory =>
      exact Assembly.Internal.nearCubicDenseAtOrAbove atOrAboveHistory

end HypostructureErdos64EG
