import Hypostructure.Graph.Strategy.SpineRows.HotColdPartition
import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.RealizedAtOrAbove
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.RealizedBelow

/-! A branch of the near-cubic survivor, retaining its full literal ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicRealized
    {selected : EGInput.{u}}
    (enumerated : ExactLedger EGInput.{u} selected
      [K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      enumerated (by key_fresh)
  match selectedBarrierDichotomy partitioned
      (by key_fresh) (by key_fresh) with
  | .left capHistory =>
      -- `[145]` carries no mathematical assertion of its own: pass the
      -- literal `[22]` ledger directly to `[146]`.
      match coldRoute8Dichotomy (data := spineData) capHistory
          (by key_fresh) (by key_fresh) with
      | .left belowHistory =>
          exact Assembly.Internal.nearCubicRealizedBelow belowHistory
      | .right atOrAboveHistory =>
          exact Assembly.Internal.nearCubicRealizedAtOrAbove atOrAboveHistory
  | .right overflowHistory =>
      exact (selectedBarrierOverflowCloses overflowHistory
        (by key_fresh) (by key_fresh)).elim

end HypostructureErdos64EG
