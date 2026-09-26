import Hypostructure.Graph.Strategy.BlockedCompressionRows
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.UnrealizedBelow
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.UnrealizedDense

/-! A branch of the near-cubic survivor, retaining its full literal ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicUnrealized
    {selected : EGInput.{u}}
    (unrealizedHistory : ExactLedger EGInput.{u} selected
      [K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[159]`: the dense-packing residual on which the manuscript's `[158]`
  -- realization sentence fails (`2^{b_𝒫}` exceeds the labelled skeleton
  -- count).  `[160]` then decides `τ(θ) < 1/4` on this literal residual; the
  -- hot/cold split `[22]` is run only inside the `[162]` pass.
  let denseOverflow :=
    (densePackingOverflowRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unrealizedHistory (by key_fresh)
  match selectedDenseDeficiencyDichotomy denseOverflow
      (by key_fresh) (by key_fresh) with
  | .left belowHistory =>
      exact Assembly.Internal.nearCubicUnrealizedBelow belowHistory
  | .right denseHistory =>
      exact Assembly.Internal.nearCubicUnrealizedDense denseHistory

end HypostructureErdos64EG
