import Hypostructure.Graph.Strategy.SpineRows.HotColdPartition
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
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- The residual on which the manuscript's `[21]` realization sentence
  -- fails (dense packing: `2^{bits·p}` exceeds the skeleton states).  The
  -- manuscript's own nodes are run on it: `[22]`'s partition, then the
  -- `τ(θ) < 1/4` reading of `prop:negative-net-charge` as a decision.
  let denseOverflow :=
    (densePackingOverflowRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unrealizedHistory (by simp [K_eq_iff])
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      denseOverflow (by simp [K_eq_iff])
  -- `[145]` is the direct handoff of `[22]`'s hot/cold fact.  Both
  -- deficiency arms read it from this same literal ExactLedger.
  match Decision.run partitioned (K .denseDeficiencyBelow) (K .denseDeficiencyAtOrAbove)
      `HypostructureErdos64EG.selectedDenseDeficiencyDichotomy
      (by
        classical
        exact if below : DenseDeficiencyBelowStatement spineData.{u} selected.object then
          .inl ⟨below⟩
        else
          .inr ⟨below⟩)
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left belowHistory =>
      exact Assembly.Internal.nearCubicUnrealizedBelow belowHistory
  | .right denseHistory =>
      exact Assembly.Internal.nearCubicUnrealizedDense denseHistory

end HypostructureErdos64EG
