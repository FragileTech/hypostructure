import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdMass
import Hypostructure.Graph.Strategy.ColdCorridorRows.EntryDichotomies
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.HotColdPartition
import Hypostructure.Graph.Strategy.SpineRows.Route8RateFromColdBelow
import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRateFailure.Bounded
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRateFailure.Linear

/-! Survivor branch dispatcher; terminal proofs compile separately. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicBelowRateFailure
    {selected : EGInput.{u}}
    (rateFails : ExactLedger EGInput.{u} selected
      [K .route8RateFails, K .denseDeficiencyBelow,
       K .densePackingOverflow, K .windowPackageUnrealized, K .skeletonDominates,
       K .windowPackageSeparated, K .barrierEnumeration, K .sparseSurplusSurvivor,
       K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
       K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres,
       K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
       K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap,
       K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[162]` on `[160]`'s second complement (`τ(θ) < 1/4`, private-carrier
  -- rate failed): the dense hot/cold pass runs `[22]` -- the canonical
  -- partition and its live-hot cap decision -- and `[145]`--`[157]` on this
  -- literal residual, retaining both `[160]` decision facts.
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      rateFails (by key_fresh)
  match selectedBarrierDichotomy partitioned
      (by key_fresh) (by key_fresh) with
  | .right overflowHistory =>
      exact (selectedBarrierOverflowCloses overflowHistory
        (by key_fresh) (by key_fresh)).elim
  | .left capHistory =>
  match coldRoute8Dichotomy (data := spineData) capHistory
      (by key_fresh) (by key_fresh) with
  | .left coldBelowHistory =>
      -- `[147]`: `θ < 1/78` gives the route-8 private-carrier rate on the
      -- canonical packing (`route8RateFromColdBelowRow`), the exact
      -- negation of the retained `K .route8RateFails`.  Core closes the pair.
      let closedHistory :=
        (route8RateFromColdBelowRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible coldBelowHistory
          (K .route8RateFails) (K .route8Rate)
          (by key_fresh) (by key_fresh)
      exact (closedHistory.elimClosed (by infer_instance)).elim
  | .right coldAtOrAboveHistory =>
  match coldHotEntropyDichotomy (data := spineData)
      coldAtOrAboveHistory (by key_fresh)
      (by key_fresh) with
  | .left overflowHistory =>
      exact (selectedColdHotEntropyCloses overflowHistory).elim
  | .right hotCapHistory =>
  let mass :=
    (coldMassRow (data := spineData)).run hotCapHistory
      (by key_fresh)
  let cubic :=
    (coldAmbientCubicRow (data := spineData)).run mass
      (by key_fresh)
  let stubs :=
    (coldStubExcessRow (data := spineData)).run cubic
      (by key_fresh)
  match coldMassDichotomy (data := spineData) stubs
      (by key_fresh) (by key_fresh) with
  | .left linearHistory =>
      exact Assembly.Internal.nearCubicBelowRateFailureLinear linearHistory
  | .right boundedHistory =>
      exact Assembly.Internal.nearCubicBelowRateFailureBounded boundedHistory

end HypostructureErdos64EG
