import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.EntropyCapDichotomy
import Hypostructure.Graph.Strategy.SpineRows.EntropyPackage
import Hypostructure.Graph.Strategy.SpineRows.NetDeficiencyCap
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicBelowRateFailureHighEntropy
    {selected : EGInput.{u}}
    (highHistory : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost, K .curvatureFullRank,
       K .targetRankCircuit, K .exactResponseProfile, K .admissibleRankQuotient,
       K .curvatureTargetRank, K .wedgeSupply, K .stubSupply, K .boundaryDemand,
       K .remainderRelabelingEntropy, K .remainderNormalized, K .densityCap,
       K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
       K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap,
       K .hotColdPartition, K .route8RateFails, K .denseDeficiencyBelow, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[52]`/`[53]`: the high arm performs only the manuscript's independent
  -- window/remainder accounting and entropy-cap test.
  let package :=
    (entropyPackageRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) spineData).run
    highHistory (by key_fresh)
  match entropyCapDichotomy (data := spineData) package
      (by key_fresh) (by key_fresh) with
  | .left activeHistory =>
      -- `[54]`: the sealed row derives the exact opposite budget bound on
      -- both alternatives stored in `K .hotColdPartition`; Core closes the
      -- resulting incompatible facts on this literal active ledger.
      let closedHistory :=
        (entropyCapBoundRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).runAndCloseIncompatible
            activeHistory
            (K .entropyCapActive) (K .entropyCapBound)
            (by key_fresh)
            (by key_fresh)
      exact (closedHistory.elimClosed (by infer_instance)).elim
  | .right largeHistory =>
      let netCap :=
        (netDeficiencyCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          largeHistory (by key_fresh)
      -- `[162]`'s bounded `[153]` arm has returned through `[24]` to `[25]`;
      -- this ledger already retains `[160]`'s failed private-carrier rate
      -- (`K .route8RateFails`), which the route-8 continuation `[57]`--`[124]`
      -- would consume at `[120]`--`[122]`.  The retained failure is the
      -- `[187]` outcome at the entry of that continuation.
      exact Or.inr (Or.inl (netCap.get (K .route8RateFails)).down)

end HypostructureErdos64EG
