import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.EntropyCapDichotomy
import Hypostructure.Graph.Strategy.SpineRows.EntropyPackage
import Hypostructure.Graph.Strategy.SpineRows.RouteEightNetDeficiencyCap
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NetCharge.Continuation

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicRealizedBelowHighEntropy
    {selected : EGInput.{u}}
    (highHistory : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost, K .curvatureFullRank,
       K .targetRankCircuit, K .exactResponseProfile, K .admissibleRankQuotient,
       K .curvatureTargetRank, K .wedgeSupply, K .stubSupply, K .boundaryDemand,
       K .remainderRelabelingEntropy, K .remainderNormalized, K .route8Rate,
       K .coldRoute8Below, K .barrierCap, K .hotColdPartition, K .windowPackageRealized,
       K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
       K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
       K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality,
       K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
       K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
       K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[52]`: join the high-entropy remainder and window accounts;
  -- `[53]`: test the resulting entropy cap.
  let package :=
    (entropyPackageRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      highHistory (by simp [K_eq_iff])
  match entropyCapDichotomy (data := spineData) package
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left activeHistory =>
      -- `[54]`: the sealed row handles both alternatives already
      -- stored in `K .hotColdPartition` and publishes only the exact
      -- opposite budget bound.  Core closes the two registered facts.
      let closedHistory :=
        (entropyCapBoundRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible activeHistory
            (K .entropyCapActive) (K .entropyCapBound)
            (by simp [K_eq_iff]) (by simp [K_eq_iff])
      exact (closedHistory.elimClosed (by infer_instance)).elim
  | .right largeHistory =>
      -- `[55]`: Residual C on the high-entropy arm.
      -- `[56]` on the route-8 arm: `Δ_net(R) < 1/4` from `τ(θ) < 3/13`
  -- (`K .coldRoute8Below`), which is the density input of this arm.
      let netCap :=
        (routeEightNetDeficiencyCapRow (BranchState := BranchState)
  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          largeHistory (by simp [K_eq_iff])
      -- `[57]` onward on this residual is the next producer.
      exact Or.inl (selectedNetChargeContinuation netCap)

end HypostructureErdos64EG
