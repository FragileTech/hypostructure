import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.BoundaryDemand
import Hypostructure.Graph.Strategy.SpineRows.BranchDependence
import Hypostructure.Graph.Strategy.SpineRows.CurvatureRankDichotomy
import Hypostructure.Graph.Strategy.SpineRows.CurvatureTargetRank
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import Hypostructure.Graph.Strategy.SpineRows.SeparatedTesters
import Hypostructure.Graph.Strategy.SpineRows.StubSupply
import Hypostructure.Graph.Strategy.SpineRows.TargetRankCircuit
import Hypostructure.Graph.Strategy.SpineRows.WedgeSupply
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRateFailure.FullRank

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicBelowRateFailureBounded
    {selected : EGInput.{u}}
    (boundedHistory : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
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
  -- `[153]` bounded arm: return to `[24]` with the density cap, and only
  -- that live residual continues to `[25]`--`[30]` (no rate test on this
  -- edge; the private-carrier rate is tested where the route-8
  -- continuation consumes it).
  let density :=
    (densityBudgetRow (data := spineData)).run boundedHistory (by key_fresh)
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        density (by key_fresh)
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        remainder (by key_fresh)
  let boundary :=
    (boundaryDemandRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        relabelingEntropy (by key_fresh)
  let stubSupply :=
    (stubSupplyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        boundary (by key_fresh)
  let wedge :=
    (wedgeSupplyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        stubSupply (by key_fresh)
  -- `[31]`: the curvature target-rank of the remainder and `lem:target-rank-circuit`.
  let rank :=
    (curvatureTargetRankRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        wedge (by key_fresh)
  let circuit :=
    (targetRankCircuitRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        rank (by key_fresh)
  -- `[32]`: the exact finite rank split at the canonical maximal packing.
  match curvatureRankDichotomy (data := spineData) circuit
      (by key_fresh) (by key_fresh) with
  | .left dropHistory =>
      -- `[33]`--`[46]`: Branch D, closed.
      let dependence :=
        (branchDependenceRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) spineData).run
        dropHistory (by key_fresh)
      -- `[35]`: retain the Branch-D state and append only
      -- `lem:separated-testers` to the same literal ledger.
      let tested :=
        (separatedTestersRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          dependence (by key_fresh)
      exact (selectedRankDropCloses tested
        (by key_fresh) (by key_fresh)
        (by key_fresh) (by key_fresh)
        (by key_fresh) (by key_fresh)
        (by key_fresh) (by key_fresh)
        (by key_fresh)).elim
  | .right fullRankHistory =>
      exact Assembly.Internal.nearCubicBelowRateFailureFullRank fullRankHistory

end HypostructureErdos64EG
