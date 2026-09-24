import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.BoundaryDemand
import Hypostructure.Graph.Strategy.SpineRows.BranchDependence
import Hypostructure.Graph.Strategy.SpineRows.CurvatureRankDichotomy
import Hypostructure.Graph.Strategy.SpineRows.CurvatureTargetRank
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import Hypostructure.Graph.Strategy.SpineRows.Route8RateFromColdBelow
import Hypostructure.Graph.Strategy.SpineRows.SeparatedTesters
import Hypostructure.Graph.Strategy.SpineRows.StubSupply
import Hypostructure.Graph.Strategy.SpineRows.TargetRankCircuit
import Hypostructure.Graph.Strategy.SpineRows.WedgeSupply
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow.FullRank

/-! Survivor branch dispatcher; terminal proofs compile separately. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicDenseBelow
    {selected : EGInput.{u}}
    (belowHistory : ExactLedger EGInput.{u} selected
      [K .coldRoute8Below, K .barrierCap, K .denseDeficiencyAtOrAbove, K .hotColdPartition,
       K .densePackingOverflow, K .windowPackageUnrealized, K .skeletonDominates,
       K .windowPackageSeparated, K .barrierEnumeration, K .sparseSurplusSurvivor,
       K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .uncompressible,
       K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres,
       K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
       K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap,
       K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let belowHistory :=
    (route8RateFromColdBelowRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      belowHistory (by simp [K_eq_iff])
  -- `[147]`: `τ(θ) < 3/13`, the spine's route-8 closure with that
  -- inequality as `[56]`'s input.
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        belowHistory (by simp [K_eq_iff])
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        remainder (by simp [K_eq_iff])
  let boundary :=
    (boundaryDemandRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        relabelingEntropy (by simp [K_eq_iff])
  let stubSupply :=
    (stubSupplyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        boundary (by simp [K_eq_iff])
  let wedge :=
    (wedgeSupplyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        stubSupply (by simp [K_eq_iff])
  -- `[31]`: the curvature target-rank of the remainder and `lem:target-rank-circuit`.
  let rank :=
    (curvatureTargetRankRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        wedge (by simp [K_eq_iff])
  let circuit :=
    (targetRankCircuitRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        rank (by simp [K_eq_iff])
  -- `[32]`: the exact finite rank split at the canonical maximal packing.
  match curvatureRankDichotomy (data := spineData) circuit
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left dropHistory =>
      -- `[33]`--`[46]`: Branch D, closed.
      let dependence :=
        (branchDependenceRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) spineData).run
        dropHistory (by simp [K_eq_iff])
      -- `[35]`: retain the Branch-D state and append only
      -- `lem:separated-testers` to the same literal ledger.
      let tested :=
        (separatedTestersRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          dependence (by simp [K_eq_iff])
      exact (selectedRankDropCloses tested
        (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff])).elim
  | .right fullRankHistory =>
      exact Assembly.Internal.nearCubicDenseBelowFullRank fullRankHistory

end HypostructureErdos64EG
