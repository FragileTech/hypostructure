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
import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRateFailure.Bounded
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRateFailure.FullRank
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
      [K .route8RateFails, K .denseDeficiencyBelow, K .hotColdPartition,
       K .densePackingOverflow, K .windowPackageUnrealized, K .skeletonDominates,
       K .windowPackageSeparated, K .barrierEnumeration, K .sparseSurplusSurvivor,
       K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .uncompressible,
       K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres,
       K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
       K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap,
       K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- The exact interval `3/13 ≤ τ < 1/4` does not satisfy the
  -- private-carrier input of `[120]`--`[122]`.  Keep both literal
  -- decision facts and run `[162]` on this residual; in particular,
  -- do not fabricate `K .route8Rate` in order to enter `[161]`.
  match selectedBarrierDichotomy rateFails
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .right overflowHistory =>
      exact (selectedBarrierOverflowCloses overflowHistory
        (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim
  | .left capHistory =>
  match coldRoute8Dichotomy (data := spineData) capHistory
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left coldBelowHistory =>
      let coldBelowHistory :=
        (route8RateFromColdBelowRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run coldBelowHistory
          (by simp [K_eq_iff])
      let remainder :=
        (remainderNormalizationRow (BranchState := BranchState)
            (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
            (presentation := erdosReceiverLoadProfile) (data := spineData)).run
            coldBelowHistory (by simp [K_eq_iff])
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
          exact Assembly.Internal.nearCubicBelowRateFailureFullRank fullRankHistory
  | .right coldAtOrAboveHistory =>
  match coldHotEntropyDichotomy (data := spineData)
      coldAtOrAboveHistory (by simp [K_eq_iff])
      (by simp [K_eq_iff]) with
  | .left overflowHistory =>
      exact (selectedColdHotEntropyCloses overflowHistory).elim
  | .right hotCapHistory =>
  let mass :=
    (coldMassRow (data := spineData)).run hotCapHistory
      (by simp [K_eq_iff])
  let cubic :=
    (coldAmbientCubicRow (data := spineData)).run mass
      (by simp [K_eq_iff])
  let stubs :=
    (coldStubExcessRow (data := spineData)).run cubic
      (by simp [K_eq_iff])
  match coldMassDichotomy (data := spineData) stubs
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left linearHistory =>
      exact Assembly.Internal.nearCubicBelowRateFailureLinear linearHistory
  | .right boundedHistory =>
      exact Assembly.Internal.nearCubicBelowRateFailureBounded boundedHistory

end HypostructureErdos64EG
