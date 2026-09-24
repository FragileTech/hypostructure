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
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.RealizedBelow.FullRank

/-! Survivor branch dispatcher; terminal proofs compile separately. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicRealizedBelow
    {selected : EGInput.{u}}
    (belowHistory : ExactLedger EGInput.{u} selected
      [K .coldRoute8Below, K .barrierCap, K .hotColdPartition, K .windowPackageRealized,
       K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
       K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
       K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality,
       K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
       K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
       K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- The route-8 rate `K .route8Rate` (`[120]`, `τ < 3/13` with the exact
  -- allowances) is `K .coldRoute8Below` read through `|∂R| ≤ 15p + σ_W`.
  let belowHistory :=
    (route8RateFromColdBelowRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      belowHistory (by simp [K_eq_iff])
  -- `[147]`: "If `θ < 1/78`, then `τ(θ) < 3/13` by
  -- `def:cold-window-ledger`; this is exactly the private-carrier
  -- inequality used in `thm:large-budget-route8-only`, so the route-8
  -- branch closes."  The private-carrier inequality is
  -- `K .coldRoute8Below` on this residual, and the closure it names is
  -- the spine's own large-budget/route-8 closure (`[25]` → `[55]` →
  -- `[63]` → `[110]`--`[124]`), which reads `τ < 1/4` at `[56]`/`[59]`
  -- and `τ < 3/13` at `[122]` from that fact in place of `[24]`'s
  -- density cap.  Run `[25]`--`[31]` on the literal `[146]` yes-residual;
  -- `[32]` onward on it is the next producer.
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      belowHistory (by simp [K_eq_iff])
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run remainder (by simp [K_eq_iff])
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
      -- `[33]`: Branch D, the rank-reducing curvature dependence with its
      -- inclusion-minimal connected support.
      let dependence :=
        (branchDependenceRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          dropHistory (by simp [K_eq_iff])
      -- `[35]`: the repeated Branch-D state plus the exact
      -- `lem:separated-testers` fact on this literal ancestry.
      let tested :=
        (separatedTestersRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          dependence (by simp [K_eq_iff])
      exact (selectedRankDropCloses tested
        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim
  | .right fullRankHistory =>
      exact Assembly.Internal.nearCubicRealizedBelowFullRank fullRankHistory

end HypostructureErdos64EG
