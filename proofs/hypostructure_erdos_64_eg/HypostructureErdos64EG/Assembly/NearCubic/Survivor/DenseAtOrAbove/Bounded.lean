import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.BoundaryDemand
import Hypostructure.Graph.Strategy.SpineRows.BranchDependence
import Hypostructure.Graph.Strategy.SpineRows.CurvatureRankDichotomy
import Hypostructure.Graph.Strategy.SpineRows.CurvatureTargetRank
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import Hypostructure.Graph.Strategy.SpineRows.Route8RateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.SeparatedTesters
import Hypostructure.Graph.Strategy.SpineRows.StubSupply
import Hypostructure.Graph.Strategy.SpineRows.TargetRankCircuit
import Hypostructure.Graph.Strategy.SpineRows.WedgeSupply
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.FullRank

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicDenseAtOrAboveBounded
    {selected : EGInput.{u}}
    (boundedHistory : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
       K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap,
       K .denseDeficiencyAtOrAbove, K .hotColdPartition, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[24]`: the density cap on the bounded arm, then the spine.  The
  -- route-8 rate `τ < 3/13` (`[120]`) follows from the density cap
  -- only for sufficiently large `n`; it is decided here, and its
  -- failure (`densityCap` with `3/13 ≤ τ`, a finite-order corner
  -- like `[57]`'s) is the next producer.
  let density :=
    (densityBudgetRow (data := spineData)).run boundedHistory (by simp [K_eq_iff])
  match route8RateDichotomy (data := spineData) density
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .right rateFails =>
      exact Or.inr (Or.inl
        (rateFails.get (K .route8RateFails)).down)
  | .left density =>
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        density (by simp [K_eq_iff])
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
      exact Assembly.Internal.nearCubicDenseAtOrAboveFullRank fullRankHistory

end HypostructureErdos64EG
