import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.DominantRootedType
import Hypostructure.Graph.Strategy.SpineRows.DominantRootedTypeWedgeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.ForcedCurvatureCost
import Hypostructure.Graph.Strategy.SpineRows.LocalTypeCoordinateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.RemainderEntropyDichotomy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow.HighEntropy
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow.Nonrepetitive
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow.Wedge
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow.WedgeFree

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicDenseBelowFullRank
    {selected : EGInput.{u}}
    (fullRankHistory : ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .targetRankCircuit, K .exactResponseProfile,
       K .admissibleRankQuotient, K .curvatureTargetRank, K .wedgeSupply, K .stubSupply,
       K .boundaryDemand, K .remainderRelabelingEntropy, K .remainderNormalized,
       K .route8Rate, K .coldRoute8Below, K .barrierCap, K .denseDeficiencyAtOrAbove,
       K .hotColdPartition, K .densePackingOverflow, K .windowPackageUnrealized,
       K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
       K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
       K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality,
       K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
       K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
       K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[34]`/`[47]`/`[48]`: full rank and `cor:forced-curvature-cost`.
  let cost :=
    (forcedCurvatureCostRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        fullRankHistory (by simp [K_eq_iff])
  match remainderEntropyDichotomy (data := spineData) cost
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left highHistory =>
      exact Assembly.Internal.nearCubicDenseBelowHighEntropy highHistory
  | .right lowHistory =>
    match localTypeCoordinateDichotomy (data := spineData) lowHistory
          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
    | .right nonrepetitiveHistory =>
        exact Assembly.Internal.nearCubicDenseBelowNonrepetitive nonrepetitiveHistory
    | .left repetitiveHistory =>
        let dominant :=
          (dominantRootedTypeRow (BranchState := BranchState)
            (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
            (presentation := erdosReceiverLoadProfile) (data := spineData)).run
            repetitiveHistory (by simp [K_eq_iff])
        match dominantRootedTypeWedgeDichotomy (data := spineData) dominant
            (by simp [K_eq_iff])
            (by simp [K_eq_iff]) with
        | .right wedgeFreeHistory =>
            exact Assembly.Internal.nearCubicDenseBelowWedgeFree wedgeFreeHistory
        | .left wedgeHistory =>
            exact Assembly.Internal.nearCubicDenseBelowWedge wedgeHistory

end HypostructureErdos64EG
