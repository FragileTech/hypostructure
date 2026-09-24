import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.DominantRootedType
import Hypostructure.Graph.Strategy.SpineRows.DominantRootedTypeWedgeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.ForcedCurvatureCost
import Hypostructure.Graph.Strategy.SpineRows.LocalTypeCoordinateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.RemainderEntropyDichotomy
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.HighEntropy
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.Nonrepetitive
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.Wedge
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.WedgeFree

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicDenseAtOrAboveFullRank
    {selected : EGInput.{u}}
    (fullRankHistory : ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .targetRankCircuit, K .exactResponseProfile,
       K .admissibleRankQuotient, K .curvatureTargetRank, K .wedgeSupply, K .stubSupply,
       K .boundaryDemand, K .remainderRelabelingEntropy, K .remainderNormalized,
       K .route8Rate, K .densityCap, K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess,
       K .coldAmbientCubic, K .coldMass, K .coldHotEntropyCap, K .coldRoute8AtOrAbove,
       K .barrierCap, K .denseDeficiencyAtOrAbove, K .hotColdPartition,
       K .densePackingOverflow, K .windowPackageUnrealized, K .skeletonDominates,
       K .windowPackageSeparated, K .barrierEnumeration, K .sparseSurplusSurvivor,
       K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .uncompressible,
       K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres,
       K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
       K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap,
       K .cubicBaseline, K .selection]) :
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
      exact Assembly.Internal.nearCubicDenseAtOrAboveHighEntropy highHistory
  | .right lowHistory =>
      match localTypeCoordinateDichotomy (data := spineData) lowHistory
          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
      | .right nonrepetitiveHistory =>
          exact Assembly.Internal.nearCubicDenseAtOrAboveNonrepetitive nonrepetitiveHistory
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
              exact Assembly.Internal.nearCubicDenseAtOrAboveWedgeFree wedgeFreeHistory
          | .left wedgeHistory =>
              exact Assembly.Internal.nearCubicDenseAtOrAboveWedge wedgeHistory

end HypostructureErdos64EG
