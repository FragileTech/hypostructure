import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.LowEntropyLargeBudget
import Hypostructure.Graph.Strategy.SpineRows.NetDeficiencyCap
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement
import HypostructureErdos64EG.Assembly.NetCharge.Continuation

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicDenseAtOrAboveWedgeFree
    {selected : EGInput.{u}}
    (wedgeFreeHistory : ExactLedger EGInput.{u} selected
      [K .dominantRootedTypeWedgeFree, K .dominantRootedType,
       K .localTypeCoordinateRepetitive, K .remainderEntropyLow, K .forcedCurvatureCost,
       K .curvatureFullRank, K .targetRankCircuit, K .exactResponseProfile,
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
  let large :=
    (lowEntropyLargeBudgetRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      wedgeFreeHistory (by simp [K_eq_iff])
  let netCap :=
    (netDeficiencyCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      large (by simp [K_eq_iff])
  exact Or.inl (selectedNetChargeContinuation netCap)

end HypostructureErdos64EG
