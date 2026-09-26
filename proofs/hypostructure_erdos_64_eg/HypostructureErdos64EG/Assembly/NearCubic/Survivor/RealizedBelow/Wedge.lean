import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.SpineRows.IndependentObstructionTranslates
import Hypostructure.Graph.Strategy.SpineRows.LowEntropyLargeBudget
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
noncomputable def Assembly.Internal.nearCubicRealizedBelowWedge
    {selected : EGInput.{u}}
    (wedgeHistory : ExactLedger EGInput.{u} selected
      [K .dominantRootedWedgeType, K .dominantRootedType, K .localTypeCoordinateRepetitive,
       K .remainderEntropyLow, K .forcedCurvatureCost, K .curvatureFullRank,
       K .targetRankCircuit, K .exactResponseProfile, K .admissibleRankQuotient,
       K .curvatureTargetRank, K .wedgeSupply, K .stubSupply, K .boundaryDemand,
       K .remainderRelabelingEntropy, K .remainderNormalized, K .route8Rate,
       K .coldRoute8Below, K .barrierCap, K .hotColdPartition, K .windowPackageRealized,
       K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
       K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
       K .windowPresent, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality,
       K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
       K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
       K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let translated :=
    (independentObstructionTranslatesRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      wedgeHistory (by key_fresh)
  let large :=
    (lowEntropyLargeBudgetRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      translated (by key_fresh)
  let netCap :=
    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      large (by key_fresh)
  exact Or.inl (selectedNetChargeContinuation netCap
    (unifiedTrueFresh := by key_fresh)
    (peelingFresh := by key_fresh)
    (stageFailedFresh := by key_fresh)
    (demandLedgerFresh := by key_fresh)
    (demandAbsorptionFresh := by key_fresh)
    (openBoundarySaturatedFresh := by key_fresh)
    (demandUnitCountFresh := by key_fresh)
    (windowBlockersFresh := by key_fresh)
    (windowShadowSignatureFresh := by key_fresh)
    (windowShadowTailFresh := by key_fresh)
    (windowShadowCycleFresh := by key_fresh)
    (windowShadowExcludedFresh := by key_fresh)
    (demandResidualFresh := by key_fresh)
    (unpaidExitFourFresh := by key_fresh)
    (unifiedVisibleFresh := by key_fresh)
    (unifiedVisibleOverloadFresh := by key_fresh)
    (jointBalanceFresh := by key_fresh)
    (unifiedTerminalFresh := by key_fresh)
    (globalLocalBridgeFresh := by key_fresh)
    (fanClosedFresh := by key_fresh)
    (compatibleClosureFresh := by key_fresh)
    (fanClosedRoutingFresh := by key_fresh)
    (compatibleRoutingFresh := by key_fresh)
    (triangularRoutingFresh := by key_fresh)
    (shoulderCompletionFresh := by key_fresh)
    (triangularPortReturnFresh := by key_fresh)
    (firstLandingFresh := by key_fresh)
    (crossShoulderFresh := by key_fresh)
    (fanSafeFresh := by key_fresh))

end HypostructureErdos64EG
