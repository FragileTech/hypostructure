import Hypostructure.Graph.Strategy.ColdCorridorRows
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
       K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality,
       K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
       K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
       K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let translated :=
    (independentObstructionTranslatesRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      wedgeHistory (by simp [K_eq_iff])
  let large :=
    (lowEntropyLargeBudgetRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      translated (by simp [K_eq_iff])
  let netCap :=
    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      large (by simp [K_eq_iff])
  exact Or.inl (selectedNetChargeContinuation netCap
    (unifiedTrueFresh := by simp [K_eq_iff])
    (peelingFresh := by simp [K_eq_iff])
    (stageFailedFresh := by simp [K_eq_iff])
    (demandLedgerFresh := by simp [K_eq_iff])
    (demandAbsorptionFresh := by simp [K_eq_iff])
    (openBoundarySaturatedFresh := by simp [K_eq_iff])
    (demandUnitCountFresh := by simp [K_eq_iff])
    (windowBlockersFresh := by simp [K_eq_iff])
    (windowShadowSignatureFresh := by simp [K_eq_iff])
    (windowShadowTailFresh := by simp [K_eq_iff])
    (windowShadowCycleFresh := by simp [K_eq_iff])
    (windowShadowExcludedFresh := by simp [K_eq_iff])
    (demandResidualFresh := by simp [K_eq_iff])
    (unpaidExitFourFresh := by simp [K_eq_iff])
    (unifiedVisibleFresh := by simp [K_eq_iff])
    (unifiedVisibleOverloadFresh := by simp [K_eq_iff])
    (jointBalanceFresh := by simp [K_eq_iff])
    (unifiedTerminalFresh := by simp [K_eq_iff])
    (globalLocalBridgeFresh := by simp [K_eq_iff])
    (fanClosedFresh := by simp [K_eq_iff])
    (compatibleClosureFresh := by simp [K_eq_iff])
    (fanClosedRoutingFresh := by simp [K_eq_iff])
    (compatibleRoutingFresh := by simp [K_eq_iff])
    (triangularRoutingFresh := by simp [K_eq_iff])
    (shoulderCompletionFresh := by simp [K_eq_iff])
    (triangularPortReturnFresh := by simp [K_eq_iff])
    (firstLandingFresh := by simp [K_eq_iff])
    (crossShoulderFresh := by simp [K_eq_iff])
    (fanSafeFresh := by simp [K_eq_iff]))

end HypostructureErdos64EG
