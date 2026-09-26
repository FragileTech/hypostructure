import Hypostructure.Graph.Strategy.SpineRows.BridgeFanMass
import Hypostructure.Graph.Strategy.SpineRows.Route8ExtractedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8PiecesClassified
import Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedNegative
import Hypostructure.Graph.Strategy.SpineRows.TypeAExclusion
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeReduction
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeSublinear
import Hypostructure.Graph.Strategy.SpineRows.TypeBSublinearDichotomy
import HypostructureErdos64EG.Assembly.RouteEight.Boundary
import HypostructureErdos64EG.Assembly.RouteEight.Local

/-!
# Assembly: TypeA / ExitFourDischargedRetest

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys the Part IX continuation of the discharged receiver may add. -/
noncomputable abbrev typeADischargedRetestKeys : FactKeys EGInput.{u} :=
  [K .route8UnifiedNegative,
    K .typeAExclusion,
    K .typeBBridgeReduction,
    K .route8PiecesClassified,
    K .typeBBridgeMass,
    K .typeBBridgeSublinear,
    K .typeBSublinearLedger,
    K .typeBSublinearResidual,
    K .route8UnifiedDeficit,
    K .route8QuotientFree,
    K .route8QuotientResidual,
    K .route8UnifiedEntryCensus,
    K .route8ExtractedEntryCensus,
    K .route8PeelingDescent,
    K .route8UnifiedTrueTwoCarrierEntry,
    K .route8StageRateFailed,
    K .route8TerminalNoGo,
    K .route8DemandLedger,
    K .route8DemandAbsorption,
    K .route8OpenBoundarySaturated,
    K .route8DemandUnitCount,
    K .route8WindowBlockers,
    K .windowShadowSignature,
    K .windowShadowSingletonTail,
    K .windowShadowHitCycle,
    K .windowShadowHitExcluded,
    K .route8PeeledDemandResidual,
    K .route8UnpaidExitFourResidual,
    K .route8UnifiedVisibleResidual,
    K .route8UnifiedVisibleOverload,
    K .route8JointBalance]

/-- **`[102]` → `[89]` → `[123]`, the discharged receiver.**  On the no arm of
the recompute-`L₄` retest the peeled receiver is unsaturated with nonnegative
remaining charge (`K .typeAExitFourReceiverDischarged`,
`lem:typeA-exit4-peeling-charge`), and its peeled target-defect loads enter
node `[123]`'s unified target-defect/route-`8` pressure ledger.  The chain from
`[123]` below repeats the `[113]`-fails arm of `selectedRouteEightResidual`. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedTypeAExitFourDischargedRetest
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (fresh : List.Disjoint typeADischargedRetestKeys known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  -- `[123]`: publish `def:typeA-unified-negative` on this residual.
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let typeAExcluded :=
    (typeAExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unifiedNegative (by key_fresh)
  let typeBReduced :=
    (typeBBridgeReductionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeAExcluded (by key_fresh)
  let classified :=
    (route8PiecesClassifiedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeBReduced (by key_fresh)
  let extractedCensus :=
    (route8ExtractedEntryCensusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      classified (by key_fresh)
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      extractedCensus (by key_fresh)
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by key_fresh)
  match typeBSublinearDichotomy (data := spineData) bridgeSublinear
      (by key_fresh)
      (by key_fresh) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by key_fresh)
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
          (by key_fresh)
          (by key_fresh) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory
                (by key_fresh)
          let peeled := selectedLargeBudgetPressureCensus census
            (peelingFresh := by key_fresh)
            (unifiedTrueFresh := by key_fresh)
            (stageFailedFresh := by key_fresh)
            (terminalFresh := by key_fresh)
            (demandLedgerFresh := by key_fresh)
            (demandAbsorptionFresh := by
              key_fresh)
            (openBoundarySaturatedFresh := by
              key_fresh)
            (demandUnitCountFresh := by
              key_fresh)
            (windowBlockersFresh := by key_fresh)
            (windowShadowSignatureFresh := by key_fresh)
            (windowShadowTailFresh := by key_fresh)
            (windowShadowCycleFresh := by key_fresh)
            (windowShadowExcludedFresh := by key_fresh)
            (demandResidualFresh := by key_fresh)
          let unpaidExitFour :=
            selectedRouteEightUnpaidExitFourReduction peeled
              (unifiedTrueFresh := by key_fresh)
              (residualFresh := by key_fresh)
              (terminalFresh := by key_fresh)
          let visibleResidual :=
            selectedRouteEightVisibleResidual unpaidExitFour
              (visibleFresh := by key_fresh)
          let visibleOverload :=
            selectedRouteEightVisibleOverload visibleResidual
              (overloadFresh := by
                key_fresh)
          let jointBalance :=
            selectedRouteEightJointBalance visibleOverload
              (by key_fresh)
          exact Or.inr (Or.inr
            (jointBalance.get (K .route8JointBalance)).down)

end HypostructureErdos64EG
