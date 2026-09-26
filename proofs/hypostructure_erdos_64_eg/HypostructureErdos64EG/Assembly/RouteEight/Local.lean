import Hypostructure.Graph.Strategy.SpineRows.Route8OpenBoundarySaturated
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowSignature
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowSingletonTail
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitCycle
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitExcluded
import Hypostructure.Graph.Strategy.SpineRows.Route8DemandAbsorption
import Hypostructure.Graph.Strategy.SpineRows.Route8DemandPartition
import Hypostructure.Graph.Strategy.SpineRows.Route8JointBalance
import Hypostructure.Graph.Strategy.SpineRows.Route8PeelingDescent
import Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8StageOutcomeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8TwoCarrierExit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleOverload
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleResidual
import Hypostructure.Graph.Strategy.SpineRows.Route8UnpaidExitFourDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8WindowBlockers
import Hypostructure.Graph.Strategy.SpineRows.TypeBSublinearDichotomy
import Hypostructure.Graph.Strategy.TypeAExitRun
import HypostructureErdos64EG.Assembly.RouteEight.Boundary

/-!
# Assembly: RouteEight / Local

The unified route-`8` residual of Part IX, from the Type B sublinear-bridge
decision through nodes `[123]`, `[124]`, `[181]` and `[183]`--`[186]`.  One
composition, generic over the incoming exact ledger: every caller that reaches
the unified target-defect/route-`8` ledger runs it on its own literal
residual.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Node `[123]`: finite exact descent terminates in true route 8?**

The descent row records the terminal stage of `thm:large-budget-route8-only`;
the decision is its reduced-rate test.  A passing stage carries the terminal
true two-support entry, closed at node `[124]` by the framework
(`thm:typeA-two-carrier-nogo` against `lem:typeA-carrier-deletion-exit`).  The
failed stage runs the demand, absorption and unique-window blocker ledgers
(with the window-signature facts) and is the node-`[181]` residual
(`def:typeA-peeled-demand-residual`), returned with every inherited key. -/
-- EG-NODE [123] finite exact descent terminates in true route 8?
-- EG-NODE [124] local exclusion theorem: no two-support route-8 obstruction
noncomputable def selectedRouteEightDescent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .selection) known]
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by
      key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by
      key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh) :
    ExactLedger EGInput.{u} selected
      ([K .windowShadowHitExcluded, K .windowShadowHitCycle,
        K .windowShadowSingletonTail, K .windowShadowSignature,
        K .route8WindowBlockers, K .route8OpenBoundarySaturated,
        K .route8DemandUnitCount, K .route8DemandAbsorption,
        K .route8DemandLedger, K .route8StageRateFailed,
        K .route8PeelingDescent] ++ known) := by
  let descended :=
    (route8PeelingDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match route8StageOutcomeDichotomy (data := spineData) descended
      (by key_fresh) (by key_fresh) with
  | .left rateHistory =>
      -- `[123]` yes → `[124]`.
      let trueEntry :=
        (route8StageTrueEntryRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          rateHistory (by key_fresh)
      exact (((route8UnifiedTwoCarrierExitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible trueEntry
          (K .route8UnifiedTrueTwoCarrierEntry)
          (K .route8UnifiedTwoCarrierExit)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right failedStage =>
      -- `[123]` no ("failed reduced rate") → the ledgers of `[181]`.
      let ledger :=
        (route8DemandLedgerRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failedStage (by key_fresh)
      let absorbed :=
        (route8DemandAbsorptionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          ledger (by key_fresh)
      let saturated :=
        (route8OpenBoundarySaturatedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          absorbed (by key_fresh)
      let blocked :=
        (route8WindowBlockersRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          saturated (by key_fresh)
      let shadowSignature :=
        (windowShadowSignatureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          blocked (by key_fresh)
      let shadowTail :=
        (windowShadowSingletonTailRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          shadowSignature (by key_fresh)
      let shadowCycle :=
        (windowShadowHitCycleRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          shadowTail (by key_fresh)
      exact
        (windowShadowHitExcludedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          shadowCycle (by key_fresh)

/-- **Nodes `[181]`/`[183]`: maximal-ledger exit-`(4)` reduction**
(`thm:typeA-unpaid-exit4-reduction`).

The incoming node-`[181]` ledger is retained verbatim.  The one-entry
augmentation (168.1) is published first; the decision then asks whether some
unpaid entry of a maximal ledger lacks an exit-`(4)` witness.  Such an entry is
exactly the terminal input of `thm:typeA-two-carrier-nogo` and is closed at
node `[124]`; the only survivor is node `[183]`, (168.2). -/
-- EG-NODE [181] maximal-ledger augmentation: some unpaid entry lacks an exit-\textup{(4)} witness?
-- EG-NODE [183] shortest-trace boundary-support test on the retained unified entries
noncomputable def selectedRouteEightUnpaidReduction
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (residualFresh : K .route8UnpaidExitFourResidual ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      (K .route8UnpaidExitFourResidual :: K .route8UnpaidTwoCarrier :: known) := by
  let twoCarrier :=
    (route8UnpaidTwoCarrierRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match route8UnpaidExitFourDichotomy (data := spineData) twoCarrier
      (by key_fresh) (by key_fresh) with
  | .left witnessFree =>
      -- `[181]` yes → `[124]`.
      let trueEntry :=
        (route8UnpaidTrueEntryRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          witnessFree (by key_fresh)
      exact (((route8UnifiedTwoCarrierExitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible trueEntry
          (K .route8UnifiedTrueTwoCarrierEntry)
          (K .route8UnifiedTwoCarrierExit)
          (by key_fresh) (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right residualHistory =>
      exact residualHistory

/-- **The unified target-defect/route-`8` residual** (`rem:why-unified`),
from the Type B sublinear-bridge decision to node `[186]`.

The negative Type B bridge arm is the Type B residual; the sublinear arm
publishes the unified deficit (`lem:typeA-unified-deficit`) and asks the
quotient-freeness test of the unified census.  Its failure is the route-`8`
quotient residual; on the free arm the unified entry census is published and
the branch runs node `[123]`, node `[181]`, and the reductions `[183]`--`[185]`
to the joint balance at node `[186]`. -/
-- EG-NODE [184] visible-first prefix test on the unchanged all-visible entries
-- EG-NODE [185] canonical actual visible-four packages; non-overloaded count zero
-- EG-NODE [186] OPEN: joint balance and silent-terminal exclusion; visible-entry history retained
noncomputable def selectedRouteEightUnifiedResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by
      key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by
      key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  match typeBSublinearDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by key_fresh)
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
          (by key_fresh) (by key_fresh) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory (by key_fresh)
          let peeled := selectedRouteEightDescent census
          let unpaid := selectedRouteEightUnpaidReduction peeled
          -- `[183]` → `[184]`: the silent coordinate is zero.
          let visibleResidual :=
            (route8UnifiedVisibleResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run unpaid (by key_fresh)
          -- `[184]` → `[185]`: the non-overloaded coordinate is zero.
          let visibleOverload :=
            (route8UnifiedVisibleOverloadRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run visibleResidual (by key_fresh)
          -- `[185]` → `[186]`: the simultaneous exact account.
          let jointBalance :=
            (route8JointBalanceRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run visibleOverload (by key_fresh)
          exact Or.inr (Or.inr
            (jointBalance.get (K .route8JointBalance)).down)

/-- **The unified residual on the silent Type A lane** (`[94]` silent arm,
decided by `typeASilentExitSevenDichotomy`).  Identical to
`selectedRouteEightUnifiedResidual` up to node `[184]`; there the selected
silent excess load of `K .typeASilentExitSevenFree` is a unified entry, which
node `[184]` makes visible, so the lane closes through the framework.

The negative Type B bridge arm is the Type B residual; the sublinear arm
publishes the unified deficit (`lem:typeA-unified-deficit`) and asks the
quotient-freeness test of the unified census.  Its failure is the route-`8`
quotient residual; on the free arm the unified entry census is published and
the branch runs node `[123]`, node `[181]`, and the reductions `[183]`--`[185]`
to the joint balance at node `[186]`. -/
noncomputable def selectedRouteEightUnifiedResidualSilent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .typeASilentExitSevenFree) known]
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageRateFresh : K .route8StageRate ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (unifiedExitFresh : K .route8UnifiedTwoCarrierExit ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by
      key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by
      key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh) :
    SelectedRouteEightBoundary selected := by
  match typeBSublinearDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by key_fresh)
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
          (by key_fresh) (by key_fresh) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory (by key_fresh)
          let peeled := selectedRouteEightDescent census
          let unpaid := selectedRouteEightUnpaidReduction peeled
          -- `[183]` → `[184]`: the silent coordinate is zero, against the
          -- lane's selected silent excess load.
          exact (((route8UnifiedVisibleResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible unpaid
              (K .typeASilentExitSevenFree) (K .route8UnifiedVisibleResidual)
              (by key_fresh) (by key_fresh)).elimClosed
                (by infer_instance)).elim

end HypostructureErdos64EG
