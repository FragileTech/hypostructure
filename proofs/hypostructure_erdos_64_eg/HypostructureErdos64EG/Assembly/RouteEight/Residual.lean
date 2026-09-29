import Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCore
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCutParity
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDeletionWitnesses
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8Census
import Hypostructure.Graph.Strategy.SpineRows.Route8LargeBudgetDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8PrivateCarrierBudget
import Hypostructure.Graph.Strategy.SpineRows.Route8ResidualProfile
import Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreCollapse
import Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreExit
import Hypostructure.Graph.Strategy.SpineRows.Route8TrueResidual
import Hypostructure.Graph.Strategy.SpineRows.Route8TrueTwoCarrierEntry
import Hypostructure.Graph.Strategy.SpineRows.Route8TwoCarrierExit
import HypostructureErdos64EG.Assembly.RouteEight.TypeBContinuation

/-!
# Assembly: RouteEight / Residual

Part IX from exit `(8)`: nodes `[110]`--`[124]`, then the unified
target-defect/route-`8` ledger of nodes `[123]`, `[181]`, `[183]`--`[186]`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- **Nodes `[110]`--`[112]`**: the exit-`(8)` residual profile, the collection
`𝒳_A` of node `[111]` (a definition node; its "carrying `D_A`" is the
node-`[113]` inequality), and the burden `s·D_A(𝒳_A) ≤ N_basin(𝒳_A)`, appended
to the incoming ledger. -/
-- EG-NODE [110] exit (8): route-8 residual profile
-- EG-NODE [111] global squeeze extracts a route-8 Type A collection $\mathcal X_A$ carrying $D_A(\mathcal X_A)$
-- EG-NODE [112] route-8 burden: $N_{\rm basin}(\mathcal X_A)\ge4D_A(\mathcal X_A)$
noncomputable def selectedRouteEightProfile
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (profileFresh : K .route8ResidualProfile ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      ([K .route8BasinBurden, K .route8ResidualProfile]
        ++ known) :=
  -- `[110]`
  let profile :=
    (route8ResidualProfileRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[111]` is a definition node (`def:typeA-large-budget-deficit`):
  -- `𝒳_A := route8SurvivorComponents`, `D_A := route8Deficit`.  Its
  -- "carrying `D_A`" content is the node-`[113]` inequality, decided below.
  -- `[112]`
  let burdened :=
    (route8BasinBurdenRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      profile (by key_fresh)
  -- `[113]`: the route-8-only lower bound is tested, because the manuscript's
  -- unified-demand correction (`rem:why-unified`) forbids deriving it while
  -- target-defect supports may still carry negative mass.
  burdened

set_option maxHeartbeats 8000000 in
/-- **Nodes `[114]`--`[124]` on the positive arm of `[113]`.**

`[114]` publishes the carrier cores, the true residual and the cut parity;
`[115]` decides the zero/one-core entry, closed at `[116]` against the true
residual; `[117]` decides the two-support entry: its no arm publishes the
private-support budget `[119]`--`[120]`, closed at `[121]`--`[122]` against the
census, and its yes arm `[118]` is a two-support entry of the route-`8`
collection carrying the large-budget deficit: `thm:large-budget-route8-only`
(its route-`8` alternative) and `prop:typeA-route8-closure-from-nogo` make it
the terminal obstruction, closed at `[124]` by `thm:typeA-two-carrier-nogo`.
Every arm of `[113]`-yes closes. -/
-- EG-NODE [114] each entry passes to its canonical minimal target-complete response-support core inside the declared $u$-supported response algebra
-- EG-NODE [115] some entry has $\alpha_{\mathcal X}(\xi)\le1$?
-- EG-NODE [116] exits (4)--(7) occur
-- EG-NODE [117] some entry has $\pi_{\mathcal X}(\xi)\le2$?
-- EG-NODE [118] two-support route-8 entry
-- EG-NODE [119] no two-support entry: every indexed entry has at least three private essential boundary incidences
-- EG-NODE [120] private-support budget: $3N_{\rm basin}(\mathcal X_A)\le\defp(R)+o(|R|)\le\tau_{\rm win}|R|+o(|R|)$
-- EG-NODE [121] burden plus deficit: $N_{\rm basin}(\mathcal X_A)\ge4(1/4-\tau_{\rm win})|R|-o(|R|)$
-- EG-NODE [122] contradiction: $\tau_{\rm win}\ge12(1/4-\tau_{\rm win})$, but $\tau_{\rm win}<3/13$
theorem selectedRouteEightCollection
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (deficit : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8ResidualProfile) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8LargeBudgetDeficit) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    (coreFresh : K .route8CarrierCore ∉ known := by key_fresh)
    (trueResidualFresh : K .route8TrueResidual ∉ known := by key_fresh)
    (cutParityFresh : K .route8CarrierCutParity ∉ known := by key_fresh)
    (smallFresh : K .route8SmallCoreEntry ∉ known := by key_fresh)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known := by key_fresh)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by key_fresh)
    (censusFresh : K .route8Census ∉ known := by key_fresh)
    (twoFresh : K .route8TwoCarrierEntry ∉ known := by key_fresh)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known := by key_fresh)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known := by key_fresh)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known := by
      key_fresh)
    (twoCarrierExitFresh : K .route8TwoCarrierExit ∉ known := by key_fresh)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known := by
      key_fresh)
    (closureFresh : closed ∉ known := by key_fresh) :
    False := by
  -- `[114]`
  let cored :=
    (route8CarrierCoreRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      deficit (by key_fresh)
  let trueResidual :=
    (route8TrueResidualRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cored (by key_fresh)
  let cutParity :=
    (route8CarrierCutParityRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      trueResidual (by key_fresh)
  -- `[115]`
  match route8SmallCoreCollapseRow (data := spineData) cutParity
      (by key_fresh) (by key_fresh) with
  | .left small =>
      -- `[116]`: the collapse alternatives against the true residual.
      exact (((route8SmallCoreExitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible small
          (K .route8TrueResidual) (K .route8SmallCoreCollapse)
          (by key_fresh) (by key_fresh)).elimClosed
            (by infer_instance)).elim
  | .right noSmall =>
      -- `[117]`, read from the `[115]` no arm.
      match route8CarrierDichotomy (data := spineData) noSmall
          (by key_fresh) (by key_fresh) with
      | .right noTwo =>
          -- `[119]`--`[120]`: the private-support budget.
          let budget :=
            (route8PrivateCarrierBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run noTwo (by key_fresh)
          -- `[121]`: burden plus deficit, the census readings.
          let census :=
            (route8CensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run budget (by key_fresh)
          -- `[122]`: the budget contradicts the census readings.
          exact ((closeIncompatible census (K .route8Census)
            (K .route8PrivateCarrierBudget) (by key_fresh)).elimClosed
              (by infer_instance)).elim
      | .left twoCarrier =>
          -- `[118]`: the two-support entry `ι₂` of `𝒳_A` is a true route-`8`
          -- entry, (T2), and carries its declared deletion witnesses, (T5).
          -- It is a route-`8` entry of the collection carrying the
          -- large-budget deficit, so `thm:large-budget-route8-only` sends it
          -- through `prop:typeA-route8-closure-from-nogo` to `[124]`.
          let trueEntry :=
            (route8TrueTwoCarrierEntryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run twoCarrier (by key_fresh)
          let witnesses :=
            (route8CarrierDeletionWitnessesRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run trueEntry (by key_fresh)
          -- `[124]`, `thm:typeA-two-carrier-nogo`: the deletion witnesses and
          -- `α ≥ 2` (the `[115]` no arm) give `ι₂` its canonical exit-`(4)`
          -- witness, while (T2) says it has none.
          exact (((route8TwoCarrierExitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible witnesses
              (K .route8TrueTwoCarrierEntry) (K .route8TwoCarrierExit)
              (by key_fresh) (by key_fresh)).elimClosed
                (by infer_instance)).elim

set_option maxHeartbeats 8000000 in
/-- **Part IX: the route-`8` residual of exit `(8)`** (node `[109]` → `[110]`).

Nodes `[110]`--`[112]`, then the large-budget deficit test `[113]`: its
positive arm runs `[114]`--`[122]` and sends `[118]` to `[123]` (`selectedRouteEightCollection`);
its negative arm enters the unified target-defect/route-`8` ledger required by
`rem:why-unified` and reaches `[123]`, `[181]`, `[183]`--`[186]`.

`arm` names the Type A lane arms; the route-8 residual block and the `[113]`
deficit block complete the net-charge continuation. -/
-- EG-NODE [113] large-budget deficit: $D_A(\mathcal X_A)\ge(1/4-\tau_{\rm win})|R|-o(|R|)$
noncomputable def selectedRouteEightResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : TypeAExitFourArms selected)
    [FactKeys.Has (K .typeAExitFiveFree) known]
    [FactKeys.Has (K .typeAExitSixFree) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    (profileFresh : K .route8ResidualProfile ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by key_fresh)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known := by
      key_fresh)
    (coreFresh : K .route8CarrierCore ∉ known := by key_fresh)
    (trueResidualFresh : K .route8TrueResidual ∉ known := by key_fresh)
    (cutParityFresh : K .route8CarrierCutParity ∉ known := by key_fresh)
    (smallFresh : K .route8SmallCoreEntry ∉ known := by key_fresh)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known := by key_fresh)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by key_fresh)
    (censusFresh : K .route8Census ∉ known := by key_fresh)
    (twoFresh : K .route8TwoCarrierEntry ∉ known := by key_fresh)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known := by key_fresh)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known := by key_fresh)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known := by
      key_fresh)
    (twoCarrierExitFresh : K .route8TwoCarrierExit ∉ known := by key_fresh)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known := by
      key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (foldPeelsFresh : K .route8FoldPeels ∉ known := by key_fresh)
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
    (entriesAtGFresh : K .route8QuotientEntriesAtG ∉ known := by key_fresh)
    (pieceWindowAttachmentFresh : K .route8PieceWindowAttachment ∉ known := by key_fresh)
    (pieceChainCycleFresh : K .route8PieceChainCycle ∉ known := by key_fresh)
    (piecewiseRateFresh : K .route8PiecewiseRate ∉ known := by key_fresh)
    (pieceDominanceFresh : K .pieceDominanceIrreducible ∉ known := by key_fresh)
    (twoExitFresh : K .twoExitNewLength ∉ known := by key_fresh)
    (canonicalPieceDominanceFresh : K .canonicalPieceDominance ∉ known := by
      key_fresh)
    (canonicalTwoExitFresh : K .canonicalTwoExitNewLength ∉ known := by key_fresh)
    (sizeMonotoneFresh : K .twoExitSizeMonotone ∉ known := by key_fresh)
    (canonicalSizeMonotoneFresh : K .canonicalTwoExitSizeMonotone ∉ known := by
      key_fresh)
    (typeBSublinearCanonicalFormFresh : K .typeBSublinearCanonicalForm ∉ known := by key_fresh)
    (groupedAbsorbedCoreSubsetFresh : K .groupedAbsorbedCoreSubset ∉ known := by key_fresh)
    (typeBSublinearFailureArmsFresh : K .typeBSublinearFailureArms ∉ known := by key_fresh)
    (groupedCentresHighFresh : K .groupedCentresHigh ∉ known := by key_fresh)
    (handoffDegreeClauseEmptyFresh : K .handoffDegreeClauseEmpty ∉ known := by key_fresh)
    (pieceRoutingTotalFresh : K .pieceRoutingTotal ∉ known := by key_fresh)
    (coverPaymentFresh : K .coverPayment ∉ known := by key_fresh)
    (loadFailureSaturatedFresh : K .loadFailureSaturated ∉ known := by key_fresh)
    (unpaidAbsorbedWindowPortFresh : K .unpaidAbsorbedWindowPort ∉ known := by key_fresh)
    (receiverPortsAreWindowStubsFresh : K .receiverPortsAreWindowStubs ∉ known := by key_fresh)
    (saturatedReceiverBasinFresh : K .saturatedReceiverBasin ∉ known := by key_fresh)
    (loadFlowValueFresh : K .loadFlowValue ∉ known := by key_fresh)
    (coverFlowValueFresh : K .coverFlowValue ∉ known := by key_fresh)
    (pieceSizeProfileFresh : K .pieceSizeProfile ∉ known := by key_fresh)
    (bridgePieceMassDichotomyFresh : K .bridgePieceMassDichotomy ∉ known := by key_fresh)
    (traceIntoCentreStructureFresh : K .traceIntoCentreStructure ∉ known := by key_fresh)
    (traceIntoAbsorbedStructureFresh : K .traceIntoAbsorbedStructure ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
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
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
    [FactKeys.Has (K .twoSwitchForcedPath) known]
    [FactKeys.Has (K .crossSwitchFamily) known]
    [FactKeys.Has (K .highCentreSplitForced) known]
    [FactKeys.Has (K .sameVertexSwitchForcedPath) known]
    [FactKeys.Has (K .specWitnessStructure) known]
    [FactKeys.Has (K .remainderDeficiencyBelowCut) known]
    [FactKeys.Has (K .windowCutCapacity) known]
    [FactKeys.Has (K .primitiveCarrierCount) known]
    [FactKeys.Has (K .singleBoundaryShape) known]
    [FactKeys.Has (K .neighbourhoodPairCount) known]
    [FactKeys.Has (K .starCycleConstraint) known]
    [FactKeys.Has (K .meetingCycleConstraint) known]
    [FactKeys.Has (K .highDegreePairSum) known]
    [FactKeys.Has (K .vertexDeletionComponents) known]
    [FactKeys.Has (K .cyclesThroughVertex) known]
    [FactKeys.Has (K .cutVertexBlockPaths) known]
    [FactKeys.Has (K .cycleDoubleCount) known]
    [FactKeys.Has (K .threeRouteFan) known]
    [FactKeys.Has (K .threeRouteChain) known]
    [FactKeys.Has (K .windowPositionStubs) known]
    [FactKeys.Has (K .windowAttachmentGap) known]
    [FactKeys.Has (K .portEndDegree) known]
    [FactKeys.Has (K .hubLinkStructure) known]
    [FactKeys.Has (K .hubClassCounts) known]
    [FactKeys.Has (K .slotRelation) known]
    [FactKeys.Has (K .closedClasses) known]
    [FactKeys.Has (K .hubTwoHopLinks) known]
    [FactKeys.Has (K .slotLinear) known]
    [FactKeys.Has (K .remainderPathBounds) known]
    [FactKeys.Has (K .windowFreeGeometry) known]
    [FactKeys.Has (K .inducedPathAttachment) known]
    [FactKeys.Has (K .densityExcess) known]
    [FactKeys.Has (K .remainderSlack) known]
    [FactKeys.Has (K .hubWindowBudget) known]
    [FactKeys.Has (K .windowHubBounds) known]
    [FactKeys.Has (K .cubicNeighbourSupply) known]
    [FactKeys.Has (K .hubCountBound) known]
    [FactKeys.Has (K .lowEdgeParity) known]
    [FactKeys.Has (K .bigHubBound) known]
    [FactKeys.Has (K .bigHubVShapes) known]
    [FactKeys.Has (K .highSurplusBound) known]
    [FactKeys.Has (K .hubLengthThreePairs) known]
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected := by
  let burdened := selectedRouteEightProfile history
  -- `[113]`: the route-8-only lower bound is tested (`rem:why-unified`).
  match route8LargeBudgetDeficitRow (data := spineData) burdened
      (by key_fresh) (by key_fresh) with
  | .left deficit =>
      exact (selectedRouteEightCollection deficit).elim
  | .right deficitFails =>
      -- The carrier cores `[114]` are a fact of G on this arm too.
      let cored :=
        (route8CarrierCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          deficitFails (by key_fresh)
      exact selectedTypeBRoute8Continuation cored
        (arm.route8Residual (TypeAArmBlock_route8Residual.ret burdened)
          (Route8DeficitBlock_fails.ret deficitFails))

end HypostructureErdos64EG
