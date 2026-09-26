import Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCore
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCutParity
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDeletionWitnesses
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8Census
import Hypostructure.Graph.Strategy.SpineRows.Route8GlobalSqueeze
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

/-- **Nodes `[110]`--`[112]`**: the exit-`(8)` residual profile, the route-`8`
collection `𝒳_A` with its cleared deficit, and the burden
`s·D_A(𝒳_A) ≤ N_basin(𝒳_A)`, appended to the incoming ledger. -/
-- EG-NODE [110] exit (8): route-8 residual profile
-- EG-NODE [111] global squeeze extracts a route-8 Type A collection $\mathcal X_A$ carrying $D_A(\mathcal X_A)$
-- EG-NODE [112] route-8 burden: $N_{\rm basin}(\mathcal X_A)\ge4D_A(\mathcal X_A)$
noncomputable def selectedRouteEightProfile
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (profileFresh : K .route8ResidualProfile ∉ known := by key_fresh)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh) :
    ExactLedger EGInput.{u} selected
      ([K .route8BasinBurden, K .route8GlobalSqueeze, K .route8ResidualProfile]
        ++ known) :=
  -- `[110]`
  let profile :=
    (route8ResidualProfileRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[111]`
  let squeezed :=
    (route8GlobalSqueezeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      profile (by key_fresh)
  -- `[112]`
  let burdened :=
    (route8BasinBurdenRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      squeezed (by key_fresh)
  -- `[113]`: the route-8-only lower bound is tested, because the manuscript's
  -- unified-demand correction (`rem:why-unified`) forbids deriving it while
  -- target-defect supports may still carry negative mass.
  burdened

/-- **Nodes `[114]`--`[124]` on the positive arm of `[113]`.**

`[114]` publishes the carrier cores, the true residual and the cut parity;
`[115]` decides the zero/one-core entry, closed at `[116]` against the true
residual; `[117]` decides the two-support entry: its no arm publishes the
private-support budget `[119]`--`[120]`, closed at `[121]`--`[122]` against the
census, and its yes arm `[118]` publishes the true two-support entry with its
deletion witnesses, closed at `[124]`.  Every arm closes. -/
-- EG-NODE [114] each entry passes to its canonical minimal target-complete response-support core inside the declared $u$-supported response algebra
-- EG-NODE [115] some entry has $\alpha_{\mathcal X}(\xi)\le1$?
-- EG-NODE [116] exits (4)--(7) occur
-- EG-NODE [117] some entry has $\pi_{\mathcal X}(\xi)\le2$?
-- EG-NODE [118] two-support route-8 entry
-- EG-NODE [119] no two-support entry: every indexed entry has at least three private essential boundary incidences
-- EG-NODE [120] private-support budget: $3N_{\rm basin}(\mathcal X_A)\le\defp(R)+o(|R|)\le\tau_{\rm win}|R|+o(|R|)$
-- EG-NODE [121] burden plus deficit: $N_{\rm basin}(\mathcal X_A)\ge4(1/4-\tau_{\rm win})|R|-o(|R|)$
-- EG-NODE [122] contradiction: $\tau_{\rm win}\ge12(1/4-\tau_{\rm win})$, but $\tau_{\rm win}<3/13$
theorem selectedRouteEightCollectionCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (deficit : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8ResidualProfile) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8LargeBudgetDeficit) known]
    [FactKeys.Has (K .route8Rate) known]
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
    (closureFresh : closed ∉ known := by key_fresh) : False := by
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
      -- `[117]` on the exact `Ξ(𝒳_A)` census.
      let census :=
        (route8CensusRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          noSmall (by key_fresh)
      match route8CarrierDichotomy (data := spineData) census
          (by key_fresh) (by key_fresh) with
      | .right noTwo =>
          -- `[119]`--`[120]` publish the private budget; `[121]`--`[122]`
          -- close it against the census readings.
          exact (((route8PrivateCarrierBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible noTwo
              (K .route8Census) (K .route8PrivateCarrierBudget)
              (by key_fresh) (by key_fresh)).elimClosed
                (by infer_instance)).elim
      | .left twoCarrier =>
          -- `[118]`: the true two-support entry and its declared deletion
          -- witnesses.
          let trueEntry :=
            (route8TrueTwoCarrierEntryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run twoCarrier (by key_fresh)
          let witnessed :=
            (route8CarrierDeletionWitnessesRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run trueEntry (by key_fresh)
          -- `[124]`: the canonical Q5 exit-(4) witness against the
          -- entry's absent exit `(4)`.
          exact (((route8TwoCarrierExitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible witnessed
              (K .route8TrueTwoCarrierEntry) (K .route8TwoCarrierExit)
              (by key_fresh) (by key_fresh)).elimClosed
                (by infer_instance)).elim

/-- **Part IX: the route-`8` residual of exit `(8)`** (visible Type A lane).

Nodes `[110]`--`[112]`, then the large-budget deficit test `[113]`: its
positive arm closes at `[114]`--`[124]` (`selectedRouteEightCollectionCloses`);
its negative arm enters the unified target-defect/route-`8` ledger required by
`rem:why-unified` and reaches `[123]`, `[181]`, `[183]`--`[186]`. -/
-- EG-NODE [113] large-budget deficit: $D_A(\mathcal X_A)\ge(1/4-\tau_{\rm win})|R|-o(|R|)$
noncomputable def selectedRouteEightResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (profileFresh : K .route8ResidualProfile ∉ known := by key_fresh)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by key_fresh)
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
  let burdened := selectedRouteEightProfile history
  -- `[113]`: the route-8-only lower bound is tested (`rem:why-unified`).
  match route8LargeBudgetDeficitRow (data := spineData) burdened
      (by key_fresh) (by key_fresh) with
  | .left deficit => exact (selectedRouteEightCollectionCloses deficit).elim
  | .right deficitFails => exact selectedTypeBRoute8Continuation deficitFails

/-- **Part IX on the silent Type A lane** (the silent arm of
`typeASilentExitSevenDichotomy`, carrying `K .typeASilentExitSevenFree`).
Identical to `selectedRouteEightResidual`, except that the unified branch closes
at node `[184]`: the lane's selected silent excess load is a unified entry,
which node `[184]` makes visible. -/
noncomputable def selectedRouteEightResidualSilent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .typeASilentExitSevenFree) known]
    (profileFresh : K .route8ResidualProfile ∉ known := by key_fresh)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by key_fresh)
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
  let burdened := selectedRouteEightProfile history
  -- `[113]`: the route-8-only lower bound is tested (`rem:why-unified`).
  match route8LargeBudgetDeficitRow (data := spineData) burdened
      (by key_fresh) (by key_fresh) with
  | .left deficit => exact (selectedRouteEightCollectionCloses deficit).elim
  | .right deficitFails => exact selectedTypeBRoute8ContinuationSilent deficitFails

end HypostructureErdos64EG
