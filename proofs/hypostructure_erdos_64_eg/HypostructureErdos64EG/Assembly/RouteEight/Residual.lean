import Hypostructure.Graph.Strategy.SpineRows.BridgeFanMass
import Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCore
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCutParity
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDeletionWitnesses
import Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8Census
import Hypostructure.Graph.Strategy.SpineRows.Route8ExtractedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8GlobalSqueeze
import Hypostructure.Graph.Strategy.SpineRows.Route8LargeBudgetDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8NoTwoCarrierContradiction
import Hypostructure.Graph.Strategy.SpineRows.Route8PiecesClassified
import Hypostructure.Graph.Strategy.SpineRows.Route8PrivateCarrierBudget
import Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8ResidualProfile
import Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreCollapse
import Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreExit
import Hypostructure.Graph.Strategy.SpineRows.Route8TerminalNoGo
import Hypostructure.Graph.Strategy.SpineRows.Route8TrueResidual
import Hypostructure.Graph.Strategy.SpineRows.Route8TrueTwoCarrierEntry
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedNegative
import Hypostructure.Graph.Strategy.SpineRows.TypeAExclusion
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeReduction
import Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeSublinear
import Hypostructure.Graph.Strategy.SpineRows.TypeBSublinearDichotomy
import Hypostructure.Graph.Strategy.TypeAExitRun
import HypostructureErdos64EG.Assembly.RouteEight.Boundary
import HypostructureErdos64EG.Assembly.RouteEight.Local

/-!
# Assembly: RouteEight / Residual

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

noncomputable def selectedRouteEightResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      key_fresh)
    (silentClosure : Option
      (PProd (FactKeys.Has (K .typeASilentExitSevenFree) known)
        (closed ∉ known)) := none)
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .cubicBaseline) known] :
    SelectedRouteEightBoundary selected := by
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
  -- unified-demand correction explicitly forbids deriving it from the residual-C
  -- marker while target-defect supports may still carry negative mass.
  match route8LargeBudgetDeficitRow (data := spineData) burdened
      (by key_fresh)
      (by key_fresh) with
  | .left deficit =>
      -- `[114]`--`[116]` are the conditional route-8 reduction on the exact
      -- positive `[113]` ledger.
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
      match route8SmallCoreCollapseRow (data := spineData) cutParity
          (by key_fresh)
          (by key_fresh) with
      | .left small =>
          let collapsed :=
            (route8SmallCoreExitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              small (by key_fresh)
          have trueFacts := (collapsed.get (K .route8TrueResidual)).down
          have collapseFacts := (collapsed.get (K .route8SmallCoreCollapse)).down
          obtain ⟨_componentCore, component, componentMem, receiver, receiverMem,
            load, loadMem, _alphaSmall, alternatives⟩ := collapseFacts
          have minimal :=
            (trueFacts.2 component componentMem).2 receiver receiverMem |>.2.2
              load loadMem |>.2.1
          rcases alternatives with localDefect | compression | delocalization | separator
          · exact (minimal.2.1 localDefect).elim
          · -- `[116]`: the nontrivial target-complete quotient `ρ°_𝒞` is
            -- alternative (b) of `def:typeA-trace-basin` itself.
            exact (minimal.2.2.1 compression).elim
          · exact (minimal.2.2.2.1 delocalization).elim
          · exact (minimal.2.2.2.2 separator).elim
      | .right noSmall =>
          -- `[117]`: run the carrier decision on the exact `Ξ(𝒳_A)` census.
          let census :=
            (route8CensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              noSmall (by key_fresh)
          match route8CarrierDichotomy (data := spineData) census
              (by key_fresh)
              (by key_fresh) with
          | .right noTwo =>
              -- `[119]`--`[122]`: publish the exact private-incidence budget,
              -- then publish its contradiction with the census readings.
              let budgeted :=
                (route8PrivateCarrierBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run noTwo
                  (by key_fresh)
              let contradicted :=
                (route8NoTwoCarrierContradictionRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run budgeted
                  (by key_fresh)
              exact (contradicted.get
                (K .route8NoTwoCarrierContradiction)).down.elim
          | .left twoCarrier =>
              -- `[118]`: attach the true-residual no-exit fact and every
              -- essential-carrier deletion witness to the selected entry.
              let trueEntry :=
                (route8TrueTwoCarrierEntryRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run twoCarrier
                  (by key_fresh)
              let witnessed :=
                (route8CarrierDeletionWitnessesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run trueEntry
                  (by key_fresh)
              -- `[124]`: canonical Q5 contradicts the no-exit-(4) fact on
              -- this same monotone ledger.
              let closed :=
                (route8TerminalNoGoRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run witnessed
                  (by key_fresh)
              exact (closed.get (K .route8TerminalNoGo)).down.elim
  | .right deficitFails =>
      -- The negative `[113]` fact remains in the ledger while the Type B
      -- allowance and unified target-defect/route-8 collection are recorded.
      let bridgeMass :=
        (bridgeFanMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          deficitFails (by key_fresh)
      let bridgeSublinear :=
        (typeBBridgeSublinearRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          bridgeMass (by key_fresh)
      -- `[123]`: publish the unified negative collection on this residual.
      let unifiedNegative :=
        (route8UnifiedNegativeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          bridgeSublinear (by key_fresh)
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
      match typeBSublinearDichotomy (data := spineData) extractedCensus
          (by key_fresh)
          (by key_fresh) with
      | .right residualHistory =>
          exact Or.inl
            (residualHistory.get (K .typeBSublinearResidual)).down
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
                (unifiedTrueFresh := by
                  key_fresh)
                (stageFailedFresh := by
                  key_fresh)
                (terminalFresh := by
                  key_fresh)
                (demandLedgerFresh := by
                  key_fresh)
                (demandAbsorptionFresh := by
                  key_fresh)
                (openBoundarySaturatedFresh := by
                  key_fresh)
                (demandUnitCountFresh := by
                  key_fresh)
                (windowBlockersFresh := by
                  key_fresh)
                (windowShadowSignatureFresh := by
                  key_fresh)
                (windowShadowTailFresh := by
                  key_fresh)
                (windowShadowCycleFresh := by
                  key_fresh)
                (windowShadowExcludedFresh := by
                  key_fresh)
                (demandResidualFresh := by
                  key_fresh)
              let unpaidExitFour :=
                selectedRouteEightUnpaidExitFourReduction peeled
                  (unifiedTrueFresh := by
                    key_fresh)
                  (residualFresh := by
                    key_fresh)
                  (terminalFresh := by
                    key_fresh)
              let visibleResidual :=
                selectedRouteEightVisibleResidual unpaidExitFour
                  (visibleFresh := by
                    key_fresh)
              match silentClosure with
              | some silentData =>
                  letI : FactKeys.Has (K .typeASilentExitSevenFree) known :=
                    silentData.1
                  exact ((closeIncompatible visibleResidual
                    (K .typeASilentExitSevenFree)
                    (K .route8UnifiedVisibleResidual)
                    (by have closureFresh := silentData.2; key_fresh)).elimClosed
                      (by infer_instance)).elim
              | none =>
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
