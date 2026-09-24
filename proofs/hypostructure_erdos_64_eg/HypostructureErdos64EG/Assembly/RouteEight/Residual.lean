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
      simp [K_eq_iff])
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff])
    (jointBalanceFresh : K .route8JointBalance ∉ known := by
      simp [K_eq_iff])
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
      history (by simp [K_eq_iff, profileFresh])
  -- `[111]`
  let squeezed :=
    (route8GlobalSqueezeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      profile (by simp [K_eq_iff, squeezeFresh])
  -- `[112]`
  let burdened :=
    (route8BasinBurdenRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      squeezed (by simp [K_eq_iff, burdenFresh])
  -- `[113]`: the route-8-only lower bound is tested, because the manuscript's
  -- unified-demand correction explicitly forbids deriving it from the residual-C
  -- marker while target-defect supports may still carry negative mass.
  match route8LargeBudgetDeficitRow (data := spineData) burdened
      (by simp [K_eq_iff, deficitFresh])
      (by simp [K_eq_iff, deficitFailsFresh]) with
  | .left deficit =>
      -- `[114]`--`[116]` are the conditional route-8 reduction on the exact
      -- positive `[113]` ledger.
      let cored :=
        (route8CarrierCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          deficit (by simp [K_eq_iff, coreFresh])
      let trueResidual :=
        (route8TrueResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          cored (by simp [K_eq_iff, trueResidualFresh])
      let cutParity :=
        (route8CarrierCutParityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          trueResidual (by simp [K_eq_iff, cutParityFresh])
      match route8SmallCoreCollapseRow (data := spineData) cutParity
          (by simp [K_eq_iff, smallFresh])
          (by simp [K_eq_iff, noSmallFresh]) with
      | .left small =>
          let collapsed :=
            (route8SmallCoreExitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              small (by simp [K_eq_iff, collapseFresh])
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
              noSmall (by simp [K_eq_iff, censusFresh])
          match route8CarrierDichotomy (data := spineData) census
              (by simp [K_eq_iff, twoFresh])
              (by simp [K_eq_iff, noTwoFresh]) with
          | .right noTwo =>
              -- `[119]`--`[122]`: publish the exact private-incidence budget,
              -- then publish its contradiction with the census readings.
              let budgeted :=
                (route8PrivateCarrierBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run noTwo
                  (by simp [K_eq_iff, privateBudgetFresh])
              let contradicted :=
                (route8NoTwoCarrierContradictionRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run budgeted
                  (by simp [K_eq_iff, noTwoContradictionFresh])
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
                  (by simp [K_eq_iff, trueEntryFresh])
              let witnessed :=
                (route8CarrierDeletionWitnessesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run trueEntry
                  (by simp [K_eq_iff, deletionWitnessesFresh])
              -- `[124]`: canonical Q5 contradicts the no-exit-(4) fact on
              -- this same monotone ledger.
              let closed :=
                (route8TerminalNoGoRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run witnessed
                  (by simp [K_eq_iff, terminalNoGoFresh])
              exact (closed.get (K .route8TerminalNoGo)).down.elim
  | .right deficitFails =>
      -- The negative `[113]` fact remains in the ledger while the Type B
      -- allowance and unified target-defect/route-8 collection are recorded.
      let bridgeMass :=
        (bridgeFanMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          deficitFails (by simp [K_eq_iff, bridgeMassFresh])
      let bridgeSublinear :=
        (typeBBridgeSublinearRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          bridgeMass (by simp [K_eq_iff, bridgeSublinearFresh])
      -- `[123]`: publish the unified negative collection on this residual.
      let unifiedNegative :=
        (route8UnifiedNegativeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          bridgeSublinear (by simp [K_eq_iff, unifiedNegativeFresh])
      let typeAExcluded :=
        (typeAExclusionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unifiedNegative (by simp [K_eq_iff, typeAExclusionFresh])
      let typeBReduced :=
        (typeBBridgeReductionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          typeAExcluded (by simp [K_eq_iff, typeBBridgeReductionFresh])
      let classified :=
        (route8PiecesClassifiedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          typeBReduced (by simp [K_eq_iff, piecesClassifiedFresh])
      let extractedCensus :=
        (route8ExtractedEntryCensusRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          classified (by simp [K_eq_iff, extractedCensusFresh])
      match typeBSublinearDichotomy (data := spineData) extractedCensus
          (by simp [K_eq_iff, sublinearLedgerFresh])
          (by simp [K_eq_iff, sublinearResidualFresh]) with
      | .right residualHistory =>
          exact Or.inl
            (residualHistory.get (K .typeBSublinearResidual)).down
      | .left sublinearHistory =>
          let unifiedDeficit :=
            (route8UnifiedDeficitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              sublinearHistory (by simp [K_eq_iff, unifiedDeficitFresh])
          match route8QuotientDichotomy (data := spineData) unifiedDeficit
              (by simp [K_eq_iff, quotientFreeFresh])
              (by simp [K_eq_iff, quotientResidualFresh]) with
          | .right residualHistory =>
              exact Or.inr (Or.inl
                (residualHistory.get (K .route8QuotientResidual)).down)
          | .left quotientFreeHistory =>
              let census :=
                (route8UnifiedEntryCensusRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run quotientFreeHistory
                    (by simp [K_eq_iff, unifiedCensusFresh])
              let peeled := selectedLargeBudgetPressureCensus census
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (unifiedTrueFresh := by
                  simp [K_eq_iff, unifiedTrueFresh])
                (stageFailedFresh := by
                  simp [K_eq_iff, stageFailedFresh])
                (terminalFresh := by
                  simp [K_eq_iff, unifiedTerminalFresh])
                (demandLedgerFresh := by
                  simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by
                  simp [K_eq_iff, demandAbsorptionFresh])
                (openBoundarySaturatedFresh := by
                  simp [K_eq_iff, openBoundarySaturatedFresh])
                (demandUnitCountFresh := by
                  simp [K_eq_iff, demandUnitCountFresh])
                (windowBlockersFresh := by
                  simp [K_eq_iff, windowBlockersFresh])
                (windowShadowSignatureFresh := by
                  simp [K_eq_iff, windowShadowSignatureFresh])
                (windowShadowTailFresh := by
                  simp [K_eq_iff, windowShadowTailFresh])
                (windowShadowCycleFresh := by
                  simp [K_eq_iff, windowShadowCycleFresh])
                (windowShadowExcludedFresh := by
                  simp [K_eq_iff, windowShadowExcludedFresh])
                (demandResidualFresh := by
                  simp [K_eq_iff, demandResidualFresh])
              let unpaidExitFour :=
                selectedRouteEightUnpaidExitFourReduction peeled
                  (unifiedTrueFresh := by
                    simp [K_eq_iff, unifiedTrueFresh])
                  (residualFresh := by
                    simp [K_eq_iff, unpaidExitFourFresh])
                  (terminalFresh := by
                    simp [K_eq_iff, unifiedTerminalFresh])
              let visibleResidual :=
                selectedRouteEightVisibleResidual unpaidExitFour
                  (visibleFresh := by
                    simp [K_eq_iff, unifiedVisibleFresh])
              match silentClosure with
              | some silentData =>
                  letI : FactKeys.Has (K .typeASilentExitSevenFree) known :=
                    silentData.1
                  exact ((closeIncompatible visibleResidual
                    (K .typeASilentExitSevenFree)
                    (K .route8UnifiedVisibleResidual)
                    (by simp [K_eq_iff, silentData.2])).elimClosed
                      (by infer_instance)).elim
              | none =>
                  let visibleOverload :=
                    selectedRouteEightVisibleOverload visibleResidual
                      (overloadFresh := by
                        simp [K_eq_iff, unifiedVisibleOverloadFresh])
                  let jointBalance :=
                    selectedRouteEightJointBalance visibleOverload
                      (by simp [K_eq_iff, jointBalanceFresh])
                  exact Or.inr (Or.inr
                    (jointBalance.get (K .route8JointBalance)).down)

end HypostructureErdos64EG
