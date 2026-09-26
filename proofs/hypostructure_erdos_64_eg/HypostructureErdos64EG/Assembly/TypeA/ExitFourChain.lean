import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourFiniteDescent
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourPeelingStep
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourRetestDichotomy
import HypostructureErdos64EG.Assembly.TypeA.ExitFiveToSeven
import HypostructureErdos64EG.Assembly.TypeA.ExitFourDischargedRetest

/-!
# Assembly: TypeA / ExitFourChain

The saturated Type A exit segment `[101]`--`[109]`, shared by the visible and
the silent entry.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys the exit segment `[101]`--`[109]` and its continuations may add. -/
noncomputable abbrev typeAExitSegmentKeys : FactKeys EGInput.{u} :=
  [K .typeAExitFourFiniteDescent,
    K .typeASaturatedHandoffExitFour,
    K .typeAExitFourAbsent,
    K .typeAExitFourPeeled,
    K .typeASaturatedHandoffExitFourFree,
    K .typeAExitFourExhausted,
    K .typeAExitFourReceiverDischarged,
    K .typeAExitFive,
    K .typeAExitFiveFree,
    K .typeAExitSix,
    K .typeAExitSixFree,
    K .typeAExitSixProperScope,
    K .typeAExitSixGlobalScope,
    K .typeAExitSixProper,
    K .typeAExitSixGlobal,
    K .typeAExitSevenHandoff,
    K .typeAExitSevenAbsent,
    K .typeAExitSevenFree,
    K .typeASilentExitSevenFree,
    K .typeAExitEightNotSilent,
    K .highCentreNormalForm,
    closed,
    K .typeBDecoratedAssignedSupport,
    K .typeBFanEntry,
    K .typeBFanHeavyCentre,
    K .typeBFanDegreeFourCentres,
    K .typeBFanLocalDichotomy,
    K .sameCenterOpenPortCompatibility,
    K .typeBFanDegreeFourProfile,
    K .triangularFanCore,
    K .fanCertificateCap,
    K .fanCertificateMarked,
    K .fanCertificateResidual,
    K .fanCertificateResidualMass,
    K .typeBDirectCycle,
    K .typeBDirectCycleFree,
    K .typeBB2Choice,
    K .typeBOverlapObstruction,
    K .typeBHybridEntry,
    K .typeBDisjointLedger,
    K .typeBBridgeMass,
    K .typeBBridgeSublinear,
    K .route8UnifiedNegative,
    K .typeAExclusion,
    K .typeBBridgeReduction,
    K .route8PiecesClassified,
    K .typeBSublinearLedger,
    K .typeBSublinearResidual,
    K .route8UnifiedDeficit,
    K .route8QuotientFree,
    K .route8QuotientResidual,
    K .route8UnifiedEntryCensus,
    K .route8ExtractedEntryCensus,
    K .route8UnifiedTrueTwoCarrierEntry,
    K .route8PeelingDescent,
    K .route8StageRateFailed,
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
    K .route8JointBalance,
    K .route8TerminalNoGo,
    K .typeBExcluded,
    K .typeBExclusionResidual,
    K .typeBExclusionResidualMass,
    K .typeBOverlapObstructionMass,
    K .fanClosedPort,
    K .compatiblePairFanClosure,
    K .fanClosedPortTypeBRouting,
    K .compatiblePairTypeBRouting,
    K .triangularShoulderCompletion,
    K .triangularPortReturn,
    K .triangularFirstLanding,
    K .triangularCrossShoulder,
    K .triangularPortTypeBRouting,
    K .typeBGlobalLocalBridge,
    K .route8ResidualProfile,
    K .route8GlobalSqueeze,
    K .route8BasinBurden,
    K .route8LargeBudgetDeficit,
    K .route8LargeBudgetDeficitFails,
    K .route8CarrierCore,
    K .route8TrueResidual,
    K .route8CarrierCutParity,
    K .route8SmallCoreEntry,
    K .route8NoSmallCoreEntry,
    K .route8SmallCoreCollapse,
    K .route8Census,
    K .route8TwoCarrierEntry,
    K .route8NoTwoCarrierEntry,
    K .route8TrueTwoCarrierEntry,
    K .route8CarrierDeletionWitnesses,
    K .route8PrivateCarrierBudget,
    K .route8NoTwoCarrierContradiction]

/-- **Nodes `[101]`--`[102]` and the recompute-`L₄` loop**, on the shared entry of
the exit segment (index-polymorphic).  Both node `[99]`'s no arm and node `[94]`
enter here (`lem:typeA-exit4-residual-routing`).  `lem:typeA-exit4-finite-descent`
is committed at the entry state; then `[101]` tests exit `(4)`.  No: the entry
state is exit-`(4)`-free and exits `(5)`--`(8)` follow.  Yes: `[102]` peels the
witness's load (`lem:typeA-exit4-discharge`) and the saturated test is asked
again: if some saturated peeling state is exit-`(4)`-free, exits `(5)`--`(8)`
are asked there; otherwise every saturated state still realizes exit `(4)`, so
the finite descent discharges the peeled receiver
(`lem:typeA-saturated-handoff`, `lem:typeA-exit4-peeling-charge`) and its
target-defect loads enter Part IX at `[123]`. -/
-- EG-NODE [101] exit 4? target-defective quotient
-- EG-NODE [102] target-defect peels one load
noncomputable def selectedTypeAExitSegment
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8Rate) known]
    (fresh : List.Disjoint typeAExitSegmentKeys known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  -- `lem:typeA-exit4-finite-descent` at the entry state.
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  -- `[101]`
  match typeAExitFourDichotomy (data := spineData) descended
      (by key_fresh) (by key_fresh) with
  | .right absentHistory =>
      let exitFree :=
        (typeAExitFourFreeEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          absentHistory (by key_fresh)
      exact selectedTypeAExitFiveToEight exitFree
  | .left exitFourHistory =>
      -- `[102]`
      let peeled :=
        (typeAExitFourPeelingStepRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          exitFourHistory (by key_fresh)
      -- `[102]` → `[89]`: recompute `L₄`.
      match typeAExitFourRetestDichotomy (data := spineData) peeled
          (by key_fresh) (by key_fresh) with
      | .left exitFree =>
          exact selectedTypeAExitFiveToEight exitFree
      | .right exhaustedHistory =>
          let discharged :=
            (typeAExitFourDischargedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              exhaustedHistory (by key_fresh)
          exact selectedTypeAExitFourDischargedRetest discharged

end HypostructureErdos64EG
