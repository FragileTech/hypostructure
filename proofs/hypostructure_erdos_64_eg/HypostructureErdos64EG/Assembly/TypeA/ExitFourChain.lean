import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourFiniteDescent
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourPeelingStep
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourRetestDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAPeeledExits
import Hypostructure.Graph.Strategy.TypeAExitRun
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
    K .typeAExitSevenFree,
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
    K .typeBRoute8Entry,
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
    K .windowShadowHitCycle,
    K .windowShadowHitExcluded,
    K .route8UnpaidExitFourResidual,
    K .route8UnifiedVisibleResidual,
    K .route8UnifiedVisibleOverload,
    K .route8JointBalance,
    K .typeBExcluded,
    K .typeBExclusionResidual,
    K .typeBDegreeFourLedger,
    K .typeBDegreeFourOverlap,
    K .typeBDegreeFourClosed,
    K .typeBOverlapObstructionMass,
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
    K .route8TwoCarrierExit,
    K .route8UnifiedTwoCarrierExit,
    K .route8StageRate,
    K .route8UnpaidTwoCarrier,
    K .route8UnpaidWitnessFree,
    K .typeAExitSevenEnvelope,
    K .typeAPeeledSaturatedReceiver,
    K .typeAPeeledUnsaturatedDischarge,
    K .typeAPeeledVisibleEntry,
    K .typeAPeeledNoVisibleEntry,
    K .typeAPeeledSilentExcess,
    K .typeAPeeledExitOneReturn,
    K .typeAPeeledExitOneFree,
    K .typeAPeeledExitTwoTheta,
    K .typeAPeeledExitTwoFree,
    K .typeAPeeledExitThreeCollision,
    K .typeAPeeledExitThreeFree,
    K .typeAExitThreeCycle,
    K .typeBAbsorbedCharge]

set_option maxHeartbeats 8000000 in
/-- **Nodes `[101]`--`[102]` and the recompute-`L₄` loop**, on the shared entry of
the exit segment (index-polymorphic).  Both node `[99]`'s no arm and node `[94]`
enter here (`lem:typeA-exit4-residual-routing`).  `lem:typeA-exit4-finite-descent`
is committed at the entry state; then `[101]` tests exit `(4)`.  No: the entry
state is the terminal state, exit-`(4)`-free, and exits `(5)`--`(8)` follow.
Yes: `[102]` peels the witness's load (`lem:typeA-exit4-discharge`) and node
`[89]` is asked again with `L₄` (tex 1095).  If some receiver of `X₀` is still
saturated after its canonical peeling sequence stops, its terminal state
re-enters node `[93]`: exits `(1)`--`(3)` at the overloaded port of `P₄(w)` on
the visible lane (`lem:typeA-unpeeled-visible-routing`), the residual excess
`E₄(w)` on the silent lane (`lem:typeA-unpeeled-silent-routing`), then node
`[101]` (exit-`(4)`-free at the terminal set) and exits `(5)`--`(8)`.  If every
receiver is unsaturated after peeling, node `[90]` holds with `L₄` and node
`[91]` gives the charge bound on the unpeeled loads; the peeled loads left the
pure Type A charge through exit `(4)`, and the support enters Part IX at node
`[123]` (`rem:typeA-exit4-peeling-use`, alternative (iii) of
`lem:density-mersenne`).

`arm` names the prefix, entropy and visible-entry arms; the Type A lane block
and each exit-`(4)` arm's block are added here. -/
-- EG-NODE [101] exit 4? target-defective quotient
-- EG-NODE [102] target-defect peels one load
noncomputable def selectedTypeAExitSegment
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (arm : TypeAEntryArms selected)
    [FactKeys.Has (K .netChargeNegative) known]
    [FactKeys.Has (K .typeABoundedSupport) known]
    [FactKeys.Has (K .typeAPortReturn) known]
    [FactKeys.Has (K .typeASaturatedReceiver) known]
    [FactKeys.Has (K .typeASupport) known]
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .minDegreeBaseline) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8Rate) known]
    (fresh : List.Disjoint typeAExitSegmentKeys known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
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
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .everyWitnessSpectrumSplit) known]
    [FactKeys.Has (K .twoHighForcedPath) known]
    [FactKeys.Has (K .sameHighForcedPath) known]
    [FactKeys.Has (K .packingOrderBound) known]
    [FactKeys.Has (K .noSuppressionChordViolation) known]
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
    [FactKeys.Has (K .surplusDartIdentity) known]
    [FactKeys.Has (K .highDegreeCountBound) known]
    [FactKeys.Has (K .admissibleQuotientsLabelInjective) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  -- `lem:typeA-exit4-finite-descent` at the entry state.
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  have lane : TypeALaneArms selected :=
    ⟨arm, NetChargeLaneBlock_typeALowSurplus.ret descended⟩
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
        ⟨lane, Or.inl (TypeAExitFourBlock_absent.ret exitFree)⟩
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
      | .left saturatedHistory =>
          -- `[93]` after peeling, at the terminal state.
          match typeAPeeledVisibleEntryDichotomy (data := spineData)
              saturatedHistory (by key_fresh) (by key_fresh) with
          | .left visibleHistory =>
              -- `[95]` after peeling.
              match typeAPeeledExitOneDichotomy (data := spineData) visibleHistory
                  (by key_fresh) (by key_fresh) with
              | .left returnHistory =>
                  -- `[96]`
                  exact ((closeIncompatible returnHistory (K .returnAvoidance)
                    (K .typeAPeeledExitOneReturn) (by key_fresh)).elimClosed
                      (by infer_instance)).elim
              | .right oneFree =>
                  -- `[97]` after peeling.
                  match typeAPeeledExitTwoDichotomy (data := spineData) oneFree
                      (by key_fresh) (by key_fresh) with
                  | .left thetaHistory =>
                      -- `[98]`
                      exact ((closeIncompatible thetaHistory (K .selection)
                        (K .typeAPeeledExitTwoTheta) (by key_fresh)).elimClosed
                          (by infer_instance)).elim
                  | .right twoFree =>
                      -- `[99]` after peeling.
                      match typeAPeeledExitThreeDichotomy (data := spineData)
                          twoFree (by key_fresh) (by key_fresh) with
                      | .left collisionHistory =>
                          -- `[100]`
                          exact ((AtomicCT.runAndCloseIncompatible
                            (typeAPeeledExitThreeCycleRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData))
                            collisionHistory (K .selection) (K .typeAExitThreeCycle)
                            (by key_fresh) (by key_fresh)).elimClosed
                              (by infer_instance)).elim
                      | .right threeFree =>
                          -- `[101]` at the terminal set: exit-`(4)`-free.
                          let exitFree :=
                            (typeAPeeledVisibleExitFourFreeRow
                              (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).run threeFree (by key_fresh)
                          exact selectedTypeAExitFiveToEight exitFree
                            ⟨lane, Or.inr (Or.inl
                              (TypeAExitFourBlock_peeledVisible.ret exitFree))⟩
          | .right silentHistory =>
              -- `[94]` after peeling: the residual excess `E₄(w)`.
              let excess :=
                (typeAPeeledSilentExcessRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run silentHistory (by key_fresh)
              -- `[101]` at the terminal set: exit-`(4)`-free.
              let exitFree :=
                (typeAPeeledSilentExitFourFreeRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run excess (by key_fresh)
              exact selectedTypeAExitFiveToEight exitFree
                ⟨lane, Or.inr (Or.inr
                  (TypeAExitFourBlock_peeledNoVisible.ret exitFree))⟩
      | .right dischargedHistory =>
          -- `[90]` after peeling; `[91]`: the charge bound on the unpeeled
          -- loads (`lem:typeA-exit4-peeling-charge`).
          let discharged :=
            (typeAPeeledUnsaturatedDischargeRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run dischargedHistory (by key_fresh)
          exact selectedTypeAExitFourDischargedRetest discharged lane

end HypostructureErdos64EG
