import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitFiveDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSevenDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSixDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitSixScopeDichotomy
import HypostructureErdos64EG.Assembly.RouteEight.Residual
import HypostructureErdos64EG.Assembly.TypeA.DecoratedHandoff

/-!
# Assembly: TypeA / ExitFiveToSeven

Exits `(5)`--`(8)` of the saturated Type A exit segment.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys exits `(5)`--`(8)` and their continuations may add. -/
noncomputable abbrev typeAExitFiveToEightKeys : FactKeys EGInput.{u} :=
  [K .typeAExitFive,
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
    K .route8GlobalSqueeze]

/-- **Nodes `[103]`--`[109]`: exits `(5)`--`(7)` and the route-`8` residual**, on
a saturated exit-`(4)`-free state of the exit segment (index-polymorphic).
`[103]` exit `(5)`: a target-complete response compression closes at `[104]`
against `cor:uncompressible`.  `[105]` exit `(6)`: a delocalizing response
equality closes at `[106]` — proper scope by `lem:proper-smearing` against
`lem:replacement`, whole-graph scope by `lem:no-silent-global-smearing` against
the selection's minimality.  `[107]` exit `(7)`: the decorated handoff fan
envelope, built at node `[108]`, returns to Type B at `[65]`.  Its absence is
`[109]`, the route-`8` residual continued in Part IX. -/
-- EG-NODE [103] exit 5? target-complete response compression
-- EG-NODE [104] uncompressibility contradiction
-- EG-NODE [105] exit 6? proper/whole-graph support dependence
-- EG-NODE [106] support-dependence branch closes
-- EG-NODE [107] exit 7? decorated handoff fan
-- EG-NODE [108] returns to Type B handoff
-- EG-NODE [109] route-8 residual continued in Part IX
-- EG-NODE [66] Type A exit 7 input from the Part VIII handoff
noncomputable def selectedTypeAExitFiveToEight
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8Rate) known]
    (fresh : List.Disjoint typeAExitFiveToEightKeys known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  -- `[103]`
  match typeAExitFiveDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left fiveHistory =>
      -- `[104]`
      exact ((closeIncompatible fiveHistory (K .uncompressible) (K .typeAExitFive)
        (by key_fresh)).elimClosed (by infer_instance)).elim
  | .right fiveFree =>
      -- `[105]`
      match typeAExitSixDichotomy (data := spineData) fiveFree
          (by key_fresh) (by key_fresh) with
      | .left sixHistory =>
          -- `[106]`
          match typeAExitSixScopeDichotomy (data := spineData) sixHistory
              (by key_fresh) (by key_fresh) with
          | .left properHistory =>
              exact ((AtomicCT.runAndCloseIncompatible
                (typeAExitSixProperRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData))
                properHistory (K .replacementExclusion) (K .typeAExitSixProper)
                (by key_fresh) (by key_fresh)).elimClosed
                  (by infer_instance)).elim
          | .right globalHistory =>
              exact ((AtomicCT.runAndCloseIncompatible
                (typeAExitSixGlobalRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData))
                globalHistory (K .selection) (K .typeAExitSixGlobal)
                (by key_fresh) (by key_fresh)).elimClosed
                  (by infer_instance)).elim
      | .right sixFree =>
          -- `[107]`
          match typeAExitSevenDichotomy (data := spineData) sixFree
              (by key_fresh) (by key_fresh) with
          | .left handoffHistory =>
              -- `[108]`: the decorated handoff fan envelope, then Type B.
              let envelope :=
                (typeAExitSevenEnvelopeRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run handoffHistory (by key_fresh)
              exact selectedTypeADecoratedHandoff envelope
          | .right residual =>
              -- `[109]`: the route-`8` residual, continued in Part IX.
              let normal :=
                (highCentreNormalFormRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run residual (by key_fresh)
              exact selectedRouteEightResidual normal

end HypostructureErdos64EG
