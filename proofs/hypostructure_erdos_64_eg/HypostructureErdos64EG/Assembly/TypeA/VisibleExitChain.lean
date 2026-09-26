import Hypostructure.Graph.Strategy.SpineRows.TypeAExitOneDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitThreeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAExitTwoDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleExitEntry
import HypostructureErdos64EG.Assembly.TypeA.ExitFourChain

/-!
# Assembly: TypeA / VisibleExitChain

Exits `(1)`--`(3)` of the visible saturated lane.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys exits `(1)`--`(3)` and the exit segment may add. -/
noncomputable abbrev typeAVisibleExitKeys : FactKeys EGInput.{u} :=
  [K .typeAExitOneReturn,
    K .typeAExitOneFree,
    K .typeAExitTwoTheta,
    K .typeAExitTwoFree,
    K .typeAExitThreeCollision,
    K .typeAExitThreeFree,
    K .typeASaturatedExitEntry,
    K .typeAExitFourFiniteDescent,
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
    K .route8UnpaidExitFourResidual,
    K .route8UnifiedVisibleResidual,
    K .route8UnifiedVisibleOverload,
    K .route8JointBalance,
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
    K .route8UnpaidWitnessFree]

/-- **Nodes `[95]`--`[100]`: exits `(1)`--`(3)`** on node `[93]`'s visible arm
(index-polymorphic).  `def:typeA-saturated-exits`, `lem:typeA-exits-discharged`:
exit `(1)` — a Mersenne anchored return — closes at `[96]` against the
return-avoidance invariant `[5]`--`[7]`; exit `(2)` — a power-of-two
common-port theta — closes at `[98]` against the selection; exit `(3)` — a
`P₁₃` label collision — closes at `[100]` against the selection.  The
exit-`(3)`-free arm enters the shared exit segment at `[101]`. -/
-- EG-NODE [95] exit 1? Mersenne return
-- EG-NODE [96] target cycle
-- EG-NODE [97] exit 2? power-of-two theta
-- EG-NODE [98] target cycle
-- EG-NODE [99] exit 3? $P_{13}$ label collision
-- EG-NODE [100] label/target collision
noncomputable def selectedTypeAVisibleExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAVisibleEntry) known]
    [FactKeys.Has (K .returnAvoidance) known]
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
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8Rate) known]
    (fresh : List.Disjoint typeAVisibleExitKeys known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  -- `[95]`
  match typeAExitOneDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left returnHistory =>
      -- `[96]`
      exact ((closeIncompatible returnHistory (K .returnAvoidance)
        (K .typeAExitOneReturn) (by key_fresh)).elimClosed
          (by infer_instance)).elim
  | .right oneFree =>
      -- `[97]`
      match typeAExitTwoDichotomy (data := spineData) oneFree
          (by key_fresh) (by key_fresh) with
      | .left thetaHistory =>
          -- `[98]`
          exact ((closeIncompatible thetaHistory (K .selection)
            (K .typeAExitTwoTheta) (by key_fresh)).elimClosed
              (by infer_instance)).elim
      | .right twoFree =>
          -- `[99]`
          match typeAExitThreeDichotomy (data := spineData) twoFree
              (by key_fresh) (by key_fresh) with
          | .left collisionHistory =>
              -- `[100]`
              exact ((closeIncompatible collisionHistory (K .selection)
                (K .typeAExitThreeCollision) (by key_fresh)).elimClosed
                  (by infer_instance)).elim
          | .right threeFree =>
              -- `[99]` → `[101]`: the shared exit segment.
              let entered :=
                (typeAVisibleExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  threeFree (by key_fresh)
              exact selectedTypeAExitSegment entered

end HypostructureErdos64EG
