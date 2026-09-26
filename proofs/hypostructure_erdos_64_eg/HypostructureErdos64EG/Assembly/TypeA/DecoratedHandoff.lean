import Hypostructure.Graph.Strategy.SpineRows.TypeBDecoratedAssignedSupport
import HypostructureErdos64EG.Assembly.TypeB.DecoratedContinuation

/-!
# Assembly: TypeA / DecoratedHandoff

Node `[108]` → Type B `[65]`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- The keys the decorated Type B continuation from node `[108]` may add. -/
noncomputable abbrev typeADecoratedHandoffKeys : FactKeys EGInput.{u} :=
  [K .typeBDecoratedAssignedSupport,
    K .typeBFanEntry,
    K .highCentreNormalForm,
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
    closed,
    K .route8TwoCarrierExit,
    K .route8UnifiedTwoCarrierExit,
    K .route8StageRate,
    K .route8UnpaidTwoCarrier,
    K .route8UnpaidWitnessFree]

/-- **Node `[108]` → Type B `[65]` on the decorated envelope**: the exact
envelope committed at `[108]` (`K .typeAExitSevenHandoff`) enters the Type B
branch at `[65]`.  There `typeBDecoratedAssignedSupportRow` reads the inherited
selection, normalization, and uncompressibility facts, proves
`lem:decorated-fan-admissibility`, and commits the envelope's assigned support.
Then `[67]`--`[70]` run on that decorated envelope
(`selectedTypeBDecoratedContinuation`). -/
-- EG-NODE [65] Type B assigned support: high-degree fan centers and decorated handoff data
noncomputable def selectedTypeADecoratedHandoff
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (fresh : List.Disjoint typeADecoratedHandoffKeys known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  have fresh' := fresh
  repeat (rw [List.disjoint_cons_left] at fresh'; obtain ⟨_fresh, fresh'⟩ := fresh')
  let assigned :=
    (typeBDecoratedAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  exact selectedTypeBDecoratedContinuation assigned
    (normalFormFresh := by key_fresh)
    (decoratedHeavyFresh := by key_fresh)
    (decoratedDegreeFourFresh := by key_fresh)
    (decoratedLocalFresh := by key_fresh)
    (decoratedCompatibilityFresh := by key_fresh)
    (decoratedProfileFresh := by key_fresh)
    (decoratedTriangularCoreFresh := by key_fresh)
    (fanCapFresh := by key_fresh)
    (decoratedMarkedFresh := by key_fresh)
    (decoratedResidualFresh := by key_fresh)
    (decoratedCertificateMassFresh := by key_fresh)
    (decoratedCycleFresh := by key_fresh)
    (decoratedFreeFresh := by key_fresh)
    (decoratedB2ChoiceFresh := by key_fresh)
    (decoratedB2ObstructionFresh := by key_fresh)
    (decoratedHybridFresh := by key_fresh)
    (decoratedLedgerFresh := by key_fresh)
    (decoratedBridgeMassFresh := by key_fresh)
    (decoratedBridgeSublinearFresh := by key_fresh)
    (unifiedNegativeFresh := by key_fresh)
    (typeAExclusionFresh := by key_fresh)
    (typeBBridgeReductionFresh := by key_fresh)
    (piecesClassifiedFresh := by key_fresh)
    (sublinearLedgerFresh := by key_fresh)
    (sublinearResidualFresh := by key_fresh)
    (unifiedDeficitFresh := by key_fresh)
    (quotientFreeFresh := by key_fresh)
    (quotientResidualFresh := by key_fresh)
    (unifiedCensusFresh := by key_fresh)
    (extractedCensusFresh := by key_fresh)
    (unifiedTrueFresh := by key_fresh)
    (peelingFresh := by key_fresh)
    (stageFailedFresh := by key_fresh)
    (demandLedgerFresh := by key_fresh)
    (demandAbsorptionFresh := by key_fresh)
    (openBoundarySaturatedFresh := by key_fresh)
    (demandUnitCountFresh := by key_fresh)
    (windowBlockersFresh := by key_fresh)
    (windowShadowSignatureFresh := by key_fresh)
    (windowShadowTailFresh := by key_fresh)
    (windowShadowCycleFresh := by key_fresh)
    (windowShadowExcludedFresh := by key_fresh)
    (demandResidualFresh := by key_fresh)
    (unpaidExitFourFresh := by key_fresh)
    (unifiedVisibleFresh := by key_fresh)
    (unifiedVisibleOverloadFresh := by key_fresh)
    (jointBalanceFresh := by key_fresh)
    (unifiedTerminalFresh := by key_fresh)
    (decoratedExcludedFresh := by key_fresh)
    (decoratedExclusionResidualFresh := by key_fresh)
    (decoratedExclusionMassFresh := by key_fresh)
    (decoratedObstructionMassFresh := by key_fresh)
    (fanClosedFresh := by key_fresh)
    (compatibleClosureFresh := by key_fresh)
    (fanClosedRoutingFresh := by key_fresh)
    (compatibleRoutingFresh := by key_fresh)
    (shoulderCompletionFresh := by key_fresh)
    (portReturnFresh := by key_fresh)
    (firstLandingFresh := by key_fresh)
    (crossShoulderFresh := by key_fresh)
    (triangularRoutingFresh := by key_fresh)
    (decoratedGlobalLocalBridgeFresh := by key_fresh)

end HypostructureErdos64EG
