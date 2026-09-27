import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Route8Blocks

/-!
# Assembly: `TypeBSublinearOutcome` as a product of arm blocks

`TypeBSublinearOutcome` (node `[187]`, Type B sublinear failure) is returned
at one Lean site, the negative arm of `typeBSublinearDichotomy` in
`selectedRouteEightUnifiedResidual` (`Assembly/RouteEight/Local.lean`), and
is reached there by 1360 selected-root paths whose ledgers hold 1360 distinct
fact sets.  Those fact sets are exactly the 62 common keys of the generic
residual `TypeBSublinearOutcome` together with one choice in each factor of the
nested arm-block product of `Assembly/Residuals/Route8Blocks.lean`; the
product is full (all 5 × 4 × 68 combinations occur, each on one path).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **Node `[187]` (Type B sublinear failure), as a product of arm blocks**:
the 62 common facts of the generic residual, one of the 5 prefix blocks, one of
the 4 entropy blocks and one of the 68 continuation combinations. -/
abbrev TypeBSublinearOutcome_product (selected : EGInput.{u}) : Prop :=
  TypeBSublinearOutcome selected ∧
  Route8LanePrefix selected ∧
  EntropyArm selected ∧
  NetChargeContinuation selected

/-- The product residual forgets to the generic residual. -/
theorem TypeBSublinearOutcome_product.toGeneric {selected : EGInput.{u}}
    (h : TypeBSublinearOutcome_product selected) :
    TypeBSublinearOutcome selected :=
  h.1

/-- The return of `TypeBSublinearOutcome_product`, parameterised by the arm
choices: the generic facts are read with one `get` each
(`typeBSublinearReturn`), and each factor is the chosen arm block, itself built
by its `.ret` theorem with one `get` per key on the same ledger. -/
theorem typeBSublinearProductReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .route8BasinBurden) known]
    [FactKeys.Has (K .route8CarrierCore) known]
    [FactKeys.Has (K .typeBBridgeMass) known]
    [FactKeys.Has (K .typeBBridgeSublinear) known]
    [FactKeys.Has (K .route8UnifiedNegative) known]
    [FactKeys.Has (K .typeAExclusion) known]
    [FactKeys.Has (K .typeBBridgeReduction) known]
    [FactKeys.Has (K .route8PiecesClassified) known]
    [FactKeys.Has (K .route8ExtractedEntryCensus) known]
    [FactKeys.Has (K .typeBSublinearResidual) known]
    (prefixArm : Route8LanePrefix selected)
    (entropyArm : EntropyArm selected)
    (continuationArm : NetChargeContinuation selected) :
    TypeBSublinearOutcome_product selected :=
  ⟨typeBSublinearReturn history, prefixArm, entropyArm, continuationArm⟩

end HypostructureErdos64EG
