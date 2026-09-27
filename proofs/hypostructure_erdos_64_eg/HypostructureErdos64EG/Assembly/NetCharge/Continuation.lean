import Hypostructure.Graph.Strategy.SpineRows.AbsorbedConfigurationResidual
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.ExactCollisionDichotomy
import Hypostructure.Graph.Strategy.SpineRows.NegativeSupport
import Hypostructure.Graph.Strategy.SpineRows.NetChargeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.NetChargeLocalization
import Hypostructure.Graph.Strategy.SpineRows.TypeSplitDichotomy
import HypostructureErdos64EG.Assembly.Absorbed.Prerequisites
import HypostructureErdos64EG.Assembly.Absorbed.Residual
import HypostructureErdos64EG.Assembly.NetCharge.Boundary
import HypostructureErdos64EG.Assembly.TypeA.LowSurplusContinuation
import HypostructureErdos64EG.Assembly.TypeB.HighSurplusContinuation
import Hypostructure.Graph.Strategy.ColdCorridorRows.FirstFailureOccurrence
import Hypostructure.Graph.Strategy.ColdCorridorRows.FailureClauses
import Hypostructure.Graph.Strategy.ColdCorridorRows.HandoffTransfer

/-!
# Assembly: NetCharge / Continuation

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Every key committed by the net-charge continuation `[57]`--`[177]` and the
Type A / Type B / route-8 continuations it enters. -/
noncomputable abbrev netChargeContinuationKeys : FactKeys EGInput.{u} :=
  [K .netChargeCap, K .exactCollisionFails, K .absorbedConfigurationResidual,
    K .absorbedGermSplit, K .bridgeless, K .coldReturnCorridors,
    K .coldCorridorState,
    K .denseColdCorridorsTerminal, K .coldFirstFailureOccurrence,
    K .coldCutStatesDistinct, K .coldRepeatedStateResidual,
    K .coldHeavyEntryTerminal, K .coldDenseHeavyEntryResidual,
    K .coldFailureRouting, K .coldFailureCycle,
    K .coldFailureDefectRoute, K .coldFailureCompression,
    K .coldHandoffTransfer, K .coldExchangeBound,
    K .coldGermCandidates, K .coldPositiveGerm, K .coldGermFamilyPositive,
    K .absorbedGermFanData, K .typeBAbsorbedHalfEdge,
    K .typeBAbsorbedHalfEdgeAbsent, K .absorbedHandoffCore,
    K .absorbedHandoffCoreAbsent, K .absorbedF4Charge, K .typeBAbsorbedCharge,
    K .typeBFanEntry, K .coldGermRealized,
    K .coldGermDistinguished, K .coldGermSilent, K .coldGermRouted,
    K .coldSameInterfaceTable, K .coldBranchClosed,
    K .coldNeutralEqualLengthTerminal, K .coldAbsorbedNeutralConfiguration,
    K .coldSelectedFamilyEmpty,
    K .coldCanonicalNeutralConfiguration,
    K .coldGenuineSecondStrand, K .coldCanonicalReplacementSwap,
    K .coldCanonicalReplacementTrivial, K .coldTwoStrandSurvivor,
    K .coldWindowStubStructure, K .coldSymmetricPairExcluded,
    K .netChargeLocalization, K .netChargeNonNegative, K .netChargeNegative,
    K .negativeSupport, K .typeALowSurplus, K .typeBHighSurplus,
    K .typeABoundedSupport, K .typeAReceiverRouting, K .typeASaturatedReceiver,
    K .typeAUnsaturatedReceivers, K .typeAUnsaturatedDischarge,
    K .typeAPortReturn, K .typeAVisibleEntry,
    K .typeAVisibleFirstExcess, K .typeAExitOneReturn, K .typeAExitOneFree,
    K .typeAExitTwoTheta, K .typeAExitTwoFree, K .typeAExitThreeCollision,
    K .typeAExitThreeFree, closed, K .typeASaturatedExitEntry,
    K .typeAExitFourFiniteDescent, K .typeASaturatedHandoffExitFour,
    K .typeASaturatedHandoffExitFourFree, K .typeAExitFourPeeled,
    K .typeAExitFourReceiverDischarged, K .typeAExitFive, K .typeAExitFiveFree,
    K .typeAExitSix, K .typeAExitSixFree, K .typeAExitSixProper,
    K .typeAExitSixGlobal, K .typeAExitSevenFree, K .typeAExitSevenHandoff,
    K .typeASupport, K .typeANoVisibleEntry, K .typeAExitFourAbsent,
    K .typeAExitSixProperScope,
    K .typeAExitSixGlobalScope,
    K .typeBAssignedSupport,
    K .highCentreNormalForm, K .typeBFanHeavyCentre,
    K .typeBFanDegreeFourCentres, K .typeBFanLocalDichotomy,
    K .sameCenterOpenPortCompatibility, K .fanCertificateCap,
    K .fanCertificateMarked, K .fanCertificateResidual,
    K .fanCertificateResidualMass, K .typeBRoute8Entry, K .typeBDirectCycleFree,
    K .typeBB2Choice, K .typeBOverlapObstruction, K .typeBHybridEntry,
    K .typeBDisjointLedger, K .typeBBridgeMass, K .typeBBridgeSublinear,
    K .typeBExcluded, K .typeBExclusionResidual, K .typeBDegreeFourLedger,
    K .typeBDegreeFourOverlap,
    K .typeBDegreeFourClosed,
    K .typeBOverlapObstructionMass, K .typeBFanDegreeFourProfile,
    K .triangularFanCore, K .typeBDecoratedAssignedSupport,
    K .route8ResidualProfile, K .route8BasinBurden,
    K .route8LargeBudgetDeficit, K .route8LargeBudgetDeficitFails,
    K .route8CarrierCore, K .route8TrueResidual, K .route8CarrierCutParity,
    K .route8SmallCoreEntry, K .route8NoSmallCoreEntry,
    K .route8SmallCoreCollapse, K .route8Census, K .route8TwoCarrierEntry,
    K .route8NoTwoCarrierEntry, K .route8TrueTwoCarrierEntry,
    K .route8CarrierDeletionWitnesses, K .route8PrivateCarrierBudget,
    K .route8UnifiedNegative, K .typeAExclusion, K .typeBBridgeReduction,
    K .route8PiecesClassified, K .typeBSublinearLedger,
    K .typeBSublinearResidual, K .route8UnifiedDeficit, K .route8QuotientFree,
    K .route8QuotientResidual, K .route8UnifiedEntryCensus,
    K .route8ExtractedEntryCensus, K .route8UnifiedTrueTwoCarrierEntry,
    K .route8PeelingDescent, K .route8StageRateFailed, K .route8DemandLedger,
    K .route8DemandAbsorption, K .route8OpenBoundarySaturated,
    K .route8DemandUnitCount, K .route8WindowBlockers, K .windowShadowHitCycle,
    K .windowShadowHitExcluded, K .route8UnpaidExitFourResidual,
    K .route8UnifiedVisibleResidual, K .route8UnifiedVisibleOverload,
    K .route8JointBalance, K .route8TwoCarrierExit,
    K .route8UnifiedTwoCarrierExit, K .route8StageRate,
    K .route8UnpaidTwoCarrier, K .route8UnpaidWitnessFree,
    K .typeBGlobalLocalBridge, K .compatiblePairFanClosure,
    K .fanClosedPortTypeBRouting, K .compatiblePairTypeBRouting,
    K .triangularPortTypeBRouting, K .triangularShoulderCompletion,
    K .triangularPortReturn, K .triangularFirstLanding,
    K .triangularCrossShoulder, K .coldNoPositiveGerm, K .coldGermSomeRealizing, K .coldGermNoneRealizing,
    K .coldGermSomeDistinguishing, K .coldGermNoneDistinguishing,
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
    K .typeAExitSevenEnvelope]

set_option maxHeartbeats 8000000 in
/-- **Nodes `[57]`--`[64]`: the large-budget net-charge split**, on the `[56]`
residual of either spine arm.  `[57]` enters the asymptotic order regime and
reads the large-budget net cap; `[58]` localizes the charge; `[59]` splits on the
sign; the nonnegative arm is the `[60]` net-cap contradiction (cap gives
`N₀(R) < 0`, the sibling gives `N₀(R) ≥ 0`); the negative arm selects a connected
negative support `[61]` and `[62]` routes it to Type A `[63]` or Type B `[64]`.
The small-order complement `[57]`, and the Type A / Type B continuations, are the
next loud producers.  It is index-polymorphic over the arm's ledger, so both the
density-cap and route-8 arms use the same definition. -/
-- EG-NODE [57] large-budget net cap
-- EG-NODE [58] net charge \(\No\)
-- EG-NODE [59] \(\No(R)\ge0\)?
-- EG-NODE [60] net-cap contradiction
-- EG-NODE [61] choose connected \(\No(X)<0\)
-- EG-NODE [62] high-degree surplus?
-- EG-NODE [63] Type A continued in Part VIII
-- EG-NODE [64] Type B continued in Part VI
-- EG-NODE [173] exact collision test holds?
-- EG-NODE [174] absorbed-configuration residual: the exact collision fails and the selected cold corridors were charged to high-degree vertices
-- EG-NODE [86] Type A: $\sigma(X)=0$, hence $\defp(X)<|X|/4$
noncomputable def selectedNetChargeContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (fresh : List.Disjoint netChargeContinuationKeys.{u} known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedNetChargeBoundary selected := by
  -- `[57]` = `[173]`, `lem:exact-collision-test`: node `[56]`'s collision decided
  -- exactly on the current object (`K .netChargeCap`), with no condition on `n`.
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match exactCollisionDichotomy (data := spineData) bridgeless
      (by key_fresh) (by key_fresh) with
  | .right failsHistory =>
      -- `[174]`, `lem:exact-collision-test`: the failed collision rearranges to
      -- the cold-window lower bound `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`.
      let absorbed :=
        (absorbedConfigurationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failsHistory (by key_fresh)
      -- `[58]`'s localization of the net charge is a fact of G on this arm too.
      let localizedAbsorbed :=
        (netChargeLocalizationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          absorbed (by key_fresh)
      match selectedAbsorbedGermPrerequisites localizedAbsorbed with
      | .inl prepared =>
          -- `[175]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ
          -- residual (`selectedAbsorbedGermResidual`).
          exact Or.inr (Or.inl (selectedAbsorbedGermResidual prepared))
      | .inr repeated =>
          -- `[153]`, ¬(★): G's first equal-state pair, returned.
          exact Or.inr (Or.inr repeated)
  | .left capped =>
      -- The cold return corridors of G, their states, first failures, failure
      -- cycles, compression reading and handoff transfer are facts of G on
      -- this arm too (the absorbed arm publishes them at `[174]`): each row
      -- reads only `lem:bridgeless`, the partition and the selection.
      let corridors := nearCubicColdCorridorState capped
      let occurred :=
        (coldFirstFailureOccurrenceRow (data := spineData)).run corridors
          (by key_fresh)
      let cycled :=
        (coldFailureCycleRow (data := spineData)).run occurred (by key_fresh)
      let compressed :=
        (coldFailureCompressionRow (data := spineData)).run cycled (by key_fresh)
      let transferred :=
        (coldHandoffTransferRow (data := spineData)).run compressed
          (by key_fresh)
      -- `[58]`: `lem:netcharge-superadd` localizes negative charge to a piece.
      let localized :=
        (netChargeLocalizationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          transferred (by key_fresh)
      -- `[59]`: `N₀(R) ≥ 0?`
      match netChargeDichotomy (data := spineData) localized
          (by key_fresh) (by key_fresh) with
      | .left nonNegHistory =>
          -- `[60]`: the net-cap contradiction on the same canonical maximal
          -- packing: the cap gives `N₀(R) < 0`, the sibling `N₀(R) ≥ 0`.
          exact ((closeIncompatible nonNegHistory (K .netChargeNonNegative)
            (K .netChargeCap) (by key_fresh)).elimClosed
            (by infer_instance)).elim
      | .right negativeHistory =>
          -- `[61]`: select the connected negative support.
          let support :=
            (negativeSupportRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              negativeHistory (by key_fresh)
          -- `[62]`: high-degree surplus? Type A `[63]` / Type B `[64]`.
          match typeSplitDichotomy (data := spineData) support
              (by key_fresh) (by key_fresh) with
          | .left typeAHistory =>
              exact Or.inl (selectedTypeALowSurplusContinuation typeAHistory)
          | .right typeBHistory =>
              exact Or.inl (selectedTypeBHighSurplusContinuation typeBHistory)

end HypostructureErdos64EG
