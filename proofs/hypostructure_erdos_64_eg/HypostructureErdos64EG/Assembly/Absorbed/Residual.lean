import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGerm
import Hypostructure.Graph.Strategy.ColdCorridorRows.AbsorbedGermFanEnvelope
import Hypostructure.Graph.Strategy.ColdCorridorRows.CanonicalReplacement
import Hypostructure.Graph.Strategy.ColdCorridorRows.ColdFamilyClosure
import Hypostructure.Graph.Strategy.ColdCorridorRows.GermTrichotomy
import Hypostructure.Graph.Strategy.ColdCorridorRows.NeutralTerminal
import Hypostructure.Graph.Strategy.ColdCorridorRows.TwoStrand
import HypostructureErdos64EG.Assembly.Absorbed.Boundary
import HypostructureErdos64EG.Assembly.Absorbed.FanCharge
import HypostructureErdos64EG.Assembly.NearCubic.ColdPass

/-!
# Assembly: Absorbed / Residual

Nodes `[175]`--`[177]`, `lem:absorbed-germ-fan-data`, on the absorbed-configuration
residual `[174]`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Every key committed from the `[177]` entry on: the Type B entry and the
Type B / route-8 charge tail. -/
noncomputable abbrev netChargeFanEntryKeys : FactKeys EGInput.{u} :=
  [K .typeBFanEntry, K .netChargeLocalization,
    K .netChargeNonNegative, K .netChargeNegative, K .negativeSupport,
    K .typeALowSurplus, K .typeBHighSurplus, K .typeABoundedSupport,
    K .typeAReceiverRouting, K .typeASaturatedReceiver,
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
    K .triangularCrossShoulder,
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
    K .typeAExitSevenEnvelope,
    K .route8GlobalSqueeze]

/-- Every key committed from `[177]` on: the fan data, its Type B entry, and the
Type B / route-8 charge tail. -/
noncomputable abbrev netChargeFanDataKeys : FactKeys EGInput.{u} :=
  K .absorbedGermFanData :: K .typeBAbsorbedHalfEdge ::
    K .typeBAbsorbedHalfEdgeAbsent :: K .typeBAbsorbedCharge ::
      netChargeFanEntryKeys.{u}

/-- **Node `[177]`**: on the `[175]` yes arm (`K .typeBAbsorbedHalfEdge`), the
decorated handoff fan data at the first high centre of `G`'s canonical absorbed
half-edge enters Type B at `[65]`, followed by the common registered charge
tail. -/
-- EG-NODE [177] decorated handoff fan data at the heavy centre \(z\): continue at Type B [65]
noncomputable def selectedAbsorbedFanData
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .typeBAbsorbedHalfEdge) known]
    (fresh : List.Disjoint netChargeFanEntryKeys.{u} known := by key_fresh)
    (chargeFresh : K .typeBAbsorbedCharge ∉ known := by key_fresh) :
    SelectedAbsorbedGermBoundary selected := by
  -- `[177]`: every selected half-edge outside the subcubic candidates is
  -- charged to the Type B ledger at its own pinned absorbed support.
  let charged :=
    (typeBAbsorbedChargeRow (data := spineData)).run history (by key_fresh)
  -- `[177]` → `[65]`: the canonical absorbed half-edge enters Type B.
  let fanEntry :=
    (absorbedGermFanEnvelopeRow (data := spineData)).run charged
      (by key_fresh)
  exact Or.inl <| Assembly.Internal.selectedAbsorbedFanChargeContinuation fanEntry
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by key_fresh)
        (by infer_instance)
        (by key_fresh)
        (unifiedNegativeFresh := by key_fresh)
        (typeAExclusionFresh := by key_fresh)
        (typeBBridgeReductionFresh := by
          key_fresh)
        (piecesClassifiedFresh := by key_fresh)
        (sublinearLedgerFresh := by key_fresh)
        (sublinearResidualFresh := by key_fresh)
        (unifiedDeficitFresh := by key_fresh)
        (quotientFreeFresh := by key_fresh)
        (quotientResidualFresh := by key_fresh)
        (unifiedCensusFresh := by key_fresh)
        (unifiedTrueFresh := by key_fresh)
        (peelingFresh := by key_fresh)
        (stageFailedFresh := by key_fresh)
        (demandLedgerFresh := by key_fresh)
        (demandAbsorptionFresh := by key_fresh)
        (openBoundarySaturatedFresh := by key_fresh)
        (demandUnitCountFresh := by key_fresh)
        (windowBlockersFresh := by key_fresh)
        (windowShadowCycleFresh := by key_fresh)
        (windowShadowExcludedFresh := by key_fresh)
        (demandResidualFresh := by key_fresh)
        (unpaidExitFourFresh := by key_fresh)
        (unifiedVisibleFresh := by key_fresh)
        (unifiedVisibleOverloadFresh := by
          key_fresh)
        (jointBalanceFresh := by key_fresh)
        (unifiedTerminalFresh := by key_fresh)

/-- **Nodes `[175]`--`[177]`, `lem:absorbed-germ-fan-data`.**  `[175]` publishes
the per-half-edge case split and decides whether some selected corridor avoids
the high-degree vertices.  On its yes arm the genuine (F5) configurations
`[176]` run `[154]`--`[157]`: G1 closes at `[155]`; the G2 test of `[154]`
splits the no-G1 arm: G2 `[156]` is recorded by the trichotomy and the
same-interface table (`K .coldBranchClosed`, `[187]`), and on the silent arm the
neutral configuration `[163]` is split: its genuine second strand
closes at `[167]`/`[168]` and whose canonical replacement is published with
`Q = E` (`[165]`--`[166]`); the case-(ii) complement of a mixed family then
continues at `[177]`.  On its no arm every selected corridor is `[177]` fan
data. -/
-- EG-NODE [175] selected corridor meets a high-degree vertex?
-- EG-NODE [176] graph-realized (F5) configuration: closed by [154]--[157], [165]--[168]
noncomputable def selectedAbsorbedGermResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (fresh : List.Disjoint
      (K .absorbedGermSplit :: K .coldPositiveGerm :: K .coldNoPositiveGerm ::
        K .coldGermFamilyPositive :: K .coldGermSomeRealizing ::
        K .coldGermNoneRealizing :: K .coldGermSomeDistinguishing ::
        K .coldGermNoneDistinguishing :: K .coldNeutralEqualLengthTerminal ::
        K .coldGermRealized :: K .coldGermDistinguished :: K .coldGermSilent ::
        K .coldGermRouted :: K .coldSameInterfaceTable :: K .coldBranchClosed ::
        K .coldCanonicalNeutralConfiguration :: K .coldGenuineSecondStrand ::
        K .coldCanonicalReplacementSwap :: K .coldCanonicalReplacementTrivial ::
        K .coldTwoStrandSurvivor :: K .coldWindowStubStructure ::
        K .coldSymmetricPairExcluded :: netChargeFanDataKeys.{u}) known := by
        key_fresh) :
    SelectedAbsorbedGermBoundary selected := by
  let split :=
    (absorbedGermSplitRow (data := spineData)).run history (by key_fresh)
  match absorbedGermDichotomy (data := spineData) split
      (by key_fresh) (by key_fresh) with
  | .right noPositiveHistory =>
      let fanData :=
        (absorbedGermFanDataRow (data := spineData)).run noPositiveHistory
          (by key_fresh)
      -- `[175]` read at `[177]`: does some selected corridor meet a
      -- high-degree vertex?
      match typeBAbsorbedHalfEdgeDichotomy (data := spineData) fanData
          (by key_fresh) (by key_fresh) with
      | .left outsideHistory => exact selectedAbsorbedFanData outsideHistory
      | .right subcubicHistory =>
          -- `[176]`: every selected corridor is subcubic, so every selected
          -- configuration is a genuine (F5) configuration (here the family
          -- is empty: no candidate and no outside half-edge); it is closed by
          -- `[154]`--`[157]` (G1 is vacuous) with the local cold-terminal
          -- exclusion retained at `[187]`.
          let closedHistory := nearCubicColdTable subcubicHistory
          exact Or.inr (closedHistory.get (K .coldBranchClosed)).down
  | .left positiveHistory =>
      let positiveFamily :=
        (absorbedGermFamilyPositiveRow (data := spineData)).run positiveHistory
          (by key_fresh)
      let unhit := nearCubicColdNoHit positiveFamily
      -- `[154]`, second test (G2): a hit-distinguished configuration of the
      -- extracted family is the `[156]` outcome, recorded by the trichotomy
      -- and the same-interface table (`K .coldBranchClosed`, retained at
      -- `[187]`); the silent arm `[157]` carries the neutral configuration,
      -- which is split below.
      match coldGermDistinctionDichotomy (data := spineData) unhit
          (by key_fresh) (by key_fresh) with
      | .left distinguishedHistory =>
          exact Or.inr
            ((nearCubicColdTable distinguishedHistory).get
              (K .coldBranchClosed)).down
      | .right silentHistory =>
          let neutralConfiguration :=
            (neutralEqualLengthTerminalRow (data := spineData)).run silentHistory
              (by key_fresh)
          let closed := nearCubicColdTable neutralConfiguration
          match neutralGermSymmetryDichotomy (data := spineData) closed
              (by key_fresh) (by key_fresh) with
          | .right genuineHistory =>
              let survivor :=
                (twoStrandSurvivorRow (data := spineData)).run genuineHistory
                  (by key_fresh)
              let stubbed :=
                (coldWindowStubStructureRow (data := spineData)).run survivor
                  (by key_fresh)
              exact ((symmetricPairEndpointExclusionRow
                (data := spineData)).runAndCloseIncompatible stubbed
                  (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded)
                  (by key_fresh) (by key_fresh)).elimClosed (by infer_instance) |>.elim
          | .left canonicalHistory =>
              let swapped :=
                (canonicalReplacementSwapRow (data := spineData)).run
                  canonicalHistory (by key_fresh)
              let trivial :=
                (canonicalReplacementTrivialRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  swapped (by key_fresh)
              let fanData :=
                (absorbedGermFanDataRow (data := spineData)).run trivial
                  (by key_fresh)
              -- `[175]` read at `[177]`: does some selected corridor meet a
              -- high-degree vertex (the case-(ii) complement of the family)?
              match typeBAbsorbedHalfEdgeDichotomy (data := spineData) fanData
                  (by key_fresh) (by key_fresh) with
              | .left outsideHistory => exact selectedAbsorbedFanData outsideHistory
              | .right subcubicHistory =>
                  -- `[176]`: every selected corridor is a genuine (F5)
                  -- configuration, closed above by `[154]`--`[157]` and
                  -- `[165]`--`[168]`; the local cold-terminal exclusion is
                  -- retained at `[187]`.
                  exact Or.inr (subcubicHistory.get (K .coldBranchClosed)).down

end HypostructureErdos64EG
