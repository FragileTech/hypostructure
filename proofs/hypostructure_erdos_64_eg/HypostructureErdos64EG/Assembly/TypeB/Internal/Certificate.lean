import Hypostructure.Graph.Strategy.SpineRows.B2AssignmentDichotomy
import Hypostructure.Graph.Strategy.SpineRows.TypeBDirectCycleFree
import Hypostructure.Graph.Strategy.SpineRows.DisjointPostLedgerComponents
import Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap
import Hypostructure.Graph.Strategy.SpineRows.FanCertificateDichotomy
import Hypostructure.Graph.Strategy.SpineRows.FanCertificateResidualMass
import Hypostructure.Graph.Strategy.SpineRows.HybridEntry
import Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion
import Hypostructure.Graph.Strategy.SpineRows.TypeBGlobalLocalBridge
import Hypostructure.Graph.Strategy.SpineRows.TypeBOverlapObstructionMass
import HypostructureErdos64EG.Assembly.RouteEight.TypeBContinuation

/-!
# Assembly: TypeB / Internal / Certificate

Nodes `[70]`--`[77]` and `[80]`--`[85]` at the Type B support of the selected
counterexample.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
/-- **The common Type B certificate walk `[71]`--`[77]` / `[80]`--`[85]`.**

`[70]` has published the fan-safe graph and the certificate cap at the Type B
support of the `[69]`/`[79]` arm fact.  `[71]`/`[80]` reads the cap and decides
G's canonical certificate labelling at that support; its residual arm is
charged to the fan mass `[75]`/`[84]` and then `[76]`/`[85]`.  On the marked arm
the local fan-window ledger is completed: the direct fan-window cycles are
excluded (a fact, `lem:typeB-direct-fan-window-cycles`) and the B1 ledger is
published.

* Heavy arm (`degreeFour = none`), `[72]`: B2 disjointness holds?  B2 success
  is the bridge reduction `[74]` and `[76]`; B2 failure is the minimal overlap
  obstruction `[73]`, reflected and charged to the fan mass `[75]`, then `[76]`.
* Degree-four arm (`degreeFour` carries the `[78]` fact), `[81]`: `c ≤ 1`, or
  `c ≥ 2` with B2?  The yes arm is `[82]` (certificate-closed or B2-paid) and
  `[85]`; the no arm is `[83]`, reflected and charged to the fan mass `[84]`,
  then `[85]`.

Every arm enters the route-8 cores `[77]` through the Type B entry, which reads
the `[76]`/`[85]` fact on its own ledger. -/
-- EG-NODE [71] certificate labelling present?
-- EG-NODE [72] local fan-window ledger complete; B2 disjointness holds?
-- EG-NODE [73] B2 disjointness fails: minimal Type B overlap obstruction
-- EG-NODE [74] B2 holds: bridge reduction gives \(\No(X)\ge0\) outside route 8
-- EG-NODE [75] bridge fan-mass: fan-certificate centers and B2 failures charged to assigned surplus
-- EG-NODE [76] Type B cannot carry the linear deficit outside two-support route 8
-- EG-NODE [80] certificate labelling present?
-- EG-NODE [81] \(c\le1\), or \(c\ge2\) with B2 disjoint ledger?
-- EG-NODE [82] yes: certificate-closed or B2-paid; \(\No(X)\ge0\) outside route 8
-- EG-NODE [83] no: \(c\ge2\) and B2 fails; minimal Type B overlap obstruction
-- EG-NODE [84] fan-mass route: certificate failures and B2 failures charged to assigned surplus
-- EG-NODE [85] degree-\(4\) Type B cannot carry linear deficit outside route 8 once the fan-mass residual is sublinear
noncomputable def Assembly.Internal.selectedTypeBCertificateContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (degreeFour : Option (FactKeys.Has (K .typeBFanDegreeFourCentres) known))
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (closureFresh : closed ∉ known := by key_fresh)
    (markedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (residualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      key_fresh)
    (route8EntryFresh : K .typeBRoute8Entry ∉ known := by key_fresh)
    (freeFresh : K .typeBDirectCycleFree ∉ known := by key_fresh)
    (hybridFresh : K .typeBHybridEntry ∉ known := by key_fresh)
    (choiceFresh : K .typeBB2Choice ∉ known := by key_fresh)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by key_fresh)
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by key_fresh)
    (excludedFresh : K .typeBExcluded ∉ known := by key_fresh)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by key_fresh)
    (degreeFourLedgerFresh : K .typeBDegreeFourLedger ∉ known := by key_fresh)
    (degreeFourOverlapFresh : K .typeBDegreeFourOverlap ∉ known := by key_fresh)
    (degreeFourClosedFresh : K .typeBDegreeFourClosed ∉ known := by key_fresh)
    (globalLocalBridgeFresh : K .typeBGlobalLocalBridge ∉ known := by
      key_fresh)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      key_fresh)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by key_fresh)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by key_fresh)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by key_fresh)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by key_fresh)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      key_fresh)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      key_fresh)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by key_fresh)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      key_fresh)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by key_fresh)
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by key_fresh)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      key_fresh)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      key_fresh)
    (extractedCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      key_fresh)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      key_fresh)
    (peelingFresh : K .route8PeelingDescent ∉ known := by key_fresh)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by key_fresh)
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by key_fresh)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      key_fresh)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      key_fresh)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by key_fresh)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by key_fresh)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      key_fresh)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      key_fresh)
    (demandResidualFresh : K .route8StageRate ∉ known := by
      key_fresh)
    (unpaidExitFourFresh : K .route8UnpaidExitFourResidual ∉ known := by
      key_fresh)
    (unifiedVisibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      key_fresh)
    (unifiedVisibleOverloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      key_fresh)
    (jointBalanceFresh : K .route8JointBalance ∉ known := by key_fresh)
    (unifiedTerminalFresh : K .route8UnifiedTwoCarrierExit ∉ known := by key_fresh)
    (unpaidTwoFresh : K .route8UnpaidTwoCarrier ∉ known := by key_fresh)
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh)
    (burdenFresh : K .route8BasinBurden ∉ known := by key_fresh)
    (carrierCoreFresh : K .route8CarrierCore ∉ known := by key_fresh)
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .sameCenterOpenPortCompatibility) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .triangularPortReturn) known]
    [FactKeys.Has (K .triangularShoulderCompletion) known]
    [FactKeys.Has (K .typeBAbsorbedCharge) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known] :
    SelectedRouteEightBoundary selected := by
  -- `[71]`/`[80]`: certificate labelling present?
  match fanCertificateDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .right residualHistory =>
      -- `[75]`/`[84]`: the fan-certificate residual support is charged to its
      -- assigned surplus; `[76]`/`[85]`: B2 fails there; `[77]`.
      let mass := (fanCertificateResidualMassRow (data := spineData)).run
        residualHistory (by key_fresh)
      let closedMass := (typeBCertificateMassExclusionRow (data := spineData)).run
        mass (by key_fresh)
      exact selectedTypeBRoute8Entry closedMass
  | .left markedHistory =>
      -- The local fan-window ledger: the direct fan-window cycles are excluded
      -- at every assigned centre, and the local B1 ledger is published.
      let free := (typeBDirectCycleFreeRow (data := spineData)).run markedHistory
        (by key_fresh)
      let hybrid := (hybridEntryRow (data := spineData)).run free
        (by key_fresh)
      cases degreeFour with
      | none =>
          -- `[72]`: local fan-window ledger complete; B2 disjointness holds?
          match b2AssignmentDichotomy (data := spineData) hybrid
              (by key_fresh) (by key_fresh) with
          | .left choiceHistory =>
              -- `[74]`: the B2-paid ledger and the bridge reduction; `[76]`:
              -- the remaining core carries the whole deficit; `[77]`.
              let ledger :=
                (disjointPostLedgerComponentsRow (data := spineData)).run
                  choiceHistory (by key_fresh)
              let excluded := (typeBExcludedRow (data := spineData)).run
                ledger (by key_fresh)
              let residual :=
                (typeBExclusionResidualRow (data := spineData)).run
                  excluded (by key_fresh)
              exact selectedTypeBRoute8Entry residual
          | .right obstructionHistory =>
              -- `[73]`: the minimal overlap obstruction and its
              -- global-to-local reflection; `[75]`: charged to the fan
              -- mass; `[76]`; `[77]`.
              let reflected :=
                (typeBGlobalLocalBridgeRow (data := spineData)).run
                  obstructionHistory (by key_fresh)
              let mass :=
                (typeBOverlapObstructionMassRow (data := spineData)).run
                  reflected (by key_fresh)
              let closedMass :=
                (typeBObstructionMassExclusionRow (data := spineData)).run
                  mass (by key_fresh)
              exact selectedTypeBRoute8Entry closedMass
      | some degreeFourCentres =>
          letI := degreeFourCentres
          -- `[81]`: `c ≤ 1`, or `c ≥ 2` with B2 disjoint ledger?
          match degreeFourLedgerDichotomy (data := spineData) hybrid
              (by key_fresh) (by key_fresh) with
          | .left ledgerHistory =>
              -- `[82]`: certificate-closed (`lem:typeB-exclusion` Step 1) or
              -- B2-paid (the bridge reduction); `[85]`; `[77]`.
              let closedHistory :=
                (typeBDegreeFourClosedRow (data := spineData)).run
                  ledgerHistory (by key_fresh)
              let residual :=
                (typeBDegreeFourExclusionResidualRow (data := spineData)).run
                  closedHistory (by key_fresh)
              exact selectedTypeBRoute8Entry residual
          | .right overlapHistory =>
              -- `[83]`: `c ≥ 2` and B2 fails, the minimal overlap
              -- obstruction and its reflection; `[84]`: charged to the fan
              -- mass; `[85]`; `[77]`.
              let reflected :=
                (typeBDegreeFourGlobalLocalBridgeRow (data := spineData)).run
                  overlapHistory (by key_fresh)
              let mass :=
                (typeBOverlapObstructionMassRow (data := spineData)).run
                  reflected (by key_fresh)
              let closedMass :=
                (typeBObstructionMassExclusionRow (data := spineData)).run
                  mass (by key_fresh)
              exact selectedTypeBRoute8Entry closedMass

end HypostructureErdos64EG
