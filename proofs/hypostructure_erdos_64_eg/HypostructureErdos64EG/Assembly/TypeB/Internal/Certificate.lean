import Hypostructure.Graph.Strategy.SpineRows.B2AssignmentDichotomy
import Hypostructure.Graph.Strategy.SpineRows.DirectCycleDichotomy
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

/-- **The common Type B certificate walk `[70]`--`[77]` / `[80]`--`[85]`.**

`[70]` reads the node-`[65]` entry and publishes the fan-safe graph and the
certificate cap at its Type B support.  `[71]`/`[80]` reads the cap and decides
the certificate labelling at that support; its residual arm is charged to the
fan mass `[75]`/`[84]` and then `[76]`/`[85]`.  On the marked arm the direct
fan-window configurations are decided first (their arm closes against the
selection), then the local B1 ledger is published.

* Heavy arm (`degreeFour = none`), `[72]`: B2 disjointness holds?  B2 success
  is the bridge reduction `[74]` and `[76]`; B2 failure is the minimal overlap
  obstruction `[73]`, reflected and charged to the fan mass `[75]`, then `[76]`.
* Degree-four arm (`degreeFour` carries the `[78]` fact), `[81]`: `c ≤ 1`, or `c ≥ 2` with B2?
  The yes arm is `[82]` (the B2 ledger whenever B2 holds, and the bridge
  reduction) and `[85]`; the no arm is `[83]`, reflected and charged to the fan
  mass `[84]`, then `[85]`.

Every open arm continues to the route-8 cores `[77]` on its own ledger. -/
-- EG-NODE [70] fan-safe graph, \(P_{13}\) certificate graph, and certificate-marked cap \(d_G(h)\le8\)
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
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (closureFresh : closed ∉ known := by key_fresh)
    (capFresh : K .fanCertificateCap ∉ known := by key_fresh)
    (markedFresh : K .fanCertificateMarked ∉ known := by key_fresh)
    (residualFresh : K .fanCertificateResidual ∉ known := by key_fresh)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      key_fresh)
    (cycleFresh : K .typeBDirectCycle ∉ known := by key_fresh)
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
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by
      key_fresh)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by
      key_fresh)
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
    (witnessFreeFresh : K .route8UnpaidWitnessFree ∉ known := by key_fresh) :
    SelectedRouteEightBoundary selected := by
  -- `[70]`: the fan-safe graph and the certificate-marked cap.
  let capped := (fanCertificateCapRow (data := spineData)).run history
    (by key_fresh)
  -- `[71]`/`[80]`: certificate labelling present?
  match fanCertificateDichotomy (data := spineData) capped
      (by key_fresh) (by key_fresh) with
  | .right residualHistory =>
      -- `[75]`/`[84]`: every fan-certificate residual centre is charged to the
      -- bridge fan mass; `[76]`/`[85]`: the support is a Type B bridge residual.
      let mass := (fanCertificateResidualMassRow (data := spineData)).run
        residualHistory (by key_fresh)
      let closedMass := (typeBCertificateMassExclusionRow (data := spineData)).run
        mass (by key_fresh)
      exact selectedTypeBRoute8Continuation closedMass
  | .left markedHistory =>
      -- The local fan-window ledger is complete exactly when no direct
      -- configuration occurs; a direct configuration is an accepted cycle.
      match directCycleDichotomy (data := spineData) markedHistory
          (by key_fresh) (by key_fresh) with
      | .left cycleHistory =>
          exact ((closeIncompatible cycleHistory (K .selection)
            (K .typeBDirectCycle) (by key_fresh)).elimClosed
              (by infer_instance)).elim
      | .right freeHistory =>
          -- The local B1 ledger of every marked centre.
          let hybrid := (hybridEntryRow (data := spineData)).run freeHistory
            (by key_fresh)
          cases degreeFour with
          | none =>
              -- `[72]`: B2 disjointness holds?
              match b2AssignmentDichotomy (data := spineData) hybrid
                  (by key_fresh) (by key_fresh) with
              | .left choiceHistory =>
                  -- `[74]`: the B2 refinement and the bridge reduction;
                  -- `[76]`: the negative post-ledger residual.
                  let ledger :=
                    (disjointPostLedgerComponentsRow (data := spineData)).run
                      choiceHistory (by key_fresh)
                  let excluded := (typeBExcludedRow (data := spineData)).run
                    ledger (by key_fresh)
                  let residual :=
                    (typeBExclusionResidualRow (data := spineData)).run
                      excluded (by key_fresh)
                  exact selectedTypeBRoute8Continuation residual
              | .right obstructionHistory =>
                  -- `[73]`: the minimal overlap obstruction and its
                  -- global-to-local reflection; `[75]`: charged to the fan
                  -- mass; `[76]`.
                  let reflected :=
                    (typeBGlobalLocalBridgeRow (data := spineData)).run
                      obstructionHistory (by key_fresh)
                  let mass :=
                    (typeBOverlapObstructionMassRow (data := spineData)).run
                      reflected (by key_fresh)
                  let closedMass :=
                    (typeBObstructionMassExclusionRow (data := spineData)).run
                      mass (by key_fresh)
                  exact selectedTypeBRoute8Continuation closedMass
          | some degreeFourCentres =>
              letI := degreeFourCentres
              -- `[81]`: `c ≤ 1`, or `c ≥ 2` with B2 disjoint ledger?
              match degreeFourLedgerDichotomy (data := spineData) hybrid
                  (by key_fresh) (by key_fresh) with
              | .left ledgerHistory =>
                  -- `[82]`: certificate-closed (`lem:typeB-exclusion` Step 1)
                  -- or B2-paid (the B2 ledger whenever B2 holds, and the
                  -- bridge reduction); `[85]`.
                  let closedHistory :=
                    (typeBDegreeFourClosedRow (data := spineData)).run
                      ledgerHistory (by key_fresh)
                  let ledger :=
                    (degreeFourDisjointLedgerRow (data := spineData)).run
                      closedHistory (by key_fresh)
                  let excluded := (typeBExcludedRow (data := spineData)).run
                    ledger (by key_fresh)
                  let residual :=
                    (typeBExclusionResidualRow (data := spineData)).run
                      excluded (by key_fresh)
                  exact selectedTypeBRoute8Continuation residual
              | .right overlapHistory =>
                  -- `[83]`: `c ≥ 2` and B2 fails, the minimal overlap
                  -- obstruction and its reflection; `[84]`: charged to the fan
                  -- mass; `[85]`.
                  let reflected :=
                    (typeBDegreeFourGlobalLocalBridgeRow (data := spineData)).run
                      overlapHistory (by key_fresh)
                  let mass :=
                    (typeBOverlapObstructionMassRow (data := spineData)).run
                      reflected (by key_fresh)
                  let closedMass :=
                    (typeBObstructionMassExclusionRow (data := spineData)).run
                      mass (by key_fresh)
                  exact selectedTypeBRoute8Continuation closedMass

end HypostructureErdos64EG
