import HypostructureErdos64EG.Assembly.Entry
import HypostructureErdos64EG.Assembly.Surplus.Strict.Independent
import HypostructureErdos64EG.Assembly.Surplus.Strict.Dependent

/-! Strict-surplus dispatcher. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

-- EG-NODE [125] sparse-load survivor: after \(P_{13}\) label algebra and sparse exits
set_option maxHeartbeats 1000000 in
noncomputable def selectedStrictSurplusBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor,
        K .paperBudgetBound, K .paperBudgetCertifies, K .pairCodeConfiguration,
        K .canonicalTokenCount,
        K .canonicalBlockedFreePartition, K .canonicalLedgerDeficit,
        K .pairCountDeficit, K .canonicalCertificationCriterion,
        K .canonicalOverloadOfFits, K .canonicalFreeExcessOfCapped,
        K .canonicalCapacityExplicit, K .highDegreePositive,
        K .highDegreeSurplusCapacity, K .orderAboveScaleSquare,
        K .sixVertexExtremalEnvelope, K .edgeSurplusIdentity,
        K .ceilSqrtAboveScale, K .baselineSpineDemand, K .sparseUpperEnvelope,
        K .surplusAbove, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
        K .admissibleQuotientsLabelInjective, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .surplusDartIdentity, K .highDegreeCountBound, K .highCentreSplitForced, K .tightEndpoint, K .slackIndependent,
        K .singleBoundaryShape, K .noProperBaseline, K .sameVertexSwitchForcedPath, K .returnAvoidance,
        K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
        K .twoSwitchForcedPath, K .crossSwitchFamily, K .minDegreeBaseline, K .bridgeless, K .cubicBaseline, K .packingOrderBound,
        K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    StrictSurplusBoundaryResult selected := by
  -- The enclosing `[20]` decision has already selected the survivor arm;
  -- its literal ledger is node `[125]`, which enters `[126]`--`[128]`.
  let activated := selectedSparseSurplusActivation history
  -- EG-NODE [129] full active family and baseline: \(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)
  -- `[129]`'s baseline spine demand `K .baselineSpineDemand` is on the ledger
  -- since the top of the strict arm of `[19]` (`sparseExitBaselineSpineDemandRow`,
  -- which reads only entry facts and `K .surplusAbove`), so it is not
  -- published again here.
  -- EG-NODE [130] canonical pair split: blocker-free?
  match pairResponseIndependenceDichotomy (data := spineData) activated
      (by key_fresh) (by key_fresh) with
  | .left independentHistory =>
      exact Assembly.Internal.strictSurplusIndependent independentHistory
  | .right dependentHistory =>
      exact Assembly.Internal.strictSurplusDependent dependentHistory

end HypostructureErdos64EG
