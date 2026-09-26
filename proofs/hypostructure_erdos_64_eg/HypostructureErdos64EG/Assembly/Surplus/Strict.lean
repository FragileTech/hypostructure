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
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking,
        K .windowPresent, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    StrictSurplusBoundaryResult selected := by
  -- The enclosing `[20]` decision has already selected the survivor arm;
  -- its literal ledger is node `[125]`, which enters `[126]`--`[128]`.
  let activated := selectedSparseSurplusActivation history
  let baseline := selectedBaselineSpineDemand activated
  match selectedPairResponseIndependenceDichotomy baseline with
  | .left independentHistory =>
      exact Assembly.Internal.strictSurplusIndependent independentHistory
  | .right dependentHistory =>
      exact Assembly.Internal.strictSurplusDependent dependentHistory

end HypostructureErdos64EG
