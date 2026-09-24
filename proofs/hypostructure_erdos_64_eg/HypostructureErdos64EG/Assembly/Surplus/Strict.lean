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

set_option maxHeartbeats 1000000 in
noncomputable def selectedStrictSurplusBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    StrictSurplusBoundaryResult selected := by
  -- The enclosing `[20]` decision has already selected the survivor arm.
  -- `[125]` is the exact identity edge prescribed by the diagram; only that
  -- same ledger can enter `[126]`--`[128]` and `[129]`.
  let node125 := selectedSparseSurplusSurvivorNode125 history
  let activated := selectedSparseSurplusActivation node125
  let baseline := selectedBaselineSpineDemand activated
  match selectedPairResponseIndependenceDichotomy baseline with
  | .left independentHistory =>
      exact Assembly.Internal.strictSurplusIndependent independentHistory
  | .right dependentHistory =>
      exact Assembly.Internal.strictSurplusDependent dependentHistory

end HypostructureErdos64EG
