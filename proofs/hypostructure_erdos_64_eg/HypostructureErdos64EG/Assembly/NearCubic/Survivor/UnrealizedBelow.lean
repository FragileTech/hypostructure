import Hypostructure.Graph.Strategy.SpineRows.Route8RateDichotomy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRate
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.BelowRateFailure

/-! A branch of the near-cubic survivor, retaining its full literal ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicUnrealizedBelow
    {selected : EGInput.{u}}
    (belowHistory : ExactLedger EGInput.{u} selected
      [K .denseDeficiencyBelow, K .hotColdPartition, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `τ(θ) < 1/4`: the net-charge collision, `[25]`--`[62]` and the Type A/B
  -- branches, with `[56]` read from the decision.  The route-8 rate
  -- `τ < 3/13` (`[120]`) is not decided by `τ < 1/4`; it is decided here
  -- (`route8RateDichotomy`), and its failure — the manuscript's delicate
  -- density interval `3/13 ≤ τ < 1/4`, row 2 of `tab:cold-branch-ledger`,
  -- which the manuscript sends to the hot/cold pass — is the next producer.
  match route8RateDichotomy (data := spineData) belowHistory
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .right rateFails =>
      exact Assembly.Internal.nearCubicBelowRateFailure rateFails
  | .left belowHistory =>
      exact Assembly.Internal.nearCubicBelowRate belowHistory

end HypostructureErdos64EG
