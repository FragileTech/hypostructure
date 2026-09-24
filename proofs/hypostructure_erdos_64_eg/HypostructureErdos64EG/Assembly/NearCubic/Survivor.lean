import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.Realized
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.Unrealized

/-! The near-cubic survivor dispatcher. Branch proofs compile independently. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def selectedNearCubicSurvivorBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let dominated := selectedNearCubicNode21 history
  match selectedWindowPackageRealizationDichotomy dominated with
  | .right unrealizedHistory =>
      exact Assembly.Internal.nearCubicUnrealized unrealizedHistory
  | .left enumerated =>
      exact Assembly.Internal.nearCubicRealized enumerated

end HypostructureErdos64EG
