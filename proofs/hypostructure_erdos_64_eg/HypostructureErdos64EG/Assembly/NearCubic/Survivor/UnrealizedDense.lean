import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseBelow

/-! A branch of the near-cubic survivor, retaining its full literal ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicUnrealizedDense
    {selected : EGInput.{u}}
    (denseHistory : ExactLedger EGInput.{u} selected
      [K .denseDeficiencyAtOrAbove, K .hotColdPartition, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `τ(θ) ≥ 1/4`, the dense residual: `[22]`'s live-hot cap decision and the
  -- cold branch `[145]`--`[157]` on it.
  match selectedBarrierDichotomy denseHistory
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .right overflowHistory =>
      exact (selectedBarrierOverflowCloses overflowHistory
        (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim
  | .left capHistory =>
  -- `[145]`'s split is already on this ledger (run before the deficiency test).
  match coldRoute8Dichotomy (data := spineData) capHistory
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left belowHistory =>
      exact Assembly.Internal.nearCubicDenseBelow belowHistory
  | .right atOrAboveHistory =>
      exact Assembly.Internal.nearCubicDenseAtOrAbove atOrAboveHistory

end HypostructureErdos64EG
