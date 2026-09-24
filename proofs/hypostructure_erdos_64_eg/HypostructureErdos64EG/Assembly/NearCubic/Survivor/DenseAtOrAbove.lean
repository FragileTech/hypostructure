import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.Bounded
import HypostructureErdos64EG.Assembly.NearCubic.Survivor.DenseAtOrAbove.Linear

/-! Survivor branch dispatcher; terminal proofs compile separately. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicDenseAtOrAbove
    {selected : EGInput.{u}}
    (atOrAboveHistory : ExactLedger EGInput.{u} selected
      [K .coldRoute8AtOrAbove, K .barrierCap, K .denseDeficiencyAtOrAbove, K .hotColdPartition,
       K .densePackingOverflow, K .windowPackageUnrealized, K .skeletonDominates,
       K .windowPackageSeparated, K .barrierEnumeration, K .sparseSurplusSurvivor,
       K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .uncompressible,
       K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres,
       K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
       K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap,
       K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  match coldHotEntropyDichotomy (data := spineData) atOrAboveHistory
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left overflowHistory =>
      exact (selectedColdHotEntropyCloses overflowHistory).elim
  | .right hotCapHistory =>
  let mass :=
    (coldMassRow (data := spineData)).run hotCapHistory (by simp [K_eq_iff])
  let cubic :=
    (coldAmbientCubicRow (data := spineData)).run mass (by simp [K_eq_iff])
  let stubs :=
    (coldStubExcessRow (data := spineData)).run cubic (by simp [K_eq_iff])
  match coldMassDichotomy (data := spineData) stubs
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left linearHistory =>
      exact Assembly.Internal.nearCubicDenseAtOrAboveLinear linearHistory
  | .right boundedHistory =>
      exact Assembly.Internal.nearCubicDenseAtOrAboveBounded boundedHistory

end HypostructureErdos64EG
