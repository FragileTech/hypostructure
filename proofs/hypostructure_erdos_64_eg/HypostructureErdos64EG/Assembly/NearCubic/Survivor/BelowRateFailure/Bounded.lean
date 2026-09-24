import Hypostructure.Graph.Strategy.ColdCorridorRows
import Hypostructure.Graph.Strategy.EntropyClosure
import HypostructureErdos64EG.Assembly.Cold.Barrier
import HypostructureErdos64EG.Assembly.Cold.Entropy
import HypostructureErdos64EG.Assembly.NearCubic.Boundary
import HypostructureErdos64EG.Assembly.NearCubic.Local
import HypostructureErdos64EG.Assembly.NearCubic.Replacement

/-! A survivor sub-branch with its complete incoming ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 8000000 in
noncomputable def Assembly.Internal.nearCubicBelowRateFailureBounded
    {selected : EGInput.{u}}
    (boundedHistory : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
       K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .route8RateFails,
       K .denseDeficiencyBelow, K .hotColdPartition, K .densePackingOverflow,
       K .windowPackageUnrealized, K .skeletonDominates, K .windowPackageSeparated,
       K .barrierEnumeration, K .sparseSurplusSurvivor, K .surplusAtOrBelow, K .localAlgebra,
       K .maximalPacking, K .uncompressible, K .replacementExclusion,
       K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
       K .tightEndpoint, K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
       K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
       K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  -- `[162]` has now been reached correctly.  Its bounded
  -- `[153]` arm returns through `[24]`; the existing exact
  -- finite route-rate decision remains the first downstream
  -- obligation if that stronger rate still fails.
  let density :=
    (densityBudgetRow (data := spineData)).run boundedHistory
      (by simp [K_eq_iff])
  exact Or.inr (Or.inl
    (density.get (K .route8RateFails)).down)

end HypostructureErdos64EG
