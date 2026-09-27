import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FreePairCoupledExcess
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FreePairEntropy
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairOverlapFirstFailure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FibrePressure
import HypostructureErdos64EG.Assembly.Surplus.Local

/-! A strict-surplus branch, with the complete original ledger. -/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

set_option maxHeartbeats 1000000 in
noncomputable def Assembly.Internal.strictSurplusIndependent
    {selected : EGInput.{u}}
    (independentHistory : ExactLedger EGInput.{u} selected
      [K .independentPairFamily, K .baselineSpineDemand, K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .spinePresentationLaws, K .cubicBaseline,
        K .selection]) :
    StrictSurplusBoundaryResult selected := by
  -- `[131]` first commits the manuscript's named arithmetic and
  -- dependence prefix to this literal residual; the entropy decision below
  -- reads `K .incrementalSkeletonRoom` rather than recomputing it.
  -- EG-NODE [131] free-pair entropy sandwich: \(|\Pi_{\rm free}|\le E_{\rm spine}+(\sigma/2+1)\log_2 n\)
  let mixed :=
    (mixedSparseSpineDependenceRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      independentHistory (by key_fresh)
  let cubic :=
    (exactCubicBaselineBudgetRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      mixed (by key_fresh)
  let room :=
    (incrementalSkeletonRoomRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by key_fresh)
  let dominated :=
    (skeletonDominatesRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      room (by key_fresh)
  match freePairEntropyDichotomy (data := spineData) dominated
      (by key_fresh) (by key_fresh) with
  | .left sandwichHistory =>
      -- `[131]` count holds → `[137]`: coupled excess `D_all > 0?`.  Both
      -- arms reach node `[138]`'s `σ(G) ≤ C_sp ⌈√n⌉`, which closes against
      -- node `[19]`.
      match coupledExcessDichotomy (data := spineData) sandwichHistory
          (by key_fresh) (by key_fresh) with
      | .left nearCubicHistory =>
          let closedHistory :=
            (freePairSurplusEstimateRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible
                nearCubicHistory (K .surplusAbove) (K .spineSurplusEstimate)
                (by key_fresh) (by key_fresh)
          exact (closedHistory.elimClosed (by infer_instance)).elim
      | .right overloadHistory =>
          let closedHistory :=
            (freePairSurplusEstimateRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible
                overloadHistory (K .surplusAbove) (K .spineSurplusEstimate)
                (by key_fresh) (by key_fresh)
          exact (closedHistory.elimClosed (by infer_instance)).elim
  | .right failsHistory =>
      -- `[131]` count fails: its first failed pair extension enters `[178]`.
      let unrealizedHistory :=
        (freePairCodeUnrealizedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failsHistory (by key_fresh)
      let firstFailure :=
        (freePairOverlapFirstFailureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unrealizedHistory (by key_fresh)
      exact selectedPairCodeChain firstFailure

end HypostructureErdos64EG
