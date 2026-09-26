import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FreePairCoupledExcess
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FreePairEntropy
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairFailureOverlap
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairOverlapFirstFailure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairOverlapSystem
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairPowerOfTwoCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairSystemOutcome
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PressureSpineSurplusEstimate
import HypostructureErdos64EG.Assembly.Surplus.Local
import HypostructureErdos64EG.Assembly.Surplus.Boundary

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
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    StrictSurplusBoundaryResult selected := by
  -- `[131]` first commits the manuscript's named arithmetic and
  -- dependence prefix to this literal residual.  In particular, the
  -- entropy executor below reads `K .incrementalSkeletonRoom`; it does not
  -- recompute that fact, and the other named facts remain in its ancestry.
  let mixed :=
    (mixedSparseSpineDependenceRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      independentHistory (by
        key_fresh)
  let cubic :=
    (exactCubicBaselineBudgetRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      mixed (by
        key_fresh)
  let room :=
    (incrementalSkeletonRoomRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by
        key_fresh)
  let dominated :=
    (skeletonDominatesRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      room (by
        key_fresh)
  -- `[131]`: decide the full-pair realization count on the literal
  -- baseline family read from the ledger.  The realized arm also records
  -- the exact cleared sandwich of `prop:sparse-entropy-sandwich`.
  match freePairEntropyDichotomy (data := spineData) dominated
      (by key_fresh) (by key_fresh) with
  | .left sandwichHistory =>
      -- `[131]` count holds → `[137]`: coupled excess `D_all > 0?`.
      match freePairCoupledExcessDichotomy (data := spineData) sandwichHistory
          (by key_fresh) (by key_fresh) with
      | .left nearCubicHistory =>
          -- `[138]`: `σ(G) ≤ C_sp ⌈√n⌉` against `[19]`.
          let estimate :=
            (pressureSpineSurplusEstimateRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              nearCubicHistory (by key_fresh)
          exact (selectedSpineSurplusEstimateCloses estimate).elim
      | .right overloadHistory =>
          -- `D_all > 0` is empty on the free-pair arm: the `[131]` count gives
          -- `σ(G) ≤ C_sp ⌈√n⌉`, incompatible with `[19]`.
          let closedHistory :=
            (freePairSurplusEstimateRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).runAndCloseIncompatible
                overloadHistory (K .surplusAbove) (K .spineSurplusEstimate)
                (by key_fresh) (by key_fresh)
          exact (closedHistory.elimClosed (by infer_instance)).elim
  | .right unrealizedHistory =>
      -- `[178]`: the residual on which the entropy count of the free-pair
      -- code fails (`K .freePairCodeUnrealized`), carried as its own branch.
      -- Its closure is `lem:pair-count-or-arithmetic`: the failure supplies a
      -- minimal pair overlap obstruction (`lem:pair-failure-overlap`), which
      -- `lem:pair-system-realizability` uncrosses into a scale-spanning serial
      -- demand system `[179]` (or closes by a dyadic cycle / sparse exits
      -- (b),(c) / Type B fan data), and `lem:pair-system-increment-arithmetic`
      -- `[180]` closes that system: `SerialSystem.Spectrum.exists_pow_realized`
      -- gives a dyadic cycle against `K .selection`, or the residue map is a
      -- periodic carrier routed to a sparse exit (refuted by
      -- `K .sparseSurplusSurvivor`) or to Type B.  The next producer is the
      -- row publishing the serial spectrum of `[179]` on this residual (the
      -- uncrossing of `lem:pair-system-realizability`).
      let firstFailure :=
        (freePairOverlapFirstFailureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unrealizedHistory (by
            key_fresh)
      let overlapSystem :=
        (pairOverlapSystemRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstFailure (by
            key_fresh)
      match pairConditionalFactorizationDichotomy (data := spineData)
          overlapSystem (by key_fresh) (by key_fresh) with
      | .right residualHistory =>
          let openResidual := residualHistory.get
            (K .pairConditionalFactorizationResidual)
          change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
          exact Sum.inr (Sum.inr openResidual)
      | .left factorizationHistory =>
          let overlapFailure :=
            (pairFailureOverlapRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run factorizationHistory
                (by key_fresh)
          let demandReturns :=
            (pairDemandReturnsRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run overlapFailure
                (by key_fresh)
          match pairSystemRealizabilityDichotomy (data := spineData)
              demandReturns (by key_fresh) (by key_fresh) with
          | .right residualHistory =>
              let openResidual := residualHistory.get
                (K .pairConditionalFactorizationResidual)
              change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
              exact Sum.inr (Sum.inr openResidual)
          | .left coveredHistory =>
              match pairSystemOutcomeDichotomy (data := spineData)
                  coveredHistory (by key_fresh)
                    (by key_fresh) with
              | .left earlyHistory =>
                  let typeBHistory :=
                    (pairSystemEarlyTypeBEntryRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run earlyHistory
                        (by key_fresh)
                  let typeBEntry := typeBHistory.get (K .typeBFanEntry)
                  change ((K .typeBFanEntry).At selected) at typeBEntry
                  let bridgelessrowStep :=
                    (bridgelessRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      typeBHistory (by key_fresh)
                  let remaindernormalizationrowStep :=
                    (remainderNormalizationRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      bridgelessrowStep (by key_fresh)
                  let remainderrelabelingentropyrowStep :=
                    (remainderRelabelingEntropyRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      remaindernormalizationrowStep (by key_fresh)
                  exact Sum.inr (Sum.inl ⟨⟨
                    Or.inl (remainderrelabelingentropyrowStep.get
                      (K .pairSystemEarlyOutcome)).down,
                    (remainderrelabelingentropyrowStep.get
                      (K .typeBFanEntry)).down,
                    (remainderrelabelingentropyrowStep.get (K .surplusAbove)).down,
                    (remainderrelabelingentropyrowStep.get (K .sparseSurplusSurvivor)).down⟩⟩)
              | .right serialHistory =>
                  match pairIncrementCoveredDichotomy (data := spineData)
                      serialHistory (by key_fresh)
                        (by key_fresh) with
                  | .right residualHistory =>
                      let openResidual := residualHistory.get
                        (K .pairConditionalFactorizationResidual)
                      change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
                      exact Sum.inr (Sum.inr openResidual)
                  | .left incrementHistory =>
                      match pairIncrementOutcomeDichotomy (data := spineData)
                          incrementHistory (by key_fresh)
                            (by key_fresh) with
                      | .left earlyHistory =>
                          let typeBHistory :=
                            (pairIncrementEarlyTypeBEntryRow
                              (BranchState := BranchState)
                              (Presentation :=
                                Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).run earlyHistory
                                (by key_fresh)
                          let typeBEntry :=
                            typeBHistory.get (K .typeBFanEntry)
                          change ((K .typeBFanEntry).At selected) at typeBEntry
                          let bridgelessrowStep :=
                            (bridgelessRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              typeBHistory (by key_fresh)
                          let remaindernormalizationrowStep :=
                            (remainderNormalizationRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              bridgelessrowStep (by key_fresh)
                          let remainderrelabelingentropyrowStep :=
                            (remainderRelabelingEntropyRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              remaindernormalizationrowStep (by key_fresh)
                          exact Sum.inr (Sum.inl ⟨⟨
                            Or.inr (remainderrelabelingentropyrowStep.get
                              (K .pairIncrementEarlyOutcome)).down,
                            (remainderrelabelingentropyrowStep.get
                              (K .typeBFanEntry)).down,
                    (remainderrelabelingentropyrowStep.get (K .surplusAbove)).down,
                    (remainderrelabelingentropyrowStep.get (K .sparseSurplusSurvivor)).down⟩⟩)
                      | .right arithmeticHistory =>
                          let closedHistory :=
                            (pairPowerOfTwoCycleRow
                              (BranchState := BranchState)
                              (Presentation :=
                                Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).runAndCloseIncompatible
                                arithmeticHistory (K .selection)
                                (K .pairPowerOfTwoCycle)
                                (by key_fresh) (by key_fresh)
                          exact (closedHistory.elimClosed (by infer_instance)).elim

end HypostructureErdos64EG
