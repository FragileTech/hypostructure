import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import HypostructureErdos64EG.Assembly.Surplus.Local
import HypostructureErdos64EG.Assembly.Surplus.TypeBContinuation

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
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
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
        simp [mixedSparseSpineDependenceRow, K_eq_iff])
  let cubic :=
    (exactCubicBaselineBudgetRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      mixed (by
        simp [exactCubicBaselineBudgetRow,
          mixedSparseSpineDependenceRow, K_eq_iff])
  let room :=
    (incrementalSkeletonRoomRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by
        simp [incrementalSkeletonRoomRow, exactCubicBaselineBudgetRow,
          mixedSparseSpineDependenceRow, K_eq_iff])
  let dominated :=
    (skeletonDominatesRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      room (by
        simp [skeletonDominatesRow, incrementalSkeletonRoomRow,
          exactCubicBaselineBudgetRow, mixedSparseSpineDependenceRow,
          K_eq_iff])
  -- `[131]`: decide the full-pair realization count on the literal
  -- baseline family read from the ledger.  The realized arm also records
  -- the exact cleared sandwich of `prop:sparse-entropy-sandwich`.
  match freePairEntropyDichotomy (data := spineData) dominated
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left sandwichHistory =>
      -- `[131]` → `[137]` (no blocked pairs, `D_all = 0`) → `[138]`:
      -- `cor:spine-lower-bound-surplus-estimates`, `σ(G) ≤ C_sp ⌈√n⌉`,
      -- against node `[19]`'s strict lower bound.
      let estimate :=
        (freePairSurplusEstimateRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sandwichHistory (by simp [K_eq_iff])
      exact (selectedSpineSurplusEstimateCloses estimate).elim
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
            simp [freePairOverlapFirstFailureRow, K_eq_iff])
      let overlapSystem :=
        (pairOverlapSystemRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstFailure (by
            simp [pairOverlapSystemRow, freePairOverlapFirstFailureRow,
              K_eq_iff])
      match pairConditionalFactorizationDichotomy (data := spineData)
          overlapSystem (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
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
                (by simp [K_eq_iff])
          let demandReturns :=
            (pairDemandReturnsRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run overlapFailure
                (by simp [K_eq_iff])
          match pairSystemRealizabilityDichotomy (data := spineData)
              demandReturns (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .right residualHistory =>
              let openResidual := residualHistory.get
                (K .pairConditionalFactorizationResidual)
              change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
              exact Sum.inr (Sum.inr openResidual)
          | .left coveredHistory =>
              match pairSystemOutcomeDichotomy (data := spineData)
                  coveredHistory (by simp [K_eq_iff])
                    (by simp [K_eq_iff]) with
              | .left earlyHistory =>
                  let typeBHistory :=
                    (pairSystemEarlyTypeBEntryRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run earlyHistory
                        (by simp [K_eq_iff])
                  let typeBEntry := typeBHistory.get (K .typeBFanEntry)
                  change ((K .typeBFanEntry).At selected) at typeBEntry
                  let bridgelessrowStep :=
                    (bridgelessRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      typeBHistory (by simp [K_eq_iff])
                  let remaindernormalizationrowStep :=
                    (remainderNormalizationRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      bridgelessrowStep (by simp [K_eq_iff])
                  let remainderrelabelingentropyrowStep :=
                    (remainderRelabelingEntropyRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      remaindernormalizationrowStep (by simp [K_eq_iff])
                  exact Sum.inr (Sum.inl ⟨⟨
                    Or.inl (remainderrelabelingentropyrowStep.get
                      (K .pairSystemEarlyOutcome)).down,
                    selectedStrictSurplusTypeBContinuation
                      remainderrelabelingentropyrowStep,
                    (remainderrelabelingentropyrowStep.get (K .surplusAbove)).down,
                    (remainderrelabelingentropyrowStep.get (K .sparseSurplusSurvivor)).down⟩⟩)
              | .right serialHistory =>
                  match pairIncrementCoveredDichotomy (data := spineData)
                      serialHistory (by simp [K_eq_iff])
                        (by simp [K_eq_iff]) with
                  | .right residualHistory =>
                      let openResidual := residualHistory.get
                        (K .pairConditionalFactorizationResidual)
                      change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
                      exact Sum.inr (Sum.inr openResidual)
                  | .left incrementHistory =>
                      match pairIncrementOutcomeDichotomy (data := spineData)
                          incrementHistory (by simp [K_eq_iff])
                            (by simp [K_eq_iff]) with
                      | .left earlyHistory =>
                          let typeBHistory :=
                            (pairIncrementEarlyTypeBEntryRow
                              (BranchState := BranchState)
                              (Presentation :=
                                Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).run earlyHistory
                                (by simp [K_eq_iff])
                          let typeBEntry :=
                            typeBHistory.get (K .typeBFanEntry)
                          change ((K .typeBFanEntry).At selected) at typeBEntry
                          let bridgelessrowStep :=
                            (bridgelessRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              typeBHistory (by simp [K_eq_iff])
                          let remaindernormalizationrowStep :=
                            (remainderNormalizationRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              bridgelessrowStep (by simp [K_eq_iff])
                          let remainderrelabelingentropyrowStep :=
                            (remainderRelabelingEntropyRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              remaindernormalizationrowStep (by simp [K_eq_iff])
                          exact Sum.inr (Sum.inl ⟨⟨
                            Or.inr (remainderrelabelingentropyrowStep.get
                              (K .pairIncrementEarlyOutcome)).down,
                            selectedStrictSurplusTypeBContinuation
                              remainderrelabelingentropyrowStep,
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
                                (by simp [K_eq_iff]) (by simp [K_eq_iff])
                          exact (closedHistory.elimClosed (by infer_instance)).elim

end HypostructureErdos64EG
