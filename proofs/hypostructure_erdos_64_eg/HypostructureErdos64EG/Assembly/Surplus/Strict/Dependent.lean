import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SpineRows.CubicBaseline
import Hypostructure.Graph.Strategy.SpineRows.CurvatureTargetRank
import Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm
import Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization
import Hypostructure.Graph.Strategy.SpineRows.RemainderRelabelingEntropy
import HypostructureErdos64EG.Assembly.NearCubic.Local
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
noncomputable def Assembly.Internal.strictSurplusDependent
    {selected : EGInput.{u}}
    (dependentHistory : ExactLedger EGInput.{u} selected
      [K .dependentPairFamily, K .baselineSpineDemand, K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    StrictSurplusBoundaryResult selected := by
  match selectedBlockedPairRoutingDichotomy dependentHistory with
  | .left exitHistory =>
      -- `[133]`: the exit contradicts the survivor fact of `[125]`.
      exact (selectedSparsePairExitCloses exitHistory).elim
  | .right blockerHistory =>
      -- `[134]`--`[136]`, then `[137]`: decide the entropy count of
      -- `prop:sparse-entropy-sandwich-with-blockers` at the exact
      -- presentation; on its yes arm publish the exact role-fibre
      -- partition, `lem:capacity-token-high-load`, and the coupled test.
      let pairs := selectedCanonicalPairFacts blockerHistory
      let joined := selectedExactWindowJoinPressure pairs
      let tokens := selectedCapacityTokenFacts joined
      let entropySetup :=
        (blockedPairEntropySetupRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          tokens (by simp [blockedPairEntropySetupRow, K_eq_iff])
      match blockedPairEntropyDichotomy (data := spineData) entropySetup
          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
      | .right unrealizedHistory =>
          -- `[178]` (free side of `[137]`): the residual on which the entropy
          -- count of the free side of the capacity charge fails
          -- (`K .blockedPairCodeUnrealized`), carried as its own branch and
          -- closed exactly as the free-pair case: `lem:pair-failure-overlap` →
          -- `lem:pair-system-realizability` (`[179]`) →
          -- `lem:pair-system-increment-arithmetic` (`[180]`,
          -- `SerialSystem.Spectrum.exists_pow_realized`).  Next producer: the
          -- serial-spectrum row of `[179]` on this residual.
          let firstFailure :=
            (blockedPairOverlapFirstFailureRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run unrealizedHistory (by
                simp [blockedPairOverlapFirstFailureRow, K_eq_iff])
          let overlapSystem :=
            (pairOverlapSystemRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run firstFailure (by
                simp [pairOverlapSystemRow,
                  blockedPairOverlapFirstFailureRow, K_eq_iff])
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
                  demandReturns (by simp [K_eq_iff])
                    (by simp [K_eq_iff]) with
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
                        (pairSystemEarlyTypeBEntryRow
                          (BranchState := BranchState)
                          (Presentation :=
                            Graph.ReceiverLoad.LoadCapacityProfile)
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
                          match pairIncrementOutcomeDichotomy
                              (data := spineData) incrementHistory
                                (by simp [K_eq_iff])
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
                                    (by simp [K_eq_iff])
                                    (by simp [K_eq_iff])
                              exact (closedHistory.elimClosed
                                (by infer_instance)).elim
      | .left sandwichHistory =>
          let fibres :=
            (roleFibrePartitionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              sandwichHistory (by simp [K_eq_iff])
          let pressure :=
            (fibrePressureRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              fibres (by simp [K_eq_iff])
          match selectedCoupledExcessDichotomy pressure
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .left nearCubicHistory =>
              -- `[138]`: `σ(G) ≤ R_L(n) ≤ C_sp ⌈√n⌉` against `[19]`.
              let estimate :=
                (pressureSpineSurplusEstimateRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  nearCubicHistory (by simp [K_eq_iff])
              exact (selectedSpineSurplusEstimateCloses estimate).elim
          | .right overloadHistory =>
              -- `[139]`--`[144]` on the literal overload residual.
              let bridgeless :=
                (bridgelessRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run overloadHistory (by
                    simp [bridgelessRow, K_eq_iff])
              let normal :=
                (highCentreNormalFormRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run bridgeless (by
                    simp [highCentreNormalFormRow, bridgelessRow,
                      K_eq_iff])
              -- `[144]` consumes the standing cubic-baseline equation
              -- already retained in this ExactLedger; it is not
              -- republished on the overload branch.
              let cubic := normal
              -- The parallel arm of `[144]` invokes the closed exact
              -- response profile and `def:admissible-rank-quotient`.
              -- Publish their existing prerequisite-free `[31]` row on
              -- this same overload ledger so `[144]` reads both facts via
              -- `inputs.get`; do not reconstruct either definition in the
              -- routing proof.
              let quotientFacts :=
                (curvatureTargetRankRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run cubic (by
                    simp [curvatureTargetRankRow, cubicBaselineRow,
                      highCentreNormalFormRow, K_eq_iff])
              let normalized :=
                (remainderNormalizationRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run quotientFacts (by simp [K_eq_iff])
              let relabelingEntropy :=
                (remainderRelabelingEntropyRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run normalized (by simp [K_eq_iff])
              match windowOverloadClassDichotomy (data := spineData) relabelingEntropy
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left windowHistory =>
                  let audited :=
                    (windowIncidenceAuditRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run windowHistory (by simp [K_eq_iff])
                  let routed := selectedBottleneckDischarge audited
                    (by simp [K_eq_iff]) (by simp [K_eq_iff])
                    (by simp [K_eq_iff])
                  exact Sum.inl ⟨⟨
                    (routed.get (K .typeBHandoff)).down,
                    (routed.get (K .typeBFanEntry)).down,
                        (routed.get (K .bottleneckRouting)).down,
                        (routed.get (K .homogeneousBottleneckPattern)).down,
                        (routed.get (K .sparsePressureOverload)).down,
                        (routed.get (K .capacityTokenLedger)).down,
                    (routed.get (K .surplusAbove)).down,
                    (routed.get (K .sparseSurplusSurvivor)).down⟩⟩
              | .right windowAbsent =>
                  match remainderOverloadClassDichotomy (data := spineData)
                      windowAbsent (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                  | .left remainderHistory =>
                      let audited :=
                        (remainderSurplusAuditRow (BranchState := BranchState)
                          (Presentation :=
                            Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run remainderHistory (by
                            simp [K_eq_iff])
                      let routed := selectedBottleneckDischarge audited
                        (by simp [K_eq_iff]) (by simp [K_eq_iff])
                        (by simp [K_eq_iff])
                      exact Sum.inl ⟨⟨
                        (routed.get (K .typeBHandoff)).down,
                        (routed.get (K .typeBFanEntry)).down,
                        (routed.get (K .bottleneckRouting)).down,
                        (routed.get (K .homogeneousBottleneckPattern)).down,
                        (routed.get (K .sparsePressureOverload)).down,
                        (routed.get (K .capacityTokenLedger)).down,
                        (routed.get (K .surplusAbove)).down,
                        (routed.get (K .sparseSurplusSurvivor)).down⟩⟩
                  | .right remainderAbsent =>
                      let audited :=
                        (primitiveCarrierAuditRow (BranchState := BranchState)
                          (Presentation :=
                            Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run remainderAbsent (by
                            simp [K_eq_iff])
                      let routed := selectedBottleneckDischarge audited
                        (by simp [K_eq_iff]) (by simp [K_eq_iff])
                        (by simp [K_eq_iff])
                      exact Sum.inl ⟨⟨
                        (routed.get (K .typeBHandoff)).down,
                        (routed.get (K .typeBFanEntry)).down,
                        (routed.get (K .bottleneckRouting)).down,
                        (routed.get (K .homogeneousBottleneckPattern)).down,
                        (routed.get (K .sparsePressureOverload)).down,
                        (routed.get (K .capacityTokenLedger)).down,
                        (routed.get (K .surplusAbove)).down,
                        (routed.get (K .sparseSurplusSurvivor)).down⟩⟩

end HypostructureErdos64EG
