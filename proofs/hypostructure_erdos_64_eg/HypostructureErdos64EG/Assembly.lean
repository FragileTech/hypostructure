import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Final Erdős assembly boundary

This file connects the public `Core.Target` registered in `Problem.lean` to the
canonical exact-ledger residual used by the spine.  It does not define rows or
transport state: the only proof input it accepts is the ledger theorem that the
selected residual whose ledger starts with `K .selection` closes.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

noncomputable abbrev EGProblem :=
  Graph.Strategy.Spine.problem BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile spineData

noncomputable def EGTarget : Core.Target EGProblem :=
  Graph.minimumDegreeCycleTarget erdosReceiverLoadProfile.baselineDegree
    BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    PowerOfTwoLength (fun exponent => exponent ≥ 2) (fun exponent => 2 ^ exponent)
    powerOfTwoLength_iff

noncomputable abbrev EGInput : Type (u + 1) :=
  Core.Strategy.ProblemInput EGProblem

noncomputable abbrev EGSelectionKey : FactKey EGInput :=
  K (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData) .selection

/-- The entry prefix `[5]`--`[18]`, run on the selected exact ledger. -/
noncomputable def selectedEntryPrefix
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    ExactLedger EGInput.{u} selected
      [K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] := by
  let h1 :=
    (returnAvoidanceRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by
        simp [returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h2 :=
    (noProperBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by
        simp [noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h3 :=
    (deletionCriticalityRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [deletionCriticalityRow, noProperBaselineRow, returnAvoidanceRow,
          EGSelectionKey, K_eq_iff])
  let h13 :=
    (replacementExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h3 (by
        simp [replacementExclusionRow, deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h4 :=
    (interfaceReplacementRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h13 (by
        simp [interfaceReplacementRow, replacementExclusionRow,
          deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h5 :=
    (obstructionPackingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h4 (by
        simp [obstructionPackingRow, interfaceReplacementRow,
          replacementExclusionRow,
          deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGTarget, EGSelectionKey,
          K_eq_iff])
  exact
    (localAlgebraRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h5 (by
        simp [localAlgebraRow, obstructionPackingRow, interfaceReplacementRow,
          replacementExclusionRow,
          deletionCriticalityRow, noProperBaselineRow, returnAvoidanceRow, EGTarget,
          EGSelectionKey, K_eq_iff])

/-- Node `[19]`, run on the selected exact-ledger prefix. -/
noncomputable def selectedSurplusDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .surplusAbove)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .surplusAtOrBelow)
      (selectedEntryPrefix history) :=
  Decision.run (selectedEntryPrefix history) (K .surplusAbove) (K .surplusAtOrBelow)
    `HypostructureErdos64EG.selectedSurplusDichotomy
    (if above : spineData.surplusThreshold selected.object.vertexCount <
        selected.object.degreeSurplus spineData.threshold then
      .inl ⟨above⟩
    else
      .inr ⟨Nat.le_of_not_lt above⟩)

/-- Node `[125]`: split the literal strict-surplus residual into the named
sparse-exit arm and the survivor arm. -/
noncomputable def selectedSparseSurplusExitDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision (K .sparsePairExit) (K .sparseSurplusSurvivor) history :=
  sparseSurplusExitDichotomy history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Nodes `[125]`--`[128]`, sparse-surplus activation on node `[125]`'s
literal survivor residual. -/
noncomputable def selectedSparseSurplusActivation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let h2 :=
    (sparseSlackSurplusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [sparseSlackSurplusRow, K_eq_iff])
  let h3 :=
    (activeSurplusFamilyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h2 (by
        simp [activeSurplusFamilyRow, sparseSlackSurplusRow, K_eq_iff])
  let h4 :=
    (sparsePortActivationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h3 (by
        simp [sparsePortActivationRow, activeSurplusFamilyRow,
          sparseSlackSurplusRow, K_eq_iff])
  exact
    (activeSurplusDemandsRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h4 (by
        simp [activeSurplusDemandsRow, sparsePortActivationRow,
          activeSurplusFamilyRow, sparseSlackSurplusRow,
          K_eq_iff])

/-- Node `[129]`, the paper's common active-family baseline demand on the
strict surplus arm.  This reads only the completed `[125]`--`[128]` fact; it
does not read or manufacture the sibling node `[21]` package. -/
noncomputable def selectedBaselineSpineDemand
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor, K .surplusAbove,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (baselineSpineDemandRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [baselineSpineDemandRow, K_eq_iff])

/-- Node `[130]`: the full pair-response family, split into the paper's
independent and dependent residuals on the literal `[129]` ledger. -/
noncomputable def selectedPairResponseIndependenceDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision (K .independentPairFamily) (K .dependentPairFamily) history :=
  pairResponseIndependenceDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[131]`, the exact mixed sparse-spine dependence fact on the
independent residual of `[130]`. -/
noncomputable def selectedMixedSparseSpineDependence
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .independentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .mixedSparseSpineDependence, K .independentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (mixedSparseSpineDependenceRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [mixedSparseSpineDependenceRow, K_eq_iff])

/-- Node `[131]`, `lem:exact-cubic-baseline-budget` on the literal residual
already carrying the mixed sparse-spine dependence fact. -/
noncomputable def selectedExactCubicBaselineBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .mixedSparseSpineDependence, K .independentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .exactCubicBaselineBudget, K .mixedSparseSpineDependence,
        K .independentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (exactCubicBaselineBudgetRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [exactCubicBaselineBudgetRow, K_eq_iff])

/-- Node `[131]`, `lem:incremental-skeleton-room` on the literal residual
carrying the exact cubic baseline evaluation. -/
noncomputable def selectedIncrementalSkeletonRoom
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .exactCubicBaselineBudget, K .mixedSparseSpineDependence,
        K .independentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .incrementalSkeletonRoom, K .exactCubicBaselineBudget,
        K .mixedSparseSpineDependence, K .independentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (incrementalSkeletonRoomRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [incrementalSkeletonRoomRow, K_eq_iff])

/-- Node `[131]`, `lem:skeleton-dominates` on the literal residual carrying
the incremental-room fact. -/
noncomputable def selectedSkeletonDominates
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .incrementalSkeletonRoom, K .exactCubicBaselineBudget,
        K .mixedSparseSpineDependence, K .independentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .incrementalSkeletonRoom,
        K .exactCubicBaselineBudget, K .mixedSparseSpineDependence,
        K .independentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (skeletonDominatesRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [skeletonDominatesRow, K_eq_iff])

/-- Node `[132]`, the sparse-pair routing split after baseline demand. -/
noncomputable def selectedBlockedPairRoutingDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .sparsePairExit)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .canonicalBlockerRoute)
      history :=
  blockedPairRoutingDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])
/-- Node `[133]`, sparse-pair exit closes against the survivor fact. -/
noncomputable def selectedSparsePairExitCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePairExit, K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  exact (history.get (K .sparseSurplusSurvivor)).down
    (history.get (K .sparsePairExit)).down

/-- Nodes `[130]` and `[134]`, canonical pair ledger on the blocker arm. -/
noncomputable def selectedCanonicalPairFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  exact
    (canonicalPairLedgerRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
        simp [canonicalPairLedgerRow, K_eq_iff])

/-- Node `[135]`, exact window-join pressure on the literal `[134]` residual. -/
noncomputable def selectedExactWindowJoinPressure
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (exactWindowJoinPressureRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [exactWindowJoinPressureRow, K_eq_iff])

/-- Node `[136]`, capacity tokens on the literal `[135]` residual. -/
noncomputable def selectedCapacityTokenFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .capacityTokenLedger, K .sparseUpperEnvelope,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (capacityTokenLedgerRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [capacityTokenLedgerRow, K_eq_iff])

/-- Node `[138]`, near-cubic pressure gives the spine surplus estimate. -/
noncomputable def selectedPressureSpineSurplusEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePressureNearCubic, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .spineSurplusEstimate, K .sparsePressureNearCubic,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (pressureSpineSurplusEstimateRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [pressureSpineSurplusEstimateRow, K_eq_iff])

noncomputable def selectedPressureNearCubicCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePressureNearCubic, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let afterEstimate := selectedPressureSpineSurplusEstimate history
  have lower :
      spineData.surplusThreshold selected.object.vertexCount <
        selected.object.degreeSurplus spineData.threshold := by
    change Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object
    exact (afterEstimate.get (K .surplusAbove)).down
  have upper :
      selected.object.degreeSurplus spineData.threshold ≤
        spineData.spineScale * Core.ceilSqrt selected.object.vertexCount := by
    change Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .spineSurplusEstimate selected.object
    exact (afterEstimate.get (K .spineSurplusEstimate)).down
  exact Nat.not_lt_of_ge (by
    simpa [Graph.Strategy.Spine.Data.surplusThreshold] using upper) lower

/-- Node `[139]`: classify the concrete overload token carried by the literal
incoming residual as window-incidence or non-window. -/
noncomputable def selectedWindowClassDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision (K .windowClassOverload) (K .windowClassAbsent) history :=
  windowOverloadClassDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[140]`: publish the exact window-incidence geometric audit on the
literal yes residual of `[139]`. -/
noncomputable def selectedWindowIncidenceAudit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .windowIncidenceAudit, K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (windowIncidenceAuditRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [windowIncidenceAuditRow, K_eq_iff])

/-- Node `[142]`: publish the exact remainder-surplus geometric audit on the
literal yes residual of `[141]`. -/
noncomputable def selectedRemainderSurplusAudit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .remainderSurplusAudit, K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (remainderSurplusAuditRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [remainderSurplusAuditRow, K_eq_iff])

/-- Node `[143]`: publish the canonical primitive-class verdict and its exact
geometric audit on the literal no-remainder residual. -/
noncomputable def selectedPrimitiveCarrierAudit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  let classified :=
    (primitiveClassOverloadRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [primitiveClassOverloadRow, K_eq_iff])
  (primitiveCarrierAuditRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run classified
      (by simp [primitiveCarrierAuditRow, primitiveClassOverloadRow, K_eq_iff])

/-- Node `[144]`: the manuscript's fixed homogeneous caps versus positive
same-token bottleneck-pattern alternative, decided on the literal window-audit
residual. -/
noncomputable def selectedWindowHomogeneousCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowIncidenceAudit, K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
      history :=
  Decision.run history (K .homogeneousCapsHold)
    (K .homogeneousBottleneckPattern)
    `HypostructureErdos64EG.selectedWindowHomogeneousCapsDichotomy
    (Classical.choice (show Nonempty
        ((K .homogeneousCapsHold).At selected ⊕
          (K .homogeneousBottleneckPattern).At selected) from by
      classical
      by_cases caps : Graph.HomogeneousCapsHold selected.object
          spineData.threshold spineData.windowOrder
          (Graph.SameTokenRoutingGerms.RoutingLabel
            spineData.BoundaryProfile
            (Graph.WindowCurvature.Label spineData.windowOrder))
      · exact ⟨.inl ⟨caps⟩⟩
      · exact ⟨.inr ⟨Graph.homogeneousBottleneckPatternStatement_of_not_caps
          selected.object caps⟩⟩))
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[144]`: the same manuscript caps/pattern decision on the literal
remainder-surplus audit residual. -/
noncomputable def selectedRemainderHomogeneousCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderSurplusAudit, K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
      history :=
  Decision.run history (K .homogeneousCapsHold)
    (K .homogeneousBottleneckPattern)
    `HypostructureErdos64EG.selectedRemainderHomogeneousCapsDichotomy
    (Classical.choice (show Nonempty
        ((K .homogeneousCapsHold).At selected ⊕
          (K .homogeneousBottleneckPattern).At selected) from by
      classical
      by_cases caps : Graph.HomogeneousCapsHold selected.object
          spineData.threshold spineData.windowOrder
          (Graph.SameTokenRoutingGerms.RoutingLabel
            spineData.BoundaryProfile
            (Graph.WindowCurvature.Label spineData.windowOrder))
      · exact ⟨.inl ⟨caps⟩⟩
      · exact ⟨.inr ⟨Graph.homogeneousBottleneckPatternStatement_of_not_caps
          selected.object caps⟩⟩))
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[144]`: the manuscript caps/pattern Decision on the literal
primitive-carrier audit residual. -/
noncomputable def selectedPrimitiveHomogeneousCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .primitiveCarrierAudit, K .primitiveClassOverload,
        K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
      history :=
  Decision.run history (K .homogeneousCapsHold)
    (K .homogeneousBottleneckPattern)
    `HypostructureErdos64EG.selectedPrimitiveHomogeneousCapsDichotomy
    (Classical.choice (show Nonempty
        ((K .homogeneousCapsHold).At selected ⊕
          (K .homogeneousBottleneckPattern).At selected) from by
      classical
      by_cases caps : Graph.HomogeneousCapsHold selected.object
          spineData.threshold spineData.windowOrder
          (Graph.SameTokenRoutingGerms.RoutingLabel
            spineData.BoundaryProfile
            (Graph.WindowCurvature.Label spineData.windowOrder))
      · exact ⟨.inl ⟨caps⟩⟩
      · exact ⟨.inr ⟨Graph.homogeneousBottleneckPatternStatement_of_not_caps
          selected.object caps⟩⟩))
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[144]`, the manuscript's homogeneous-cap closure on the literal
window-audit caps residual. -/
noncomputable def selectedWindowHomogeneousCapsEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .windowIncidenceAudit,
        K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneck, K .homogeneousCapsHold,
        K .windowIncidenceAudit,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (homogeneousCapsCloseRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [homogeneousCapsCloseRow, K_eq_iff])

/-- Node `[144]`, cap-close pressure on the remainder audit caps arm. -/
noncomputable def selectedRemainderHomogeneousCapsEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .remainderSurplusAudit,
        K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneck, K .homogeneousCapsHold,
        K .remainderSurplusAudit,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (homogeneousCapsCloseRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [homogeneousCapsCloseRow, K_eq_iff])

/-- Node `[144]`, the manuscript's homogeneous-cap closure on the literal
primitive-carrier caps residual. -/
noncomputable def selectedPrimitiveHomogeneousCapsEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .primitiveClassOverload,
        K .primitiveCarrierAudit,
        K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneck, K .homogeneousCapsHold,
        K .primitiveClassOverload, K .primitiveCarrierAudit,
        K .remainderClassAbsent,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (homogeneousCapsCloseRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [homogeneousCapsCloseRow, K_eq_iff])

/-- Node `[144]`, bottleneck routing fact on the primitive audit pattern arm. -/
noncomputable def selectedWindowOverloadCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .homogeneousCapsHold)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .homogeneousBottleneckPattern)
      (selectedWindowIncidenceAudit history) :=
  selectedWindowHomogeneousCapsDichotomy (selectedWindowIncidenceAudit history)

/-- Nodes `[142]` and `[144]`, remainder-overload audit through homogeneous caps. -/
noncomputable def selectedRemainderOverloadCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .homogeneousCapsHold)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .homogeneousBottleneckPattern)
      (selectedRemainderSurplusAudit history) :=
  selectedRemainderHomogeneousCapsDichotomy
    (selectedRemainderSurplusAudit history)

/-- Nodes `[143]` and `[144]`, primitive-overload audit through homogeneous caps. -/
noncomputable def selectedPrimitiveOverloadCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .homogeneousCapsHold)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .homogeneousBottleneckPattern)
      (selectedPrimitiveCarrierAudit history) :=
  selectedPrimitiveHomogeneousCapsDichotomy
    (selectedPrimitiveCarrierAudit history)

/-- Nodes `[140]`--`[144]`, window-overload arm reduced to bottleneck routing. -/
noncomputable def selectedWindowOverloadBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .windowIncidenceAudit,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBHandoff, K .bottleneckRouting,
        K .homogeneousBottleneckPattern, K .windowIncidenceAudit,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  let routed :=
    (bottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [bottleneckRoutingRow, K_eq_iff])
  (typeBHandoffRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    routed (by simp [typeBHandoffRow, bottleneckRoutingRow, K_eq_iff])

/-- Nodes `[140]`--`[144]`, window-overload bottleneck arm through the Type B
bridge-mass ledger row. -/
noncomputable def selectedWindowOverloadBridgeMassHistory
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .windowIncidenceAudit,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) := by
  let routed := selectedWindowOverloadBottleneckRouting history
  exact
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run routed
      (by simp [bridgeFanMassRow, selectedWindowOverloadBottleneckRouting,
        K_eq_iff])

/-- Nodes `[140]`--`[144]`, window-overload bottleneck arm through the Type B
bridge sublinearity ledger fact. -/
noncomputable def selectedWindowOverloadBridgeSublinearHistory
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .windowIncidenceAudit,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) := by
  let afterBridgeMass := selectedWindowOverloadBridgeMassHistory history
  exact
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterBridgeMass
      (by simp [typeBBridgeSublinearRow,
        selectedWindowOverloadBridgeMassHistory,
        selectedWindowOverloadBottleneckRouting, K_eq_iff])

/-- Nodes `[142]`--`[144]`, remainder-overload arm reduced to bottleneck routing. -/
noncomputable def selectedRemainderOverloadBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .remainderSurplusAudit,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBHandoff, K .bottleneckRouting,
        K .homogeneousBottleneckPattern, K .remainderSurplusAudit,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  let routed :=
    (bottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [bottleneckRoutingRow, K_eq_iff])
  (typeBHandoffRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    routed (by simp [typeBHandoffRow, bottleneckRoutingRow, K_eq_iff])

/-- Nodes `[142]`--`[144]`, remainder-overload bottleneck arm through the Type B
bridge-mass ledger row. -/
noncomputable def selectedRemainderOverloadBridgeMassHistory
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .remainderSurplusAudit,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) := by
  let routed := selectedRemainderOverloadBottleneckRouting history
  exact
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run routed
      (by simp [bridgeFanMassRow,
        selectedRemainderOverloadBottleneckRouting, K_eq_iff])

/-- Nodes `[142]`--`[144]`, remainder-overload bottleneck arm through the Type B
bridge sublinearity ledger fact. -/
noncomputable def selectedRemainderOverloadBridgeSublinearHistory
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .remainderSurplusAudit,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) := by
  let afterBridgeMass := selectedRemainderOverloadBridgeMassHistory history
  exact
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterBridgeMass
      (by simp [typeBBridgeSublinearRow,
        selectedRemainderOverloadBridgeMassHistory,
        selectedRemainderOverloadBottleneckRouting, K_eq_iff])

/-- Nodes `[143]`--`[144]`, primitive-overload arm reduced to bottleneck routing. -/
noncomputable def selectedPrimitiveOverloadBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .primitiveCarrierAudit,
        K .primitiveClassOverload, K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBHandoff, K .bottleneckRouting,
        K .homogeneousBottleneckPattern, K .primitiveCarrierAudit,
        K .primitiveClassOverload,
        K .remainderClassAbsent,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  let routed :=
    (bottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [bottleneckRoutingRow, K_eq_iff])
  (typeBHandoffRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    routed (by simp [typeBHandoffRow, bottleneckRoutingRow, K_eq_iff])

/-- Nodes `[143]`--`[144]`, primitive-overload bottleneck arm through the Type B
bridge-mass ledger row. -/
noncomputable def selectedPrimitiveOverloadBridgeMassHistory
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .primitiveCarrierAudit,
        K .primitiveClassOverload, K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) := by
  let routed := selectedPrimitiveOverloadBottleneckRouting history
  exact
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run routed
      (by simp [bridgeFanMassRow,
        selectedPrimitiveOverloadBottleneckRouting, K_eq_iff])

/-- Nodes `[143]`--`[144]`, primitive-overload bottleneck arm through the Type B
bridge sublinearity ledger fact. -/
noncomputable def selectedPrimitiveOverloadBridgeSublinearHistory
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .primitiveCarrierAudit,
        K .primitiveClassOverload, K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) := by
  let afterBridgeMass := selectedPrimitiveOverloadBridgeMassHistory history
  exact
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterBridgeMass
      (by simp [typeBBridgeSublinearRow,
        selectedPrimitiveOverloadBridgeMassHistory,
        selectedPrimitiveOverloadBottleneckRouting, K_eq_iff])

/-- Node `[22]`'s hot/cold decision on the separated package.

The overflow cursor is the live-hot terminal `[23]`; the cap cursor is the
literal no-arm residual forwarded toward `[24]` and the cold continuation. -/
noncomputable def selectedBarrierDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      history (by simp [hotColdPartitionRow, K_eq_iff])
  Decision.run partitioned (K .barrierCap) (K .barrierOverflow)
    `HypostructureErdos64EG.selectedBarrierDichotomy
    (by
      classical
      obtain ⟨_positive, packing, valid, cardinality, maximal⟩ :=
        (partitioned.get (K .maximalPacking)).down
      have stable : ∀ family : Finset Nat,
          partitioned.current.object.edgeCount ∈ family →
            Graph.skeletonBudget partitioned.current.object ≤
              Graph.variableEdgeBudget partitioned.current.object.vertexCount
                family :=
        fun _family member =>
          Graph.skeletonBudget_le_variableEdgeBudget
            partitioned.current.object member
      by_cases overflow : Graph.skeletonBudget partitioned.current.object <
          2 ^ (spineData.windowRate *
            spineData.separatedScaleCount
              partitioned.current.object.vertexCount * packing.card)
      · exact .inr ⟨packing, valid, cardinality, maximal, overflow⟩
      · exact .inl ⟨packing, valid, cardinality, maximal,
          Nat.le_of_not_lt overflow, stable⟩)
    (by simp [hotColdPartitionRow, K_eq_iff])
    (by simp [hotColdPartitionRow, K_eq_iff])

/-- Nodes `[22]`--`[24]`, after the barrier cap arm. -/
noncomputable def selectedDensityBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (densityBudgetRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [densityBudgetRow, K_eq_iff])

/-- Nodes `[25]`--`[31]`, after the density cap path. -/
noncomputable def selectedCompletedSpinePrefix
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .targetRankCircuit, K .curvatureTargetRank, K .functionalRankQuotient,
        K .admissibleRankQuotient, K .exactResponseProfile, K .wedgeSupply,
        K .stubSupply, K .boundaryDemand, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let h1 := selectedDensityBudget history
  let h2 :=
    (remainderNormalizationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by simp [remainderNormalizationRow, selectedDensityBudget, K_eq_iff])
  let h3 :=
    (boundaryDemandRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [boundaryDemandRow, remainderNormalizationRow, selectedDensityBudget,
          K_eq_iff])
  let h3Supply :=
    (stubSupplyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [stubSupplyRow, boundaryDemandRow, remainderNormalizationRow,
          selectedDensityBudget, K_eq_iff])
  let h4 :=
    (wedgeSupplyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3Supply (by
        simp [wedgeSupplyRow, stubSupplyRow, boundaryDemandRow, remainderNormalizationRow,
          selectedDensityBudget, K_eq_iff])
  let h5 :=
    (exactResponseProfile (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h4 (by
        simp [exactResponseProfile, wedgeSupplyRow, stubSupplyRow, boundaryDemandRow,
          remainderNormalizationRow, selectedDensityBudget, K_eq_iff])
  let h6 :=
    (admissibleRankQuotient (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h5 (by
        simp [admissibleRankQuotient, exactResponseProfile, wedgeSupplyRow, stubSupplyRow,
          boundaryDemandRow, remainderNormalizationRow, selectedDensityBudget,
          K_eq_iff])
  let h7 :=
    (functionalRankQuotientRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h6 (by
        simp [functionalRankQuotientRow, admissibleRankQuotient,
          exactResponseProfile, wedgeSupplyRow, stubSupplyRow, boundaryDemandRow,
          remainderNormalizationRow, selectedDensityBudget, K_eq_iff])
  let h8 :=
    (curvatureTargetRankRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h7 (by
        simp [curvatureTargetRankRow, functionalRankQuotientRow,
          admissibleRankQuotient,
          exactResponseProfile, wedgeSupplyRow, stubSupplyRow, boundaryDemandRow,
          remainderNormalizationRow, selectedDensityBudget, K_eq_iff])
  exact
    (targetRankCircuitRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h8 (by
        simp [targetRankCircuitRow, curvatureTargetRankRow,
          functionalRankQuotientRow, admissibleRankQuotient,
          exactResponseProfile, wedgeSupplyRow, stubSupplyRow, boundaryDemandRow,
          remainderNormalizationRow, selectedDensityBudget, K_eq_iff])

/-- Node `[32]`, run on the completed near-cubic prefix. -/
noncomputable def selectedCurvatureRankDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .curvatureRankDrop)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .curvatureFullRank)
      (selectedCompletedSpinePrefix history) :=
  curvatureRankDichotomy (data := spineData)
    (selectedCompletedSpinePrefix history)
    (by simp [selectedCompletedSpinePrefix, K_eq_iff])
    (by simp [selectedCompletedSpinePrefix, K_eq_iff])

/-- Nodes `[22]`--`[32]`, barrier-cap arm through the curvature-rank split. -/
noncomputable def selectedBarrierCapCurvatureRankDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .curvatureRankDrop)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .curvatureFullRank)
      (selectedCompletedSpinePrefix history) :=
  selectedCurvatureRankDichotomy history

/-- Branch D `[33]`--`[46]`, closing the rank-drop arm of node `[32]`. -/
noncomputable def selectedRankDropCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .curvatureRankDrop, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let afterDependence :=
    (branchDependence (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [branchDependence, K_eq_iff])
  let contextDecision :=
    contextValidityDichotomy (data := spineData) afterDependence
      (by simp [branchDependence, K_eq_iff])
      (by simp [branchDependence, K_eq_iff])
  match contextDecision with
  | .left defectHistory =>
      let closedHistory :=
        closeImpossible defectHistory (K .contextDefect) (by
          simp [branchDependence, K_eq_iff])
      exact closedHistory.elimClosed (by infer_instance)
  | .right universalHistory =>
      let atomDecision :=
        atomCompressionDichotomy (data := spineData) universalHistory
          (by simp [branchDependence, K_eq_iff])
          (by simp [branchDependence, K_eq_iff])
      match atomDecision with
      | .left compressionHistory =>
          let closedHistory :=
            closeIncompatible compressionHistory (K .selection)
              (K .atomCompression) (by simp [branchDependence, K_eq_iff])
          exact closedHistory.elimClosed (by infer_instance)
      | .right delocalizedHistory =>
          let scopeDecision :=
            delocalizationScopeDichotomy (data := spineData) delocalizedHistory
              (by simp [branchDependence, K_eq_iff])
              (by simp [branchDependence, K_eq_iff])
          match scopeDecision with
          | .left properHistory =>
              let closedHistory :=
                closeIncompatible properHistory (K .selection)
                  (K .properDelocalization)
                  (by simp [branchDependence, K_eq_iff])
              exact closedHistory.elimClosed (by infer_instance)
          | .right globalHistory =>
              let afterRepair :=
                (repairIdentity (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run globalHistory (by
                    simp [repairIdentity, branchDependence, K_eq_iff])
              let afterBarrier :=
                (globalBarrier (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run afterRepair (by
                    simp [globalBarrier, repairIdentity, branchDependence,
                      K_eq_iff])
              let closedHistory :=
                closeIncompatible afterBarrier (K .selection)
                (K .globalBarrier) (by
                    simp [globalBarrier, repairIdentity, branchDependence,
                      K_eq_iff])
              exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[21]`--`[46]`, forwarding node `[22]`'s cold cursor to the spine.

As in the Type A decisions, the hot sibling is closed from its own cursor and
the cold sibling is passed unchanged to its next atomic rows. -/
noncomputable def selectedSeparatedFullRank
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedBarrierDichotomy history with
  | .left capHistory =>
      match selectedBarrierCapCurvatureRankDichotomy capHistory with
      | .left dropHistory =>
          exact False.elim (selectedRankDropCloses dropHistory)
      | .right fullRankHistory =>
          exact fullRankHistory
  | .right overflowHistory =>
      exact False.elim (selectedBarrierOverflowCloses overflowHistory)

/-- Node `[48]`, on the full-rank arm of node `[32]`. -/
noncomputable def selectedForcedCurvatureCost
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (forcedCurvatureCostRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [forcedCurvatureCostRow, K_eq_iff])

/-- Node `[50]`, the entropy split after forced curvature cost. -/
noncomputable def selectedRemainderEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderEntropyHigh)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderEntropyLow)
      (selectedForcedCurvatureCost history) :=
  remainderEntropyDichotomy (data := spineData)
    (selectedForcedCurvatureCost history)
    (K .remainderEntropyHigh) (K .remainderEntropyLow)
    (fun high => ⟨high⟩)
    (fun low => ⟨low⟩)
    (by simp [selectedForcedCurvatureCost, K_eq_iff])
    (by simp [selectedForcedCurvatureCost, K_eq_iff])

/-- Nodes `[48]`--`[50]`, full-rank arm through the entropy split. -/
noncomputable def selectedFullRankEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderEntropyHigh)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderEntropyLow)
      (selectedForcedCurvatureCost history) :=
  selectedRemainderEntropyDichotomy history

/-- Nodes `[21]`--`[50]`, separated near-cubic arm through the entropy split. -/
noncomputable def selectedSeparatedEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderEntropyHigh)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderEntropyLow)
      (selectedForcedCurvatureCost (selectedSeparatedFullRank history)) :=
  selectedFullRankEntropyDichotomy (selectedSeparatedFullRank history)

/-- Node `[52]`, on the high-entropy arm. -/
noncomputable def selectedEntropyPackage
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (entropyPackage (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [entropyPackage, K_eq_iff])

/-- Node `[53]`, after the high-entropy package demand. -/
noncomputable def selectedEntropyCapDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .entropyCapActive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .largeBudgetResidual)
      (selectedEntropyPackage history) :=
  entropyCapDichotomy (data := spineData)
    (selectedEntropyPackage history)
    (by simp [selectedEntropyPackage, K_eq_iff])
    (by simp [selectedEntropyPackage, K_eq_iff])

/-- Nodes `[52]`--`[53]`, high-entropy arm through the cap split. -/
noncomputable def selectedHighEntropyCapDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .entropyCapActive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .largeBudgetResidual)
      (selectedEntropyPackage history) :=
  selectedEntropyCapDichotomy history

/-- Nodes `[52]`--`[54]`, high-entropy arm reduced to the large-budget survivor. -/
noncomputable def selectedHighEntropyLargeBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedHighEntropyCapDichotomy history with
  | .left activeHistory =>
      exact False.elim (selectedEntropyCapActiveCloses activeHistory)
  | .right largeHistory =>
      exact largeHistory

/-- Node `[56]`, exact net-deficiency cap on the high-entropy Residual C arm. -/
noncomputable def selectedHighEntropyNetDeficiencyCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (netDeficiencyCapRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    (selectedHighEntropyLargeBudget history)
    (by simp [netDeficiencyCapRow, selectedHighEntropyLargeBudget, K_eq_iff])

/-- Node `[55]`, on the low-entropy arm. -/
noncomputable def selectedLowEntropyLargeBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (lowEntropyLargeBudgetRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [lowEntropyLargeBudgetRow, K_eq_iff])

/-- Node `[56]`, exact net-deficiency cap on the low-entropy Residual C arm. -/
noncomputable def selectedLowEntropyNetDeficiencyCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (netDeficiencyCapRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    (selectedLowEntropyLargeBudget history)
    (by simp [netDeficiencyCapRow, selectedLowEntropyLargeBudget, K_eq_iff])

/-- Node `[60]`, the order-regime split on the low-entropy Residual C arm. -/
noncomputable def selectedLowEntropyNetChargeOrderDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeLarge)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeSmall)
      (selectedLowEntropyNetDeficiencyCap history) :=
  netChargeOrderDichotomy (data := spineData)
    (selectedLowEntropyNetDeficiencyCap history)
    (K .netChargeLarge) (K .netChargeSmall)
    (fun large => ⟨large⟩)
    (fun small => ⟨small⟩)
    (by simp [selectedLowEntropyNetDeficiencyCap,
      selectedLowEntropyLargeBudget, K_eq_iff])
    (by simp [selectedLowEntropyNetDeficiencyCap,
      selectedLowEntropyLargeBudget, K_eq_iff])

/-- Node `[60]`, the net-charge cap on the large low-entropy arm. -/
noncomputable def selectedLowEntropyNetChargeCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap,
        K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (netChargeCap (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [netChargeCap, K_eq_iff])

/-- Nodes `[57]`--`[58]`, net-charge localization on the low-entropy arm. -/
noncomputable def selectedLowEntropyNetChargeLocalization
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let afterCap := selectedLowEntropyNetChargeCap history
  exact
    (netChargeLocalization (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterCap (by
        simp [netChargeLocalization, selectedLowEntropyNetChargeCap,
          K_eq_iff])

/-- Node `[59]`, the net-charge sign split on the low-entropy arm. -/
noncomputable def selectedLowEntropyNetChargeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeNonNegative)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeNegative)
      (selectedLowEntropyNetChargeLocalization history) :=
  netChargeDichotomy (data := spineData)
    (selectedLowEntropyNetChargeLocalization history)
    (by simp [selectedLowEntropyNetChargeLocalization,
      selectedLowEntropyNetChargeCap, K_eq_iff])
    (by simp [selectedLowEntropyNetChargeLocalization,
      selectedLowEntropyNetChargeCap, K_eq_iff])

/-- Node `[60]`, closing the nonnegative low-entropy arm after recording window pressure. -/
noncomputable def selectedLowEntropyNetChargeNonNegativeCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNonNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  obtain ⟨_positive, packing, valid, cardinality, maximal⟩ :=
    (history.get (K .maximalPacking)).down
  have negative :=
    (history.get (K .netChargeCap)).down packing valid cardinality
  have nonnegative :=
    (history.get (K .netChargeNonNegative)).down packing valid maximal
  exact ((selected.object.not_negativeNetCharge_iff
    (selected.object.remainderSupport packing) spineData.threshold
    spineData.dischargeScale).mpr nonnegative) negative

/-- Node `[61]`, selecting the negative support on the low-entropy arm. -/
noncomputable def selectedLowEntropyNegativeSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (negativeSupport (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [negativeSupport, K_eq_iff])

/-- Node `[62]`, Type A/B split on the low-entropy Residual C arm. -/
noncomputable def selectedLowEntropyTypeSplitDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeALowSurplus)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBHighSurplus)
      (selectedLowEntropyNegativeSupport history) :=
  typeSplitDichotomy (data := spineData)
    (selectedLowEntropyNegativeSupport history)
    (K .negativeSupport) (K .typeALowSurplus) (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun typeA => ⟨typeA⟩)
    (fun typeB => ⟨typeB⟩)
    (by simp [selectedLowEntropyNegativeSupport, K_eq_iff])
    (by simp [selectedLowEntropyNegativeSupport, K_eq_iff])

/-- Nodes `[57]`--`[61]`, low-entropy large-charge arm reduced to negative support. -/
noncomputable def selectedLowEntropyNegativeSupportAfterNetChargeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyNetChargeDichotomy history with
  | .left nonNegativeHistory =>
      exact False.elim
        (selectedLowEntropyNetChargeNonNegativeCloses nonNegativeHistory)
  | .right negativeHistory =>
      exact selectedLowEntropyNegativeSupport negativeHistory

/-- Nodes `[57]`--`[62]`, low-entropy large-charge arm through the Type A/B split. -/
noncomputable def selectedLowEntropyTypeSplitAfterNetChargeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeALowSurplus)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBHighSurplus)
      (selectedLowEntropyNegativeSupportAfterNetChargeDichotomy history) :=
  typeSplitDichotomy (data := spineData)
    (selectedLowEntropyNegativeSupportAfterNetChargeDichotomy history)
    (K .negativeSupport) (K .typeALowSurplus) (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun typeA => ⟨typeA⟩)
    (fun typeB => ⟨typeB⟩)
    (by
      simp [selectedLowEntropyNegativeSupportAfterNetChargeDichotomy,
        selectedLowEntropyNetChargeDichotomy,
        selectedLowEntropyNetChargeLocalization,
        selectedLowEntropyNetChargeCap, selectedLowEntropyNegativeSupport,
        K_eq_iff])
    (by
      simp [selectedLowEntropyNegativeSupportAfterNetChargeDichotomy,
        selectedLowEntropyNetChargeDichotomy,
        selectedLowEntropyNetChargeLocalization,
        selectedLowEntropyNetChargeCap, selectedLowEntropyNegativeSupport,
        K_eq_iff])

/-- Node `[60]`, the order-regime split on the high-entropy Residual C arm. -/
noncomputable def selectedHighEntropyNetChargeOrderDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeLarge)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeSmall)
      history :=
  netChargeOrderDichotomy (data := spineData) history
    (K .netChargeLarge) (K .netChargeSmall)
    (fun large => ⟨large⟩)
    (fun small => ⟨small⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[52]`--`[60]`, high-entropy survivor through the net-charge order split. -/
noncomputable def selectedHighEntropyNetChargeOrderAfterCapDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeLarge)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeSmall)
      (selectedHighEntropyNetDeficiencyCap history) :=
  selectedHighEntropyNetChargeOrderDichotomy
    (selectedHighEntropyNetDeficiencyCap history)

/-- Node `[60]`, the net-charge cap on the large high-entropy arm. -/
noncomputable def selectedHighEntropyNetChargeCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap,
        K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (netChargeCap (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [netChargeCap, K_eq_iff])

/-- Nodes `[57]`--`[58]`, net-charge localization on the high-entropy arm. -/
noncomputable def selectedHighEntropyNetChargeLocalization
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterCap := selectedHighEntropyNetChargeCap history
  exact
    (netChargeLocalization (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterCap (by
        simp [netChargeLocalization, selectedHighEntropyNetChargeCap,
          K_eq_iff])

/-- Node `[59]`, the net-charge sign split on the high-entropy arm. -/
noncomputable def selectedHighEntropyNetChargeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeNonNegative)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .netChargeNegative)
      (selectedHighEntropyNetChargeLocalization history) :=
  netChargeDichotomy (data := spineData)
    (selectedHighEntropyNetChargeLocalization history)
    (by simp [selectedHighEntropyNetChargeLocalization,
      selectedHighEntropyNetChargeCap, K_eq_iff])
    (by simp [selectedHighEntropyNetChargeLocalization,
      selectedHighEntropyNetChargeCap, K_eq_iff])

/-- Node `[60]`, closing the nonnegative high-entropy arm after recording window pressure. -/
noncomputable def selectedHighEntropyNetChargeNonNegativeCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNonNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  obtain ⟨_positive, packing, valid, cardinality, maximal⟩ :=
    (history.get (K .maximalPacking)).down
  have negative :=
    (history.get (K .netChargeCap)).down packing valid cardinality
  have nonnegative :=
    (history.get (K .netChargeNonNegative)).down packing valid maximal
  exact ((selected.object.not_negativeNetCharge_iff
    (selected.object.remainderSupport packing) spineData.threshold
    spineData.dischargeScale).mpr nonnegative) negative

/-- Node `[61]`, selecting the negative support on the high-entropy arm. -/
noncomputable def selectedHighEntropyNegativeSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (negativeSupport (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [negativeSupport, K_eq_iff])

/-- Node `[62]`, Type A/B split on the high-entropy Residual C arm. -/
noncomputable def selectedHighEntropyTypeSplitDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeALowSurplus)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBHighSurplus)
      (selectedHighEntropyNegativeSupport history) :=
  typeSplitDichotomy (data := spineData)
    (selectedHighEntropyNegativeSupport history)
    (K .negativeSupport) (K .typeALowSurplus) (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun typeA => ⟨typeA⟩)
    (fun typeB => ⟨typeB⟩)
    (by simp [selectedHighEntropyNegativeSupport, K_eq_iff])
    (by simp [selectedHighEntropyNegativeSupport, K_eq_iff])

/-- Nodes `[57]`--`[61]`, high-entropy large-charge arm reduced to negative support. -/
noncomputable def selectedHighEntropyNegativeSupportAfterNetChargeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedHighEntropyNetChargeDichotomy history with
  | .left nonNegativeHistory =>
      exact False.elim
        (selectedHighEntropyNetChargeNonNegativeCloses nonNegativeHistory)
  | .right negativeHistory =>
      exact selectedHighEntropyNegativeSupport negativeHistory

/-- Nodes `[57]`--`[62]`, high-entropy large-charge arm through the Type A/B split. -/
noncomputable def selectedHighEntropyTypeSplitAfterNetChargeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeALowSurplus)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBHighSurplus)
      (selectedHighEntropyNegativeSupportAfterNetChargeDichotomy history) :=
  typeSplitDichotomy (data := spineData)
    (selectedHighEntropyNegativeSupportAfterNetChargeDichotomy history)
    (K .negativeSupport) (K .typeALowSurplus) (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun typeA => ⟨typeA⟩)
    (fun typeB => ⟨typeB⟩)
    (by
      simp [selectedHighEntropyNegativeSupportAfterNetChargeDichotomy,
        selectedHighEntropyNetChargeDichotomy,
        selectedHighEntropyNetChargeLocalization,
        selectedHighEntropyNetChargeCap, selectedHighEntropyNegativeSupport,
        K_eq_iff])
    (by
      simp [selectedHighEntropyNegativeSupportAfterNetChargeDichotomy,
        selectedHighEntropyNetChargeDichotomy,
        selectedHighEntropyNetChargeLocalization,
        selectedHighEntropyNetChargeCap, selectedHighEntropyNegativeSupport,
        K_eq_iff])

/-- Node `[88]`, receiver routing on the literal low-entropy Type A arm. -/
noncomputable def selectedLowEntropyTypeAReceiverRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeAReceiverRoutingRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [typeAReceiverRoutingRow, K_eq_iff])

/-- Node `[89]`, saturation split after node `[88]` on the same ledger. -/
noncomputable def selectedLowEntropyTypeASaturationDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedReceiver)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAUnsaturatedReceivers)
      (selectedLowEntropyTypeAReceiverRouting history) :=
  typeASaturationDichotomy (selectedLowEntropyTypeAReceiverRouting history)
    (K .typeALowSurplus) (K .typeASaturatedReceiver)
    (K .typeAUnsaturatedReceivers)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [selectedLowEntropyTypeAReceiverRouting, K_eq_iff])
    (by simp [selectedLowEntropyTypeAReceiverRouting, K_eq_iff])

/-- `lem:typeA-port-return` on the literal low-entropy saturated residual. -/
noncomputable def selectedLowEntropyTypeAPortReturn
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeAPortReturnRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [typeAPortReturnRow, K_eq_iff])

/-- Nodes `[90]`--`[91]`, unsaturated discharge on the low-entropy Type A arm. -/
noncomputable def selectedLowEntropyTypeAVisibleEntryDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAVisibleEntry)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAVisibleFirstExcess)
      (selectedLowEntropyTypeAPortReturn history) :=
  typeAVisibleEntryDichotomy (selectedLowEntropyTypeAPortReturn history)
    (K .typeAReceiverRouting) (K .typeASaturatedReceiver)
    (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess)
    (fun fact packing valid maximal piece inside surplus =>
      fact.down packing valid maximal piece inside surplus)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [selectedLowEntropyTypeAPortReturn, K_eq_iff])
    (by simp [selectedLowEntropyTypeAPortReturn, K_eq_iff])

/-- Node `[88]`, receiver routing on the literal high-entropy Type A arm. -/
noncomputable def selectedHighEntropyTypeAReceiverRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeAReceiverRoutingRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [typeAReceiverRoutingRow, K_eq_iff])

/-- Node `[89]`, high-entropy saturation split after node `[88]`. -/
noncomputable def selectedHighEntropyTypeASaturationDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedReceiver)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAUnsaturatedReceivers)
      (selectedHighEntropyTypeAReceiverRouting history) :=
  typeASaturationDichotomy (selectedHighEntropyTypeAReceiverRouting history)
    (K .typeALowSurplus) (K .typeASaturatedReceiver)
    (K .typeAUnsaturatedReceivers)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [selectedHighEntropyTypeAReceiverRouting, K_eq_iff])
    (by simp [selectedHighEntropyTypeAReceiverRouting, K_eq_iff])

/-- `lem:typeA-port-return` on the literal high-entropy saturated residual. -/
noncomputable def selectedHighEntropyTypeAPortReturn
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeAPortReturnRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [typeAPortReturnRow, K_eq_iff])

/-- Nodes `[90]`--`[91]`, unsaturated discharge on the high-entropy Type A arm. -/
noncomputable def selectedHighEntropyTypeAVisibleEntryDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAVisibleEntry)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAVisibleFirstExcess)
      (selectedHighEntropyTypeAPortReturn history) :=
  typeAVisibleEntryDichotomy (selectedHighEntropyTypeAPortReturn history)
    (K .typeAReceiverRouting) (K .typeASaturatedReceiver)
    (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess)
    (fun fact packing valid maximal piece inside surplus =>
      fact.down packing valid maximal piece inside surplus)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [selectedHighEntropyTypeAPortReturn, K_eq_iff])
    (by simp [selectedHighEntropyTypeAPortReturn, K_eq_iff])

/-- Node `[94]`, silent handoff fact on the low-entropy no-visible Type A arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitFourDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFour)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFourFree)
      history :=
  Decision.run history (K .typeASaturatedHandoffExitFour)
    (K .typeASaturatedHandoffExitFourFree)
    `HypostructureErdos64EG.selectedLowEntropyTypeAFirstExcessExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, silent⟩ :=
        (history.get (K .typeASaturatedHandoffSilent)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength spineData.LengthOK) piece
              spineData.threshold receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
              spineData.threshold spineData.dischargeScale receiver peeled
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[101]` ready state on the high-entropy first-excess Type A arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitFourDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFour)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFourFree)
      history :=
  Decision.run history (K .typeASaturatedHandoffExitFour)
    (K .typeASaturatedHandoffExitFourFree)
    `HypostructureErdos64EG.selectedHighEntropyTypeAFirstExcessExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, silent⟩ :=
        (history.get (K .typeASaturatedHandoffSilent)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength spineData.LengthOK) piece
              spineData.threshold receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
              spineData.threshold spineData.dischargeScale receiver peeled
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[103]`, exit-`(5)` split on the low-entropy first-excess arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitFiveDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFiveFree)
      history :=
  typeAExitFiveDichotomy history
    (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFive) (K .typeAExitFiveFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Low-entropy first-excess Type A continuation after node `[104]`. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitFiveFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeAFirstExcessExitFiveDichotomy history with
  | .left exitHistory =>
      have contradiction : False := by
        let uncompressible :=
          (ExactLedger.get exitHistory (K .uncompressible)).down
        obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
          _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
          _noExitFour, support, compression⟩ :=
          (ExactLedger.get exitHistory (K .typeAExitFive)).down
        exact uncompressible support compression
      exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[105]`, exit-`(6)` split on the low-entropy first-excess arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitSixDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSix)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixFree)
      history :=
  typeAExitSixDichotomy history
    (K .typeAExitFiveFree) (K .typeAExitSix) (K .typeAExitSixFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, scope split on the low-entropy first-excess exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitSixScopeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixProper)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixGlobal)
      history :=
  Decision.run history (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `HypostructureErdos64EG.selectedTypeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (ExactLedger.get history (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Low-entropy first-excess Type A continuation after node `[106]`. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitSixFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeAFirstExcessExitSixDichotomy history with
  | .left exitHistory =>
      match selectedLowEntropyTypeAFirstExcessExitSixScopeDichotomy exitHistory with
      | .left properHistory =>
          have contradiction : False := by
            obtain ⟨support, replacement⟩ :=
              (ExactLedger.get properHistory (K .typeAExitSixProper)).down
            exact (ExactLedger.get properHistory (K .uncompressible)).down
              support replacement
          exact contradiction.elim
      | .right globalHistory =>
          have contradiction : False := by
            let selection :=
              (ExactLedger.get globalHistory (K .selection)).down
            obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
              (ExactLedger.get globalHistory (K .typeAExitSixGlobal)).down
            exact selection.1
              (transfer (selection.2 representative smaller
                representativeBaseline))
          exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[107]`, exit-`(7)` split on the low-entropy first-excess arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitSevenDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenProduced)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenFree)
      history :=
  Decision.run history (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `HypostructureErdos64EG.selectedTypeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (ExactLedger.get history (K .typeAExitSixFree)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases produced :
          Graph.Strategy.Spine.HandoffProduced spineData selected.object
            packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[108]`, Type B handoff on the low-entropy first-excess exit-`(7)` arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessExitSevenHandoff
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeAExitSevenHandoffRow (data := spineData)).run history
    (by simp [typeAExitSevenHandoffRow, K_eq_iff])

/-- Nodes `[65]`--`[67]`, Type-B high-centre normal form after the low-entropy handoff. -/
noncomputable def selectedLowEntropyTypeAFirstExcessHandoffNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (highCentreNormalFormRow (data := spineData)).run history
    (by simp [highCentreNormalFormRow, K_eq_iff])

/-- Node `[68]`, decorated heavy-centre/degree-four split on this literal ledger. -/
noncomputable def selectedLowEntropyTypeAFirstExcessHandoffDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      ((cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])) := by
  let baseline := (cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])
  exact heavyCentreDichotomy (data := spineData) baseline
    (by simp [cubicBaselineRow, K_eq_iff])
    (by simp [cubicBaselineRow, K_eq_iff])


/-- Node `[69]`, local dichotomy on this literal heavy sibling. -/
noncomputable def selectedLowEntropyTypeAFirstExcessHeavyLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (heavyCentreLocalDichotomyRow (data := spineData)).run history
    (by simp [heavyCentreLocalDichotomyRow, K_eq_iff])


/-- `def:decorated-typeB-envelope-support` on this literal Type-B handoff residual. -/
/-- Node `[78]`, degree-four activation on this literal sibling. -/
noncomputable def selectedLowEntropyTypeAFirstExcessDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (degreeFourProfileRow (data := spineData)).run history
    (by simp [degreeFourProfileRow, K_eq_iff])


noncomputable def selectedLowEntropyTypeAFirstExcessHandoffAssignedSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeBDecoratedAssignedSupportRow (data := spineData)).run history
    (by simp [typeBDecoratedAssignedSupportRow, K_eq_iff])

/-- Node `[110]`, route-8 residual profile on the low-entropy first-excess arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessRoute8ResidualProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenFree, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (route8ResidualProfileRow (data := spineData)).run history
    (by simp [route8ResidualProfileRow, K_eq_iff])

/-- Node `[111]`, global route-8 squeeze on the low-entropy first-excess arm. -/
noncomputable def selectedLowEntropyTypeAFirstExcessRoute8GlobalSqueeze
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (route8GlobalSqueezeRow (data := spineData)).run history
    (by simp [route8GlobalSqueezeRow, K_eq_iff])

/-- Node `[112]`, basin burden on the low-entropy first-excess route-8 residual. -/
noncomputable def selectedLowEntropyTypeAFirstExcessRoute8BasinBurden
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (route8BasinBurdenRow (data := spineData)).run history
    (by simp [route8BasinBurdenRow, K_eq_iff])

/-- Node `[113]`, large-budget deficit on the low-entropy route-8 burden ledger. -/
noncomputable def selectedLowEntropyTypeAFirstExcessRoute8LargeBudgetDeficit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8LargeBudgetDeficit, K .route8BasinBurden,
        K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (route8LargeBudgetDeficitRow (data := spineData)).run history
    (by simp [route8LargeBudgetDeficitRow, K_eq_iff])

/-- Node `[114]`, canonical carrier cores on the low-entropy route-8 residual. -/
noncomputable def selectedLowEntropyTypeAFirstExcessRoute8CarrierCore
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8LargeBudgetDeficit, K .route8BasinBurden,
        K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8CarrierCore, K .route8LargeBudgetDeficit,
        K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (route8CarrierCoreRow (data := spineData)).run history
    (by simp [route8CarrierCoreRow, K_eq_iff])

/-- Node `[115]`, the small-core collapse fact on the low-entropy route-8 residual. -/
noncomputable def selectedLowEntropyTypeAFirstExcessRoute8SmallCoreCollapse
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8CarrierCore, K .route8LargeBudgetDeficit,
        K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8SmallCoreCollapse, K .route8CarrierCore,
        K .route8LargeBudgetDeficit, K .route8BasinBurden,
        K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (route8SmallCoreCollapseRow (data := spineData)).run history
    (by simp [route8SmallCoreCollapseRow, K_eq_iff])

/-- Node `[103]`, exit-`(5)` split on the high-entropy first-excess arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitFiveDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFiveFree)
      history :=
  typeAExitFiveDichotomy history
    (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFive) (K .typeAExitFiveFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- High-entropy first-excess Type A continuation after node `[104]`. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitFiveFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedHighEntropyTypeAFirstExcessExitFiveDichotomy history with
  | .left exitHistory =>
      have contradiction : False := by
        let uncompressible :=
          (ExactLedger.get exitHistory (K .uncompressible)).down
        obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
          _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
          _noExitFour, support, compression⟩ :=
          (ExactLedger.get exitHistory (K .typeAExitFive)).down
        exact uncompressible support compression
      exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[105]`, exit-`(6)` split on the high-entropy first-excess arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitSixDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSix)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixFree)
      history :=
  typeAExitSixDichotomy history
    (K .typeAExitFiveFree) (K .typeAExitSix) (K .typeAExitSixFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, scope split on the high-entropy first-excess exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitSixScopeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixProper)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixGlobal)
      history :=
  Decision.run history (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `HypostructureErdos64EG.selectedTypeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (ExactLedger.get history (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- High-entropy first-excess Type A continuation after node `[106]`. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitSixFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedHighEntropyTypeAFirstExcessExitSixDichotomy history with
  | .left exitHistory =>
      match selectedHighEntropyTypeAFirstExcessExitSixScopeDichotomy exitHistory with
      | .left properHistory =>
          have contradiction : False := by
            obtain ⟨support, replacement⟩ :=
              (ExactLedger.get properHistory (K .typeAExitSixProper)).down
            exact (ExactLedger.get properHistory (K .uncompressible)).down
              support replacement
          exact contradiction.elim
      | .right globalHistory =>
          have contradiction : False := by
            let selection :=
              (ExactLedger.get globalHistory (K .selection)).down
            obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
              (ExactLedger.get globalHistory (K .typeAExitSixGlobal)).down
            exact selection.1
              (transfer (selection.2 representative smaller
                representativeBaseline))
          exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[107]`, exit-`(7)` split on the high-entropy first-excess arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitSevenDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenProduced)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenFree)
      history :=
  Decision.run history (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `HypostructureErdos64EG.selectedTypeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (ExactLedger.get history (K .typeAExitSixFree)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases produced :
          Graph.Strategy.Spine.HandoffProduced spineData selected.object
            packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[108]`, Type B handoff on the high-entropy first-excess exit-`(7)` arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessExitSevenHandoff
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (typeAExitSevenHandoffRow (data := spineData)).run history
    (by simp [typeAExitSevenHandoffRow, K_eq_iff])

/-- Nodes `[65]`--`[67]`, Type-B high-centre normal form after the high-entropy handoff. -/
noncomputable def selectedHighEntropyTypeAFirstExcessHandoffNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (highCentreNormalFormRow (data := spineData)).run history
    (by simp [highCentreNormalFormRow, K_eq_iff])

/-- Node `[68]`, decorated heavy-centre/degree-four split on this literal ledger. -/
noncomputable def selectedHighEntropyTypeAFirstExcessHandoffDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      ((cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])) := by
  let baseline := (cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])
  exact heavyCentreDichotomy (data := spineData) baseline
    (by simp [cubicBaselineRow, K_eq_iff])
    (by simp [cubicBaselineRow, K_eq_iff])


/-- Node `[69]`, local dichotomy on this literal heavy sibling. -/
noncomputable def selectedHighEntropyTypeAFirstExcessHeavyLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (heavyCentreLocalDichotomyRow (data := spineData)).run history
    (by simp [heavyCentreLocalDichotomyRow, K_eq_iff])


/-- `def:decorated-typeB-envelope-support` on this literal Type-B handoff residual. -/
/-- Node `[78]`, degree-four activation on this literal sibling. -/
noncomputable def selectedHighEntropyTypeAFirstExcessDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (degreeFourProfileRow (data := spineData)).run history
    (by simp [degreeFourProfileRow, K_eq_iff])


noncomputable def selectedHighEntropyTypeAFirstExcessHandoffAssignedSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff,
        K .typeAExitSevenProduced, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (typeBDecoratedAssignedSupportRow (data := spineData)).run history
    (by simp [typeBDecoratedAssignedSupportRow, K_eq_iff])

/-- Node `[110]`, route-8 residual profile on the high-entropy first-excess arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessRoute8ResidualProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenFree, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (route8ResidualProfileRow (data := spineData)).run history
    (by simp [route8ResidualProfileRow, K_eq_iff])

/-- Node `[111]`, global route-8 squeeze on the high-entropy first-excess arm. -/
noncomputable def selectedHighEntropyTypeAFirstExcessRoute8GlobalSqueeze
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (route8GlobalSqueezeRow (data := spineData)).run history
    (by simp [route8GlobalSqueezeRow, K_eq_iff])

/-- Node `[112]`, basin burden on the high-entropy first-excess route-8 residual. -/
noncomputable def selectedHighEntropyTypeAFirstExcessRoute8BasinBurden
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (route8BasinBurdenRow (data := spineData)).run history
    (by simp [route8BasinBurdenRow, K_eq_iff])

/-- Node `[113]`, large-budget deficit on the high-entropy route-8 burden ledger. -/
noncomputable def selectedHighEntropyTypeAFirstExcessRoute8LargeBudgetDeficit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8LargeBudgetDeficit, K .route8BasinBurden,
        K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (route8LargeBudgetDeficitRow (data := spineData)).run history
    (by simp [route8LargeBudgetDeficitRow, K_eq_iff])

/-- Node `[114]`, canonical carrier cores on the high-entropy route-8 residual. -/
noncomputable def selectedHighEntropyTypeAFirstExcessRoute8CarrierCore
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8LargeBudgetDeficit, K .route8BasinBurden,
        K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8CarrierCore, K .route8LargeBudgetDeficit,
        K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (route8CarrierCoreRow (data := spineData)).run history
    (by simp [route8CarrierCoreRow, K_eq_iff])

/-- Node `[115]`, the small-core collapse fact on the high-entropy route-8 residual. -/
noncomputable def selectedHighEntropyTypeAFirstExcessRoute8SmallCoreCollapse
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8CarrierCore, K .route8LargeBudgetDeficit,
        K .route8BasinBurden, K .route8GlobalSqueeze,
        K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8SmallCoreCollapse, K .route8CarrierCore,
        K .route8LargeBudgetDeficit, K .route8BasinBurden,
        K .route8GlobalSqueeze, K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleFirstExcess,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] :=
  (route8SmallCoreCollapseRow (data := spineData)).run history
    (by simp [route8SmallCoreCollapseRow, K_eq_iff])

/-- Node `[101]`: initialize the paper's exit-`(4)` peeling state and append
its finite-descent theorem on the literal low-entropy visible-entry residual. -/
noncomputable def selectedLowEntropyTypeAExitFourFiniteDescent
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAVisibleEntryClause, K .typeAVisibleEntry,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  let entered :=
    (typeASaturatedExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [typeASaturatedExitEntryRow, K_eq_iff])
  (typeAExitFourFiniteDescentRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run entered
    (by simp [typeAExitFourFiniteDescentRow, typeASaturatedExitEntryRow,
      K_eq_iff])

/-- Node `[101]`: the same labeled descent construction on the high-entropy
visible-entry residual. -/
noncomputable def selectedHighEntropyTypeAExitFourFiniteDescent
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAVisibleEntryClause, K .typeAVisibleEntry,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  let entered :=
    (typeASaturatedExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [typeASaturatedExitEntryRow, K_eq_iff])
  (typeAExitFourFiniteDescentRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run entered
    (by simp [typeAExitFourFiniteDescentRow, typeASaturatedExitEntryRow,
      K_eq_iff])

/-- Node `[93]` yes arm, visible-entry clause on the low-entropy Type A arm. -/
noncomputable def selectedLowEntropyTypeASaturatedHandoffSplitDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAVisibleEntryClause, K .typeAVisibleEntry,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffVisible)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffSilent)
      (selectedLowEntropyTypeAExitFourFiniteDescent history) :=
  let previous := selectedLowEntropyTypeAExitFourFiniteDescent history
  Decision.run previous (K .typeASaturatedHandoffVisible)
    (K .typeASaturatedHandoffSilent)
    `HypostructureErdos64EG.selectedLowEntropyTypeASaturatedHandoffSplitDichotomy
    (by
      classical
      apply Classical.choice
      have _finiteDescent := previous.get (K .typeAExitFourFiniteDescent)
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated⟩ :=
        (previous.get (K .typeASaturatedExitEntry)).down
      let piece := previous.current.object.pieceSupport
        (previous.current.object.remainderSupport packing) component
      have exactDegree : ∀ vertex ∈ piece,
          previous.current.object.degree vertex = spineData.threshold := by
        intro vertex member
        have lower : spineData.threshold ≤ previous.current.object.degree vertex :=
          le_trans previous.current.baseline
            (previous.current.object.minDegree_le_degree vertex)
        have summand : previous.current.object.degree vertex - spineData.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other =>
                previous.current.object.degree other - spineData.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      by_cases visible : Graph.ExitFour.VisibleFourUnpeeledAt piece
          spineData.threshold spineData.dischargeScale receiver peeled
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Graph.ExitFour.visibleFourUnpeeledPackage piece spineData.threshold
            spineData.dischargeScale receiver peeled visible⟩⟩⟩
      · have silent : Graph.ExitFour.SilentUnpeeledExcessAt piece
            spineData.threshold spineData.dischargeScale receiver peeled := by
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
              piece spineData.threshold spineData.dischargeScale receiver peeled
              (exactDegree receiver isReceiver.1) isReceiver saturated with
            overloaded | silent
          · exact False.elim (visible overloaded)
          · exact silent
        exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          silent⟩⟩⟩)
    (by simp [previous, selectedLowEntropyTypeAExitFourFiniteDescent,
      typeAExitFourFiniteDescentRow, typeASaturatedExitEntryRow, K_eq_iff])
    (by simp [previous, selectedLowEntropyTypeAExitFourFiniteDescent,
      typeAExitFourFiniteDescentRow, typeASaturatedExitEntryRow, K_eq_iff])

/-- Node `[101]`, saturated-handoff split on the high-entropy visible Type A arm. -/
noncomputable def selectedHighEntropyTypeASaturatedHandoffSplitDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAVisibleEntryClause, K .typeAVisibleEntry,
        K .typeAPortReturn, K .typeASaturatedReceiver,
        K .typeAReceiverRouting, K .typeALowSurplus, K .negativeSupport,
        K .netChargeNegative, K .netChargeLocalization, K .netChargeCap,
        K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffVisible)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffSilent)
      (selectedHighEntropyTypeAExitFourFiniteDescent history) :=
  let previous := selectedHighEntropyTypeAExitFourFiniteDescent history
  Decision.run previous (K .typeASaturatedHandoffVisible)
    (K .typeASaturatedHandoffSilent)
    `HypostructureErdos64EG.selectedHighEntropyTypeASaturatedHandoffSplitDichotomy
    (by
      classical
      apply Classical.choice
      have _finiteDescent := previous.get (K .typeAExitFourFiniteDescent)
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated⟩ :=
        (previous.get (K .typeASaturatedExitEntry)).down
      let piece := previous.current.object.pieceSupport
        (previous.current.object.remainderSupport packing) component
      have exactDegree : ∀ vertex ∈ piece,
          previous.current.object.degree vertex = spineData.threshold := by
        intro vertex member
        have lower : spineData.threshold ≤ previous.current.object.degree vertex :=
          le_trans previous.current.baseline
            (previous.current.object.minDegree_le_degree vertex)
        have summand : previous.current.object.degree vertex - spineData.threshold = 0 :=
          Nat.eq_zero_of_le_zero
            (zero ▸ Finset.single_le_sum
              (f := fun other =>
                previous.current.object.degree other - spineData.threshold)
              (fun _ _ => Nat.zero_le _) member)
        omega
      by_cases visible : Graph.ExitFour.VisibleFourUnpeeledAt piece
          spineData.threshold spineData.dischargeScale receiver peeled
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Graph.ExitFour.visibleFourUnpeeledPackage piece spineData.threshold
            spineData.dischargeScale receiver peeled visible⟩⟩⟩
      · have silent : Graph.ExitFour.SilentUnpeeledExcessAt piece
            spineData.threshold spineData.dischargeScale receiver peeled := by
          rcases Graph.ExitFour.visibleFourUnpeeled_or_silentUnpeeledExcess
              piece spineData.threshold spineData.dischargeScale receiver peeled
              (exactDegree receiver isReceiver.1) isReceiver saturated with
            overloaded | silent
          · exact False.elim (visible overloaded)
          · exact silent
        exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          silent⟩⟩⟩)
    (by simp [previous, selectedHighEntropyTypeAExitFourFiniteDescent,
      typeAExitFourFiniteDescentRow, typeASaturatedExitEntryRow, K_eq_iff])
    (by simp [previous, selectedHighEntropyTypeAExitFourFiniteDescent,
      typeAExitFourFiniteDescentRow, typeASaturatedExitEntryRow, K_eq_iff])

/-- Node `[101]`, exit-`(4)` split on the low-entropy visible handoff arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitFourDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFour)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFourFree)
      history :=
  Decision.run history (K .typeASaturatedHandoffExitFour)
    (K .typeASaturatedHandoffExitFourFree)
    `HypostructureErdos64EG.selectedLowEntropyTypeAVisibleExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, packageWitness⟩ :=
        (history.get (K .typeASaturatedHandoffVisible)).down
      obtain ⟨package⟩ := packageWitness
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength spineData.LengthOK) piece
              spineData.threshold receiver peeled,
            ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                spineData.threshold spineData.dischargeScale receiver
                package.outside peeled,
              witness.load = load
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inl ⟨package, occurs⟩⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inl ⟨package, occurs⟩⟩⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[101]`, exit-`(4)` split on the low-entropy silent handoff arm. -/
noncomputable def selectedLowEntropyTypeASilentExitFourDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFour)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFourFree)
      history :=
  Decision.run history (K .typeASaturatedHandoffExitFour)
    (K .typeASaturatedHandoffExitFourFree)
    `HypostructureErdos64EG.selectedLowEntropyTypeASilentExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, silent⟩ :=
        (history.get (K .typeASaturatedHandoffSilent)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength spineData.LengthOK) piece
              spineData.threshold receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
              spineData.threshold spineData.dischargeScale receiver peeled
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[101]`, exit-`(4)` split on the high-entropy visible handoff arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitFourDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFour)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFourFree)
      history :=
  Decision.run history (K .typeASaturatedHandoffExitFour)
    (K .typeASaturatedHandoffExitFourFree)
    `HypostructureErdos64EG.selectedHighEntropyTypeAVisibleExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, packageWitness⟩ :=
        (history.get (K .typeASaturatedHandoffVisible)).down
      obtain ⟨package⟩ := packageWitness
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength spineData.LengthOK) piece
              spineData.threshold receiver peeled,
            ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                spineData.threshold spineData.dischargeScale receiver
                package.outside peeled,
              witness.load = load
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inl ⟨package, occurs⟩⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inl ⟨package, occurs⟩⟩⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[101]`, exit-`(4)` split on the high-entropy silent handoff arm. -/
noncomputable def selectedHighEntropyTypeASilentExitFourDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFour)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeASaturatedHandoffExitFourFree)
      history :=
  Decision.run history (K .typeASaturatedHandoffExitFour)
    (K .typeASaturatedHandoffExitFourFree)
    `HypostructureErdos64EG.selectedHighEntropyTypeASilentExitFourDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, silent⟩ :=
        (history.get (K .typeASaturatedHandoffSilent)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases occurs :
          ∃ witness : Graph.ExitFour.Witness
              (Graph.HasCycleWithLength spineData.LengthOK) piece
              spineData.threshold receiver peeled,
            witness.load ∈ Graph.ExitFour.unpeeledExcess piece
              spineData.threshold spineData.dischargeScale receiver peeled
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present, negative,
          zero, receiver, isReceiver, peeled, peeledSubset, saturated,
          Or.inr ⟨silent, occurs⟩⟩⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])


/-- Node `[102]`, one-load peeling on the low-entropy visible exit-`(4)` arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitFourPeelingStep
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      (typeASaturatedHandoffExitFourKeys known)) :
    ExactLedger EGInput.{u} selected (typeAExitFourPeeledKeys known) :=
  typeAExitFourPeelingStepRow.run history
    (by simp [typeAExitFourPeelingStepRow, K_eq_iff])

/-- Node `[102]`, one-load peeling on the low-entropy silent exit-`(4)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitFourPeelingStep
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      (typeASaturatedHandoffExitFourKeys known)) :
    ExactLedger EGInput.{u} selected (typeAExitFourPeeledKeys known) :=
  typeAExitFourPeelingStepRow.run history
    (by simp [typeAExitFourPeelingStepRow, K_eq_iff])

/-- Node `[102]`, one-load peeling on the high-entropy visible exit-`(4)` arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitFourPeelingStep
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      (typeASaturatedHandoffExitFourKeys known)) :
    ExactLedger EGInput.{u} selected (typeAExitFourPeeledKeys known) :=
  typeAExitFourPeelingStepRow.run history
    (by simp [typeAExitFourPeelingStepRow, K_eq_iff])

/-- Node `[102]`, one-load peeling on the high-entropy silent exit-`(4)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitFourPeelingStep
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      (typeASaturatedHandoffExitFourKeys known)) :
    ExactLedger EGInput.{u} selected (typeAExitFourPeeledKeys known) :=
  typeAExitFourPeelingStepRow.run history
    (by simp [typeAExitFourPeelingStepRow, K_eq_iff])


/-- Node `[103]`, exit-`(5)` split on the low-entropy silent no-exit-`(4)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitFiveDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFiveFree)
      history :=
  typeAExitFiveDichotomy history
    (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFive) (K .typeAExitFiveFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[104]`, closes the low-entropy silent exit-`(5)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitFiveCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFive, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let selection := (ExactLedger.get history (K .selection)).down
  obtain ⟨support, replacement⟩ :=
    (ExactLedger.get history (K .typeAExitFive)).down
  exact Graph.Strategy.InterfaceReplacement.not_replacementSupport
    (Graph.MinimumDegreeAtLeast spineData.threshold) BranchState
    (Graph.minimumDegreeAtLeast_isomorphismInvariant spineData.threshold)
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    (Core.Target.ofPredicate _
      (Graph.HasCycleWithLength spineData.LengthOK))
    ((Graph.cycleTargetInterface spineData.LengthOK).coreInvariantWithPresentation
        (Graph.MinimumDegreeAtLeast spineData.threshold) BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        (Graph.minimumDegreeAtLeast_isomorphismInvariant spineData.threshold))
    (contextOfSelection selected selection.1 selection.2)
    support replacement

/-- Low-entropy silent Type A continuation after node `[104]`. -/
noncomputable def selectedLowEntropyTypeASilentExitFiveFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeASilentExitFiveDichotomy history with
  | .left exitHistory =>
      exact False.elim
        (selectedLowEntropyTypeASilentExitFiveCloses exitHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[105]`, exit-`(6)` split on the low-entropy silent no-exit-`(5)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitSixDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSix)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixFree)
      history :=
  typeAExitSixDichotomy history
    (K .typeAExitFiveFree) (K .typeAExitSix) (K .typeAExitSixFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, scope split on the low-entropy silent exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitSixScopeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixProper)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixGlobal)
      history :=
  Decision.run history (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `HypostructureErdos64EG.selectedTypeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (ExactLedger.get history (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, closes the low-entropy silent proper exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitSixProperCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixProper, K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  obtain ⟨support, replacement⟩ :=
    (ExactLedger.get history (K .typeAExitSixProper)).down
  exact (ExactLedger.get history (K .uncompressible)).down
    support replacement

/-- Node `[106]`, closes the low-entropy silent global exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitSixGlobalCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixGlobal, K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let selection := (ExactLedger.get history (K .selection)).down
  obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
    (ExactLedger.get history (K .typeAExitSixGlobal)).down
  exact selection.1
    (transfer (selection.2 representative smaller representativeBaseline))

/-- Low-entropy silent Type A continuation after node `[106]`. -/
noncomputable def selectedLowEntropyTypeASilentExitSixFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeASilentExitSixDichotomy history with
  | .left exitHistory =>
      match selectedLowEntropyTypeASilentExitSixScopeDichotomy exitHistory with
      | .left properHistory =>
          exact False.elim
            (selectedLowEntropyTypeASilentExitSixProperCloses properHistory)
      | .right globalHistory =>
          exact False.elim
            (selectedLowEntropyTypeASilentExitSixGlobalCloses globalHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[107]`, exit-`(7)` split on the low-entropy silent no-exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeASilentExitSevenDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenProduced)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenFree)
      history :=
  Decision.run history (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `HypostructureErdos64EG.selectedTypeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (ExactLedger.get history (K .typeAExitSixFree)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases produced :
          Graph.Strategy.Spine.HandoffProduced spineData selected.object
            packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[108]`, Type B handoff fact on the low-entropy silent exit-`(7)` produced arm. -/
noncomputable def selectedLowEntropyTypeASilentExitSevenHandoff
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenProduced, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeAExitSevenHandoffRow (data := spineData)).run history
    (by simp [typeAExitSevenHandoffRow, K_eq_iff])

/-- Nodes `[65]`--`[67]`, Type-B high-centre normal form on this exit-`(7)` handoff residual. -/
noncomputable def selectedLowEntropyTypeASilentHandoffNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (highCentreNormalFormRow (data := spineData)).run history
    (by simp [highCentreNormalFormRow, K_eq_iff])

/-- Node `[68]`, decorated heavy-centre/degree-four split on this literal ledger. -/
noncomputable def selectedLowEntropyTypeASilentHandoffDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      ((cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])) := by
  let baseline := (cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])
  exact heavyCentreDichotomy (data := spineData) baseline
    (by simp [cubicBaselineRow, K_eq_iff])
    (by simp [cubicBaselineRow, K_eq_iff])


/-- Node `[69]`, local dichotomy on this literal heavy sibling. -/
noncomputable def selectedLowEntropyTypeASilentHeavyLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (heavyCentreLocalDichotomyRow (data := spineData)).run history
    (by simp [heavyCentreLocalDichotomyRow, K_eq_iff])


/-- `def:decorated-typeB-envelope-support` on this literal Type-B handoff residual. -/
/-- Node `[78]`, degree-four activation on this literal sibling. -/
noncomputable def selectedLowEntropyTypeASilentDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (degreeFourProfileRow (data := spineData)).run history
    (by simp [degreeFourProfileRow, K_eq_iff])


noncomputable def selectedLowEntropyTypeASilentHandoffAssignedSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeBDecoratedAssignedSupportRow (data := spineData)).run history
    (by simp [typeBDecoratedAssignedSupportRow, K_eq_iff])

/-- Node `[111]`, route-8 global squeeze on the low-entropy silent free arm. -/
noncomputable def selectedLowEntropyTypeASilentRoute8GlobalSqueeze
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8GlobalSqueeze, K .route8ResidualProfile,
        K .typeAExitSevenFree,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (route8GlobalSqueezeRow (data := spineData)).run history
    (by simp [K_eq_iff])

/-- Node `[103]`, exit-`(5)` split on the low-entropy visible no-exit-`(4)` arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitFiveDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFiveFree)
      history :=
  typeAExitFiveDichotomy history
    (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFive) (K .typeAExitFiveFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Low-entropy visible Type A continuation after node `[104]`. -/
noncomputable def selectedLowEntropyTypeAVisibleExitFiveFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeAVisibleExitFiveDichotomy history with
  | .left exitHistory =>
      have contradiction : False := by
        let uncompressible :=
          (ExactLedger.get exitHistory (K .uncompressible)).down
        obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
          _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
          _noExitFour, support, compression⟩ :=
          (ExactLedger.get exitHistory (K .typeAExitFive)).down
        exact uncompressible support compression
      exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[105]`, exit-`(6)` split on the low-entropy visible no-exit-`(5)` arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitSixDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSix)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixFree)
      history :=
  typeAExitSixDichotomy history
    (K .typeAExitFiveFree) (K .typeAExitSix) (K .typeAExitSixFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, scope split on the low-entropy visible exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitSixScopeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixProper)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixGlobal)
      history :=
  Decision.run history (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `HypostructureErdos64EG.selectedTypeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (ExactLedger.get history (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Low-entropy visible Type A continuation after node `[106]`. -/
noncomputable def selectedLowEntropyTypeAVisibleExitSixFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeAVisibleExitSixDichotomy history with
  | .left exitHistory =>
      match selectedLowEntropyTypeAVisibleExitSixScopeDichotomy exitHistory with
      | .left properHistory =>
          have contradiction : False := by
            obtain ⟨support, replacement⟩ :=
              (ExactLedger.get properHistory (K .typeAExitSixProper)).down
            exact (ExactLedger.get properHistory (K .uncompressible)).down
              support replacement
          exact contradiction.elim
      | .right globalHistory =>
          have contradiction : False := by
            let selection :=
              (ExactLedger.get globalHistory (K .selection)).down
            obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
              (ExactLedger.get globalHistory (K .typeAExitSixGlobal)).down
            exact selection.1
              (transfer (selection.2 representative smaller
                representativeBaseline))
          exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[107]`, exit-`(7)` split on the low-entropy visible no-exit-`(6)` arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitSevenDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenProduced)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenFree)
      history :=
  Decision.run history (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `HypostructureErdos64EG.selectedTypeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (ExactLedger.get history (K .typeAExitSixFree)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases produced :
          Graph.Strategy.Spine.HandoffProduced spineData selected.object
            packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[108]`, Type B handoff fact on the low-entropy visible exit-`(7)` produced arm. -/
noncomputable def selectedLowEntropyTypeAVisibleExitSevenHandoff
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenProduced, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeAExitSevenHandoffRow (data := spineData)).run history
    (by simp [typeAExitSevenHandoffRow, K_eq_iff])

/-- Nodes `[65]`--`[67]`, Type-B high-centre normal form on this exit-`(7)` handoff residual. -/
noncomputable def selectedLowEntropyTypeAVisibleHandoffNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (highCentreNormalFormRow (data := spineData)).run history
    (by simp [highCentreNormalFormRow, K_eq_iff])

/-- Node `[68]`, decorated heavy-centre/degree-four split on this literal ledger. -/
noncomputable def selectedLowEntropyTypeAVisibleHandoffDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      ((cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])) := by
  let baseline := (cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])
  exact heavyCentreDichotomy (data := spineData) baseline
    (by simp [cubicBaselineRow, K_eq_iff])
    (by simp [cubicBaselineRow, K_eq_iff])


/-- Node `[69]`, local dichotomy on this literal heavy sibling. -/
noncomputable def selectedLowEntropyTypeAVisibleHeavyLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (heavyCentreLocalDichotomyRow (data := spineData)).run history
    (by simp [heavyCentreLocalDichotomyRow, K_eq_iff])


/-- `def:decorated-typeB-envelope-support` on this literal Type-B handoff residual. -/
/-- Node `[78]`, degree-four activation on this literal sibling. -/
noncomputable def selectedLowEntropyTypeAVisibleDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (degreeFourProfileRow (data := spineData)).run history
    (by simp [degreeFourProfileRow, K_eq_iff])


noncomputable def selectedLowEntropyTypeAVisibleHandoffAssignedSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeBDecoratedAssignedSupportRow (data := spineData)).run history
    (by simp [typeBDecoratedAssignedSupportRow, K_eq_iff])

noncomputable def selectedHighEntropyTypeASilentExitFiveDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFiveFree)
      history :=
  typeAExitFiveDichotomy history
    (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFive) (K .typeAExitFiveFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[104]`, closes the high-entropy silent exit-`(5)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitFiveCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFive, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let selection := (ExactLedger.get history (K .selection)).down
  obtain ⟨support, replacement⟩ :=
    (ExactLedger.get history (K .typeAExitFive)).down
  exact Graph.Strategy.InterfaceReplacement.not_replacementSupport
    (Graph.MinimumDegreeAtLeast spineData.threshold) BranchState
    (Graph.minimumDegreeAtLeast_isomorphismInvariant spineData.threshold)
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    (Core.Target.ofPredicate _
      (Graph.HasCycleWithLength spineData.LengthOK))
    ((Graph.cycleTargetInterface spineData.LengthOK).coreInvariantWithPresentation
        (Graph.MinimumDegreeAtLeast spineData.threshold) BranchState
        Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
        (Graph.minimumDegreeAtLeast_isomorphismInvariant spineData.threshold))
    (contextOfSelection selected selection.1 selection.2)
    support replacement

/-- High-entropy silent Type A continuation after node `[104]`. -/
noncomputable def selectedHighEntropyTypeASilentExitFiveFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedHighEntropyTypeASilentExitFiveDichotomy history with
  | .left exitHistory =>
      exact False.elim
        (selectedHighEntropyTypeASilentExitFiveCloses exitHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[105]`, exit-`(6)` split on the high-entropy silent no-exit-`(5)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitSixDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSix)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixFree)
      history :=
  typeAExitSixDichotomy history
    (K .typeAExitFiveFree) (K .typeAExitSix) (K .typeAExitSixFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, scope split on the high-entropy silent exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitSixScopeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixProper)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixGlobal)
      history :=
  Decision.run history (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `HypostructureErdos64EG.selectedTypeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (ExactLedger.get history (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, closes the high-entropy silent proper exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitSixProperCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixProper, K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  obtain ⟨support, replacement⟩ :=
    (ExactLedger.get history (K .typeAExitSixProper)).down
  exact (ExactLedger.get history (K .uncompressible)).down
    support replacement

/-- Node `[106]`, closes the high-entropy silent global exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitSixGlobalCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixGlobal, K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let selection := (ExactLedger.get history (K .selection)).down
  obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
    (ExactLedger.get history (K .typeAExitSixGlobal)).down
  exact selection.1
    (transfer (selection.2 representative smaller representativeBaseline))

/-- High-entropy silent Type A continuation after node `[106]`. -/
noncomputable def selectedHighEntropyTypeASilentExitSixFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedHighEntropyTypeASilentExitSixDichotomy history with
  | .left exitHistory =>
      match selectedHighEntropyTypeASilentExitSixScopeDichotomy exitHistory with
      | .left properHistory =>
          exact False.elim
            (selectedHighEntropyTypeASilentExitSixProperCloses properHistory)
      | .right globalHistory =>
          exact False.elim
            (selectedHighEntropyTypeASilentExitSixGlobalCloses globalHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[107]`, exit-`(7)` split on the high-entropy silent no-exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeASilentExitSevenDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenProduced)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenFree)
      history :=
  Decision.run history (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `HypostructureErdos64EG.selectedTypeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (ExactLedger.get history (K .typeAExitSixFree)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases produced :
          Graph.Strategy.Spine.HandoffProduced spineData selected.object
            packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[108]`, Type B handoff fact on the high-entropy silent exit-`(7)` produced arm. -/
noncomputable def selectedHighEntropyTypeASilentExitSevenHandoff
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenProduced, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeAExitSevenHandoffRow (data := spineData)).run history
    (by simp [typeAExitSevenHandoffRow, K_eq_iff])

/-- Nodes `[65]`--`[67]`, Type-B high-centre normal form on this exit-`(7)` handoff residual. -/
noncomputable def selectedHighEntropyTypeASilentHandoffNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (highCentreNormalFormRow (data := spineData)).run history
    (by simp [highCentreNormalFormRow, K_eq_iff])

/-- Node `[68]`, decorated heavy-centre/degree-four split on this literal ledger. -/
noncomputable def selectedHighEntropyTypeASilentHandoffDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      ((cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])) := by
  let baseline := (cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])
  exact heavyCentreDichotomy (data := spineData) baseline
    (by simp [cubicBaselineRow, K_eq_iff])
    (by simp [cubicBaselineRow, K_eq_iff])


/-- Node `[69]`, local dichotomy on this literal heavy sibling. -/
noncomputable def selectedHighEntropyTypeASilentHeavyLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (heavyCentreLocalDichotomyRow (data := spineData)).run history
    (by simp [heavyCentreLocalDichotomyRow, K_eq_iff])


/-- `def:decorated-typeB-envelope-support` on this literal Type-B handoff residual. -/
/-- Node `[78]`, degree-four activation on this literal sibling. -/
noncomputable def selectedHighEntropyTypeASilentDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (degreeFourProfileRow (data := spineData)).run history
    (by simp [degreeFourProfileRow, K_eq_iff])


noncomputable def selectedHighEntropyTypeASilentHandoffAssignedSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeBDecoratedAssignedSupportRow (data := spineData)).run history
    (by simp [typeBDecoratedAssignedSupportRow, K_eq_iff])

/-- Node `[111]`, route-8 global squeeze on the high-entropy silent free arm. -/
noncomputable def selectedHighEntropyTypeASilentRoute8GlobalSqueeze
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .route8ResidualProfile, 
        K .typeAExitSevenFree, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .route8GlobalSqueeze, K .route8ResidualProfile,
        K .typeAExitSevenFree,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffSilent, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (route8GlobalSqueezeRow (data := spineData)).run history
    (by simp [K_eq_iff])

/-- Node `[103]`, exit-`(5)` split on the high-entropy visible no-exit-`(4)` arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitFiveDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFive)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitFiveFree)
      history :=
  typeAExitFiveDichotomy history
    (K .typeASaturatedHandoffExitFourFree)
    (K .typeAExitFive) (K .typeAExitFiveFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- High-entropy visible Type A continuation after node `[104]`. -/
noncomputable def selectedHighEntropyTypeAVisibleExitFiveFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedHighEntropyTypeAVisibleExitFiveDichotomy history with
  | .left exitHistory =>
      have contradiction : False := by
        let uncompressible :=
          (ExactLedger.get exitHistory (K .uncompressible)).down
        obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
          _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
          _noExitFour, support, compression⟩ :=
          (ExactLedger.get exitHistory (K .typeAExitFive)).down
        exact uncompressible support compression
      exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[105]`, exit-`(6)` split on the high-entropy visible no-exit-`(5)` arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitSixDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSix)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixFree)
      history :=
  typeAExitSixDichotomy history
    (K .typeAExitFiveFree) (K .typeAExitSix) (K .typeAExitSixFree)
    (fun fact => fact.down)
    (fun value => ⟨value⟩)
    (fun value => ⟨value⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[106]`, scope split on the high-entropy visible exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitSixScopeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSix, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixProper)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSixGlobal)
      history :=
  Decision.run history (K .typeAExitSixProper) (K .typeAExitSixGlobal)
    `HypostructureErdos64EG.selectedTypeAExitSixScopeDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
        _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
        _noExitFour, _noCompression, _presented, _supportEq, delocalizes⟩ :=
        (ExactLedger.get history (K .typeAExitSix)).down
      obtain ⟨delocalization⟩ := delocalizes
      rcases delocalization.localize with proper | global
      · exact ⟨.inl ⟨⟨_, proper⟩⟩⟩
      · exact ⟨.inr ⟨global⟩⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- High-entropy visible Type A continuation after node `[106]`. -/
noncomputable def selectedHighEntropyTypeAVisibleExitSixFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedHighEntropyTypeAVisibleExitSixDichotomy history with
  | .left exitHistory =>
      match selectedHighEntropyTypeAVisibleExitSixScopeDichotomy exitHistory with
      | .left properHistory =>
          have contradiction : False := by
            obtain ⟨support, replacement⟩ :=
              (ExactLedger.get properHistory (K .typeAExitSixProper)).down
            exact (ExactLedger.get properHistory (K .uncompressible)).down
              support replacement
          exact contradiction.elim
      | .right globalHistory =>
          have contradiction : False := by
            let selection :=
              (ExactLedger.get globalHistory (K .selection)).down
            obtain ⟨representative, smaller, representativeBaseline, transfer⟩ :=
              (ExactLedger.get globalHistory (K .typeAExitSixGlobal)).down
            exact selection.1
              (transfer (selection.2 representative smaller
                representativeBaseline))
          exact contradiction.elim
  | .right freeHistory =>
      exact freeHistory

/-- Node `[107]`, exit-`(7)` split on the high-entropy visible no-exit-`(6)` arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitSevenDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenProduced)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeAExitSevenFree)
      history :=
  Decision.run history (K .typeAExitSevenProduced) (K .typeAExitSevenFree)
    `HypostructureErdos64EG.selectedTypeAExitSevenDichotomy
    (by
      classical
      apply Classical.choice
      obtain ⟨packing, valid, maximal, component, present, negative, zero,
        receiver, isReceiver, peeled, peeledSubset, saturated, noExitFour,
        noCompression, noDelocalization⟩ :=
        (ExactLedger.get history (K .typeAExitSixFree)).down
      let piece := selected.object.pieceSupport
        (selected.object.remainderSupport packing) component
      by_cases produced :
          Graph.Strategy.Spine.HandoffProduced spineData selected.object
            packing piece
      · exact ⟨.inl ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩
      · exact ⟨.inr ⟨⟨packing, valid, maximal, component, present,
          negative, zero, receiver, isReceiver, peeled, peeledSubset,
          saturated, noExitFour, noCompression, noDelocalization, produced⟩⟩⟩)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[108]`, Type B handoff fact on the high-entropy visible exit-`(7)` produced arm. -/
noncomputable def selectedHighEntropyTypeAVisibleExitSevenHandoff
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenProduced, K .typeAExitSixFree,
        K .typeAExitFiveFree, K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeAExitSevenHandoffRow (data := spineData)).run history
    (by simp [typeAExitSevenHandoffRow, K_eq_iff])

/-- Nodes `[65]`--`[67]`, Type-B high-centre normal form on this exit-`(7)` handoff residual. -/
noncomputable def selectedHighEntropyTypeAVisibleHandoffNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (highCentreNormalFormRow (data := spineData)).run history
    (by simp [highCentreNormalFormRow, K_eq_iff])

/-- Node `[68]`, decorated heavy-centre/degree-four split on this literal ledger. -/
noncomputable def selectedHighEntropyTypeAVisibleHandoffDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      ((cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])) := by
  let baseline := (cubicBaselineRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by simp [cubicBaselineRow, K_eq_iff])
  exact heavyCentreDichotomy (data := spineData) baseline
    (by simp [cubicBaselineRow, K_eq_iff])
    (by simp [cubicBaselineRow, K_eq_iff])


/-- Node `[69]`, local dichotomy on this literal heavy sibling. -/
noncomputable def selectedHighEntropyTypeAVisibleHeavyLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (heavyCentreLocalDichotomyRow (data := spineData)).run history
    (by simp [heavyCentreLocalDichotomyRow, K_eq_iff])


/-- `def:decorated-typeB-envelope-support` on this literal Type-B handoff residual. -/
/-- Node `[78]`, degree-four activation on this literal sibling. -/
noncomputable def selectedHighEntropyTypeAVisibleDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .typeBDegreeFourCentres, K .cubicBaseline, K .highCentreNormalForm, K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (degreeFourProfileRow (data := spineData)).run history
    (by simp [degreeFourProfileRow, K_eq_iff])


noncomputable def selectedHighEntropyTypeAVisibleHandoffAssignedSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDecoratedAssignedSupport, K .typeAExitSevenHandoff, K .typeAExitSevenProduced,
        K .typeAExitSixFree, K .typeAExitFiveFree,
        K .typeASaturatedHandoffExitFourFree,
        K .typeASaturatedHandoffVisible, K .typeAExitFourFiniteDescent,
        K .typeASaturatedExitEntry, K .typeAVisibleEntryClause,
        K .typeAVisibleEntry, K .typeAPortReturn,
        K .typeASaturatedReceiver, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeBDecoratedAssignedSupportRow (data := spineData)).run history
    (by simp [typeBDecoratedAssignedSupportRow, K_eq_iff])


/-- Node `[68]`, normal form on the low-entropy Type B arm. -/
noncomputable def selectedLowEntropyTypeBNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (highCentreNormalForm (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [highCentreNormalForm, K_eq_iff])

/-- Node `[68]`, heavy-centre split on the low-entropy Type B arm. -/

/-- Node `[68]`, normal form on the high-entropy Type B arm. -/
noncomputable def selectedHighEntropyTypeBNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (highCentreNormalForm (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [highCentreNormalForm, K_eq_iff])

/-- Node `[68]`, heavy-centre split on the high-entropy Type B arm. -/

/-- Node `[69]`, local heavy-centre dichotomy on the low-entropy Type B heavy arm. -/
noncomputable def selectedLowEntropyTypeBLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (heavyCentreLocalDichotomy (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [heavyCentreLocalDichotomy, K_eq_iff])

/-- Node `[70]`, fan certificate cap on the low-entropy Type B heavy arm. -/
noncomputable def selectedLowEntropyTypeBHeavyFanCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let afterLocal := selectedLowEntropyTypeBLocalDichotomy history
  exact
    (fanCertificateCap (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterLocal (by
        simp [fanCertificateCap, selectedLowEntropyTypeBLocalDichotomy,
          K_eq_iff])

/-- Node `[70]`, fan certificate cap on the low-entropy Type B degree-four arm. -/
noncomputable def selectedLowEntropyTypeBDegreeFourFanCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (fanCertificateCap (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [fanCertificateCap, K_eq_iff])

/-- Nodes `[78]`--`[79]`, degree-four profile on the low-entropy Type B arm. -/
noncomputable def selectedLowEntropyTypeBDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let afterCap := selectedLowEntropyTypeBDegreeFourFanCap history
  exact
    (degreeFourProfile (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterCap (by
        simp [degreeFourProfile, selectedLowEntropyTypeBDegreeFourFanCap,
          K_eq_iff])

/-- Node `[69]`, local heavy-centre dichotomy on the high-entropy Type B heavy arm. -/
noncomputable def selectedHighEntropyTypeBLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (heavyCentreLocalDichotomy (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [heavyCentreLocalDichotomy, K_eq_iff])

/-- Node `[70]`, fan certificate cap on the high-entropy Type B heavy arm. -/
noncomputable def selectedHighEntropyTypeBHeavyFanCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterLocal := selectedHighEntropyTypeBLocalDichotomy history
  exact
    (fanCertificateCap (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterLocal (by
        simp [fanCertificateCap, selectedHighEntropyTypeBLocalDichotomy,
          K_eq_iff])

/-- Node `[70]`, fan certificate cap on the high-entropy Type B degree-four arm. -/
noncomputable def selectedHighEntropyTypeBDegreeFourFanCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (fanCertificateCap (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [fanCertificateCap, K_eq_iff])

/-- Nodes `[78]`--`[79]`, degree-four profile on the high-entropy Type B arm. -/
noncomputable def selectedHighEntropyTypeBDegreeFourProfile
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterCap := selectedHighEntropyTypeBDegreeFourFanCap history
  exact
    (degreeFourProfile (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      afterCap (by
        simp [degreeFourProfile, selectedHighEntropyTypeBDegreeFourFanCap,
          K_eq_iff])

/-- Node `[71]`, certificate split on the low-entropy Type B heavy arm. -/
noncomputable def selectedLowEntropyTypeBFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      history :=
  fanCertificateDichotomy (data := spineData) history
    (K .typeBHighSurplus) (K .fanCertificateMarked)
    (K .fanCertificateResidual)
    (fun fact => fact.down)
    (fun marked => ⟨marked⟩)
    (fun residual => ⟨residual⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[70]`--`[71]`, certificate split after the low-entropy Type B heavy cap row. -/
noncomputable def selectedLowEntropyTypeBHeavyFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      (selectedLowEntropyTypeBHeavyFanCap history) :=
  selectedLowEntropyTypeBFanCertificateDichotomy
    (selectedLowEntropyTypeBHeavyFanCap history)

/-- Node `[75]`, bridge mass on the low-entropy fan-certificate residual arm. -/
noncomputable def selectedLowEntropyTypeBCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .fanCertificateResidual) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[72]`, direct-cycle split on the low-entropy Type B heavy marked arm. -/
noncomputable def selectedLowEntropyTypeBDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycle)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycleFree)
      history :=
  directCycleDichotomy (data := spineData) history
    (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun cycle => ⟨cycle⟩)
    (fun free => ⟨free⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[72]`, closing the direct-cycle arm on the low-entropy Type B heavy path. -/
noncomputable def selectedLowEntropyTypeBDirectCycleCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycle, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let selectedFact := ExactLedger.get history (K .selection)
  let cycleFact := ExactLedger.get history (K .typeBDirectCycle)
  obtain ⟨packing, valid, _maximal, _component, _present, _charge, _positive,
    _centre, _member, _high, directCycle⟩ := cycleFact.down
  exact selectedFact.down.1
    (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
      valid directCycle)

/-- Node `[72]`, low-entropy Type B heavy marked arm reduced to the cycle-free survivor. -/
noncomputable def selectedLowEntropyTypeBDirectCycleFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeBDirectCycleDichotomy history with
  | .left cycleHistory =>
      exact False.elim (selectedLowEntropyTypeBDirectCycleCloses cycleHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[72]`, B2 assignment split on the low-entropy Type B heavy path. -/
noncomputable def selectedLowEntropyTypeBB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      history :=
  b2AssignmentDichotomy (data := spineData) history
    (K .typeBB2Choice) (K .typeBOverlapObstruction)
    (K .typeBDirectCycleFree)
    (fun fact => fact.down)
    (fun choice => ⟨choice⟩)
    (fun obstruction => ⟨obstruction⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[72]`, B2 assignment after reducing the low-entropy Type B heavy marked arm. -/
noncomputable def selectedLowEntropyTypeBB2AssignmentAfterDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      (selectedLowEntropyTypeBDirectCycleFree history) :=
  selectedLowEntropyTypeBB2AssignmentDichotomy
    (selectedLowEntropyTypeBDirectCycleFree history)

/-- Node `[73]`, bridge mass on the low-entropy Type B heavy overlap-obstruction arm. -/
noncomputable def selectedLowEntropyTypeBOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .typeBOverlapObstruction) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[71]`, certificate split on the high-entropy Type B heavy arm. -/
noncomputable def selectedHighEntropyTypeBFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      history :=
  fanCertificateDichotomy (data := spineData) history
    (K .typeBHighSurplus) (K .fanCertificateMarked)
    (K .fanCertificateResidual)
    (fun fact => fact.down)
    (fun marked => ⟨marked⟩)
    (fun residual => ⟨residual⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[70]`--`[71]`, certificate split after the high-entropy Type B heavy cap row. -/
noncomputable def selectedHighEntropyTypeBHeavyFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      (selectedHighEntropyTypeBHeavyFanCap history) :=
  selectedHighEntropyTypeBFanCertificateDichotomy
    (selectedHighEntropyTypeBHeavyFanCap history)

/-- Node `[75]`, bridge mass on the high-entropy fan-certificate residual arm. -/
noncomputable def selectedHighEntropyTypeBCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .fanCertificateResidual) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[72]`, direct-cycle split on the high-entropy Type B heavy marked arm. -/
noncomputable def selectedHighEntropyTypeBDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycle)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycleFree)
      history :=
  directCycleDichotomy (data := spineData) history
    (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun cycle => ⟨cycle⟩)
    (fun free => ⟨free⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[72]`, closing the direct-cycle arm on the high-entropy Type B heavy path. -/
noncomputable def selectedHighEntropyTypeBDirectCycleCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycle, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let selectedFact := ExactLedger.get history (K .selection)
  let cycleFact := ExactLedger.get history (K .typeBDirectCycle)
  obtain ⟨packing, valid, _maximal, _component, _present, _charge, _positive,
    _centre, _member, _high, directCycle⟩ := cycleFact.down
  exact selectedFact.down.1
    (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
      valid directCycle)

/-- Node `[72]`, high-entropy Type B heavy marked arm reduced to the cycle-free survivor. -/
noncomputable def selectedHighEntropyTypeBDirectCycleFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedHighEntropyTypeBDirectCycleDichotomy history with
  | .left cycleHistory =>
      exact False.elim (selectedHighEntropyTypeBDirectCycleCloses cycleHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[72]`, B2 assignment split on the high-entropy Type B heavy path. -/
noncomputable def selectedHighEntropyTypeBB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      history :=
  b2AssignmentDichotomy (data := spineData) history
    (K .typeBB2Choice) (K .typeBOverlapObstruction)
    (K .typeBDirectCycleFree)
    (fun fact => fact.down)
    (fun choice => ⟨choice⟩)
    (fun obstruction => ⟨obstruction⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[72]`, B2 assignment after reducing the high-entropy Type B heavy marked arm. -/
noncomputable def selectedHighEntropyTypeBB2AssignmentAfterDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      (selectedHighEntropyTypeBDirectCycleFree history) :=
  selectedHighEntropyTypeBB2AssignmentDichotomy
    (selectedHighEntropyTypeBDirectCycleFree history)

/-- Node `[73]`, bridge mass on the high-entropy Type B heavy overlap-obstruction arm. -/
noncomputable def selectedHighEntropyTypeBOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .typeBOverlapObstruction) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[80]`, certificate split on the low-entropy Type B degree-four arm. -/
noncomputable def selectedLowEntropyDegreeFourFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      history :=
  fanCertificateDichotomy (data := spineData) history
    (K .typeBHighSurplus) (K .fanCertificateMarked)
    (K .fanCertificateResidual)
    (fun fact => fact.down)
    (fun marked => ⟨marked⟩)
    (fun residual => ⟨residual⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[78]`--`[80]`, certificate split after the low-entropy degree-four profile row. -/
noncomputable def selectedLowEntropyDegreeFourProfileFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      (selectedLowEntropyTypeBDegreeFourProfile history) :=
  selectedLowEntropyDegreeFourFanCertificateDichotomy
    (selectedLowEntropyTypeBDegreeFourProfile history)

/-- Node `[84]`, bridge mass on the low-entropy degree-four certificate-residual arm. -/
noncomputable def selectedLowEntropyDegreeFourCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .fanCertificateResidual) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[81]`, direct-cycle split on the low-entropy Type B degree-four marked arm. -/
noncomputable def selectedLowEntropyDegreeFourDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycle)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycleFree)
      history :=
  directCycleDichotomy (data := spineData) history
    (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun cycle => ⟨cycle⟩)
    (fun free => ⟨free⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[81]`, closing the direct-cycle arm on the low-entropy degree-four path. -/
noncomputable def selectedLowEntropyDegreeFourDirectCycleCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycle, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let selectedFact := ExactLedger.get history (K .selection)
  let cycleFact := ExactLedger.get history (K .typeBDirectCycle)
  obtain ⟨packing, valid, _maximal, _component, _present, _charge, _positive,
    _centre, _member, _high, directCycle⟩ := cycleFact.down
  exact selectedFact.down.1
    (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
      valid directCycle)

/-- Node `[81]`, low-entropy degree-four marked arm reduced to the cycle-free survivor. -/
noncomputable def selectedLowEntropyDegreeFourDirectCycleFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyDegreeFourDirectCycleDichotomy history with
  | .left cycleHistory =>
      exact False.elim (selectedLowEntropyDegreeFourDirectCycleCloses cycleHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[81]`, B2 assignment split on the low-entropy degree-four path. -/
noncomputable def selectedLowEntropyDegreeFourB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      history :=
  b2AssignmentDichotomy (data := spineData) history
    (K .typeBB2Choice) (K .typeBOverlapObstruction)
    (K .typeBDirectCycleFree)
    (fun fact => fact.down)
    (fun choice => ⟨choice⟩)
    (fun obstruction => ⟨obstruction⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[81]`, B2 assignment after reducing the low-entropy degree-four marked arm. -/
noncomputable def selectedLowEntropyDegreeFourB2AssignmentAfterDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      (selectedLowEntropyDegreeFourDirectCycleFree history) :=
  selectedLowEntropyDegreeFourB2AssignmentDichotomy
    (selectedLowEntropyDegreeFourDirectCycleFree history)

/-- Node `[83]`, bridge mass on the low-entropy degree-four overlap-obstruction arm. -/
noncomputable def selectedLowEntropyDegreeFourOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .typeBOverlapObstruction) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[80]`, certificate split on the high-entropy Type B degree-four arm. -/
noncomputable def selectedHighEntropyDegreeFourFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      history :=
  fanCertificateDichotomy (data := spineData) history
    (K .typeBHighSurplus) (K .fanCertificateMarked)
    (K .fanCertificateResidual)
    (fun fact => fact.down)
    (fun marked => ⟨marked⟩)
    (fun residual => ⟨residual⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[78]`--`[80]`, certificate split after the high-entropy degree-four profile row. -/
noncomputable def selectedHighEntropyDegreeFourProfileFanCertificateDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateMarked)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .fanCertificateResidual)
      (selectedHighEntropyTypeBDegreeFourProfile history) :=
  selectedHighEntropyDegreeFourFanCertificateDichotomy
    (selectedHighEntropyTypeBDegreeFourProfile history)

/-- Node `[84]`, bridge mass on the high-entropy degree-four certificate-residual arm. -/
noncomputable def selectedHighEntropyDegreeFourCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .fanCertificateResidual) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Node `[81]`, direct-cycle split on the high-entropy Type B degree-four marked arm. -/
noncomputable def selectedHighEntropyDegreeFourDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycle)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDirectCycleFree)
      history :=
  directCycleDichotomy (data := spineData) history
    (K .typeBDirectCycle) (K .typeBDirectCycleFree)
    (K .typeBHighSurplus)
    (fun fact => fact.down)
    (fun cycle => ⟨cycle⟩)
    (fun free => ⟨free⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[81]`, closing the direct-cycle arm on the high-entropy degree-four path. -/
noncomputable def selectedHighEntropyDegreeFourDirectCycleCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycle, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let selectedFact := ExactLedger.get history (K .selection)
  let cycleFact := ExactLedger.get history (K .typeBDirectCycle)
  obtain ⟨packing, valid, _maximal, _component, _present, _charge, _positive,
    _centre, _member, _high, directCycle⟩ := cycleFact.down
  exact selectedFact.down.1
    (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
      valid directCycle)

/-- Node `[81]`, high-entropy degree-four marked arm reduced to the cycle-free survivor. -/
noncomputable def selectedHighEntropyDegreeFourDirectCycleFree
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedHighEntropyDegreeFourDirectCycleDichotomy history with
  | .left cycleHistory =>
      exact False.elim (selectedHighEntropyDegreeFourDirectCycleCloses cycleHistory)
  | .right freeHistory =>
      exact freeHistory

/-- Node `[81]`, B2 assignment split on the high-entropy degree-four path. -/
noncomputable def selectedHighEntropyDegreeFourB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      history :=
  b2AssignmentDichotomy (data := spineData) history
    (K .typeBB2Choice) (K .typeBOverlapObstruction)
    (K .typeBDirectCycleFree)
    (fun fact => fact.down)
    (fun choice => ⟨choice⟩)
    (fun obstruction => ⟨obstruction⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[81]`, B2 assignment after reducing the high-entropy degree-four marked arm. -/
noncomputable def selectedHighEntropyDegreeFourB2AssignmentAfterDirectCycleDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBB2Choice)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBOverlapObstruction)
      (selectedHighEntropyDegreeFourDirectCycleFree history) :=
  selectedHighEntropyDegreeFourB2AssignmentDichotomy
    (selectedHighEntropyDegreeFourDirectCycleFree history)

/-- Node `[83]`, bridge mass on the high-entropy degree-four overlap-obstruction arm. -/
noncomputable def selectedHighEntropyDegreeFourOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (bridgeFanMass (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .typeBOverlapObstruction) (by simp [K_eq_iff])).run
    history (by simp [bridgeFanMass, K_eq_iff])

/-- Nodes `[74]`--`[76]`, B2-success charge ledger on the low-entropy heavy path. -/
noncomputable def selectedLowEntropyTypeBB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let h1 :=
    (hybridEntry (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [hybridEntry, K_eq_iff])
  let h2 :=
    (disjointPostLedgerComponents (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by simp [disjointPostLedgerComponents, hybridEntry, K_eq_iff])
  let h3 :=
    (typeBSelectedFanCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [typeBSelectedFanCharge, disjointPostLedgerComponents,
          hybridEntry, K_eq_iff])
  exact
    (typeBExclusionCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [typeBExclusionCharge, typeBSelectedFanCharge,
          disjointPostLedgerComponents, hybridEntry, K_eq_iff])

/-- Node `[76]`, exclusion split after the low-entropy heavy B2 charge ledger. -/
noncomputable def selectedLowEntropyTypeBExclusionDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExcluded)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedLowEntropyTypeBB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedLowEntropyTypeBB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBExclusionCharge)
    (K .typeBExcluded) (K .typeBExclusionResidual)
    (fun charge => charge.down)
    (fun contradiction => ⟨False.elim contradiction⟩)
    (fun residual => ⟨residual⟩)
    (fun ledger => by
      obtain ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post, _groupedCoverage⟩ := ledger.down
      exact ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post⟩)
    (by
      simp [selectedLowEntropyTypeBB2ExclusionCharge, typeBExclusionCharge,
        typeBSelectedFanCharge, disjointPostLedgerComponents, hybridEntry,
        K_eq_iff])
    (by
      simp [selectedLowEntropyTypeBB2ExclusionCharge, typeBExclusionCharge,
        typeBSelectedFanCharge, disjointPostLedgerComponents, hybridEntry,
        K_eq_iff])

/-- Node `[76]`, closing the excluded arm on the low-entropy heavy Type B path. -/
noncomputable def selectedLowEntropyTypeBExcludedCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExcluded, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let closedHistory :=
    closeImpossible history (K .typeBExcluded)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[76]`, low-entropy heavy B2-success arm reduced to the exclusion residual survivor. -/
noncomputable def selectedLowEntropyTypeBExclusionResidual
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyTypeBExclusionDichotomy history with
  | .left nonnegativeHistory =>
      exact False.elim (selectedLowEntropyTypeBExcludedCloses nonnegativeHistory)
  | .right residualHistory =>
      exact residualHistory

/-- Nodes `[74]`--`[76]`, B2-success charge ledger on the high-entropy heavy path. -/
noncomputable def selectedHighEntropyTypeBB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let h1 :=
    (hybridEntry (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [hybridEntry, K_eq_iff])
  let h2 :=
    (disjointPostLedgerComponents (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by simp [disjointPostLedgerComponents, hybridEntry, K_eq_iff])
  let h3 :=
    (typeBSelectedFanCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [typeBSelectedFanCharge, disjointPostLedgerComponents,
          hybridEntry, K_eq_iff])
  exact
    (typeBExclusionCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [typeBExclusionCharge, typeBSelectedFanCharge,
          disjointPostLedgerComponents, hybridEntry, K_eq_iff])

/-- Node `[76]`, exclusion split after the high-entropy heavy B2 charge ledger. -/
noncomputable def selectedHighEntropyTypeBExclusionDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExcluded)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedHighEntropyTypeBB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedHighEntropyTypeBB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBExclusionCharge)
    (K .typeBExcluded) (K .typeBExclusionResidual)
    (fun charge => charge.down)
    (fun contradiction => ⟨False.elim contradiction⟩)
    (fun residual => ⟨residual⟩)
    (fun ledger => by
      obtain ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post, _groupedCoverage⟩ := ledger.down
      exact ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post⟩)
    (by
      simp [selectedHighEntropyTypeBB2ExclusionCharge, typeBExclusionCharge,
        typeBSelectedFanCharge, disjointPostLedgerComponents, hybridEntry,
        K_eq_iff])
    (by
      simp [selectedHighEntropyTypeBB2ExclusionCharge, typeBExclusionCharge,
        typeBSelectedFanCharge, disjointPostLedgerComponents, hybridEntry,
        K_eq_iff])

/-- Node `[76]`, closing the excluded arm on the high-entropy heavy Type B path. -/
noncomputable def selectedHighEntropyTypeBExcludedCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExcluded, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let closedHistory :=
    closeImpossible history (K .typeBExcluded)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[76]`, high-entropy heavy B2-success arm reduced to the exclusion residual survivor. -/
noncomputable def selectedHighEntropyTypeBExclusionResidual
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedHighEntropyTypeBExclusionDichotomy history with
  | .left nonnegativeHistory =>
      exact False.elim (selectedHighEntropyTypeBExcludedCloses nonnegativeHistory)
  | .right residualHistory =>
      exact residualHistory

/-- Nodes `[82]`--`[85]`, B2-success charge ledger on the low-entropy degree-four path. -/
noncomputable def selectedLowEntropyDegreeFourB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let h1 :=
    (hybridEntry (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [hybridEntry, K_eq_iff])
  let h2 :=
    (disjointPostLedgerComponents (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by simp [disjointPostLedgerComponents, hybridEntry, K_eq_iff])
  let h3 :=
    (typeBSelectedFanCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [typeBSelectedFanCharge, disjointPostLedgerComponents,
          hybridEntry, K_eq_iff])
  exact
    (typeBExclusionCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [typeBExclusionCharge, typeBSelectedFanCharge,
          disjointPostLedgerComponents, hybridEntry, K_eq_iff])

/-- Node `[85]`, exclusion split after the low-entropy degree-four B2 charge ledger. -/
noncomputable def selectedLowEntropyDegreeFourExclusionDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExcluded)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedLowEntropyDegreeFourB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedLowEntropyDegreeFourB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBExclusionCharge)
    (K .typeBExcluded) (K .typeBExclusionResidual)
    (fun charge => charge.down)
    (fun contradiction => ⟨False.elim contradiction⟩)
    (fun residual => ⟨residual⟩)
    (fun ledger => by
      obtain ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post, _groupedCoverage⟩ := ledger.down
      exact ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post⟩)
    (by
      simp [selectedLowEntropyDegreeFourB2ExclusionCharge,
        typeBExclusionCharge, typeBSelectedFanCharge,
        disjointPostLedgerComponents, hybridEntry, K_eq_iff])
    (by
      simp [selectedLowEntropyDegreeFourB2ExclusionCharge,
        typeBExclusionCharge, typeBSelectedFanCharge,
        disjointPostLedgerComponents, hybridEntry, K_eq_iff])

/-- Node `[85]`, closing the excluded arm on the low-entropy degree-four path. -/
noncomputable def selectedLowEntropyDegreeFourExcludedCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExcluded, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let closedHistory :=
    closeImpossible history (K .typeBExcluded)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[85]`, low-entropy degree-four B2-success arm reduced to the exclusion residual survivor. -/
noncomputable def selectedLowEntropyDegreeFourExclusionResidual
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedLowEntropyDegreeFourExclusionDichotomy history with
  | .left nonnegativeHistory =>
      exact False.elim
        (selectedLowEntropyDegreeFourExcludedCloses nonnegativeHistory)
  | .right residualHistory =>
      exact residualHistory

/-- Nodes `[82]`--`[85]`, B2-success charge ledger on the high-entropy degree-four path. -/
noncomputable def selectedHighEntropyDegreeFourB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let h1 :=
    (hybridEntry (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [hybridEntry, K_eq_iff])
  let h2 :=
    (disjointPostLedgerComponents (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by simp [disjointPostLedgerComponents, hybridEntry, K_eq_iff])
  let h3 :=
    (typeBSelectedFanCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [typeBSelectedFanCharge, disjointPostLedgerComponents,
          hybridEntry, K_eq_iff])
  exact
    (typeBExclusionCharge (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [typeBExclusionCharge, typeBSelectedFanCharge,
          disjointPostLedgerComponents, hybridEntry, K_eq_iff])

/-- Node `[85]`, exclusion split after the high-entropy degree-four B2 charge ledger. -/
noncomputable def selectedHighEntropyDegreeFourExclusionDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExcluded)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedHighEntropyDegreeFourB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedHighEntropyDegreeFourB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBExclusionCharge)
    (K .typeBExcluded) (K .typeBExclusionResidual)
    (fun charge => charge.down)
    (fun contradiction => ⟨False.elim contradiction⟩)
    (fun residual => ⟨residual⟩)
    (fun ledger => by
      obtain ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post, _groupedCoverage⟩ := ledger.down
      exact ⟨packing, valid, maximal, canonicalPiece, negative, surplus,
        chosen, exact, post⟩)
    (by
      simp [selectedHighEntropyDegreeFourB2ExclusionCharge,
        typeBExclusionCharge, typeBSelectedFanCharge,
        disjointPostLedgerComponents, hybridEntry, K_eq_iff])
    (by
      simp [selectedHighEntropyDegreeFourB2ExclusionCharge,
        typeBExclusionCharge, typeBSelectedFanCharge,
        disjointPostLedgerComponents, hybridEntry, K_eq_iff])

/-- Node `[85]`, closing the excluded arm on the high-entropy degree-four path. -/
noncomputable def selectedHighEntropyDegreeFourExcludedCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExcluded, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let closedHistory :=
    closeImpossible history (K .typeBExcluded)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[85]`, high-entropy degree-four B2-success arm reduced to the exclusion residual survivor. -/
noncomputable def selectedHighEntropyDegreeFourExclusionResidual
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedHighEntropyDegreeFourExclusionDichotomy history with
  | .left nonnegativeHistory =>
      exact False.elim
        (selectedHighEntropyDegreeFourExcludedCloses nonnegativeHistory)
  | .right residualHistory =>
      exact residualHistory

/-- Node `[76]`, bridge mass on the low-entropy heavy B2 residual arm. -/
noncomputable def selectedLowEntropyTypeBExclusionResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeBExclusionResidualMassRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [K_eq_iff])

/-- Node `[76]`, bridge mass on the high-entropy heavy B2 residual arm. -/
noncomputable def selectedHighEntropyTypeBExclusionResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeBExclusionResidualMassRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [K_eq_iff])

/-- Node `[85]`, bridge mass on the low-entropy degree-four B2 residual arm. -/
noncomputable def selectedLowEntropyDegreeFourExclusionResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (typeBExclusionResidualMassRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [K_eq_iff])

/-- Node `[85]`, bridge mass on the high-entropy degree-four B2 residual arm. -/
noncomputable def selectedHighEntropyDegreeFourExclusionResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidual, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (typeBExclusionResidualMassRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [K_eq_iff])

/-- Nodes `[74]`--`[76]`, low-entropy heavy B2-success arm through bridge mass. -/
noncomputable def selectedLowEntropyTypeBExclusionMassAfterDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  selectedLowEntropyTypeBExclusionResidualMass
    (selectedLowEntropyTypeBExclusionResidual history)

/-- Nodes `[74]`--`[76]`, high-entropy heavy B2-success arm through bridge mass. -/
noncomputable def selectedHighEntropyTypeBExclusionMassAfterDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  selectedHighEntropyTypeBExclusionResidualMass
    (selectedHighEntropyTypeBExclusionResidual history)

/-- Nodes `[82]`--`[85]`, low-entropy degree-four B2-success arm through bridge mass. -/
noncomputable def selectedLowEntropyDegreeFourExclusionMassAfterDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  selectedLowEntropyDegreeFourExclusionResidualMass
    (selectedLowEntropyDegreeFourExclusionResidual history)

/-- Nodes `[82]`--`[85]`, high-entropy degree-four B2-success arm through bridge mass. -/
noncomputable def selectedHighEntropyDegreeFourExclusionMassAfterDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionResidualMass, K .typeBExclusionResidual,
        K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .netDeficiencyCap, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  selectedHighEntropyDegreeFourExclusionResidualMass
    (selectedHighEntropyDegreeFourExclusionResidual history)

/-- Node `[91]`, closing the unsaturated Type A arm using the registered
incompatibility between the low-surplus support and its nonnegative discharge. -/
noncomputable def selectedLowEntropyTypeAUnsaturatedCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAUnsaturatedReceivers, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let discharged := selectedLowEntropyTypeAUnsaturatedDischarge history
  rcases (discharged.get (K .typeAUnsaturatedDischarge)).down with
    ⟨packing, _valid, _maximal, component, _componentMem, negative,
      surplusZero, discharge⟩
  unfold Graph.FiniteObject.NegativeNetCharge at negative
  rw [surplusZero, Nat.mul_zero, Nat.add_zero] at negative
  omega

/-- Node `[91]`, closing the high-entropy unsaturated Type A arm using the same
ledger incompatibility. -/
noncomputable def selectedHighEntropyTypeAUnsaturatedCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeAUnsaturatedReceivers, K .typeAReceiverRouting,
        K .typeALowSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let discharged := selectedHighEntropyTypeAUnsaturatedDischarge history
  rcases (discharged.get (K .typeAUnsaturatedDischarge)).down with
    ⟨packing, _valid, _maximal, component, _componentMem, negative,
      surplusZero, discharge⟩
  unfold Graph.FiniteObject.NegativeNetCharge at negative
  rw [surplusZero, Nat.mul_zero, Nat.add_zero] at negative
  omega

/-- Node `[145]`: record node `[22]`'s partition on the literal cold residual
after the density/spine entry.  The atomic row reads `K .hotColdPartition`
from this ExactLedger and appends only `K .coldWindowLedgerSplit`. -/
noncomputable def selectedColdWindowLedgerSplit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldWindowLedgerSplitRow (data := spineData)).run history
    (by simp [K_eq_iff])

/-- Node `[146]`: the route-8 threshold is decided on the literal `[145]`
residual.  The two outputs are sibling ledgers; neither output is appended to
the other. -/
noncomputable def selectedColdRoute8Dichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  coldRoute8Dichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[148]`: only the no arm of `[146]` reaches the live-hot entropy
decision. -/
noncomputable def selectedColdHotEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  coldHotEntropyDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[149]`: publish the exact density cap on `[148]`'s overflow
residual. -/
noncomputable def selectedColdHotEntropyDensityCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldHotEntropyOverflow, K .coldRoute8AtOrAbove,
        K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  (coldHotEntropyDensityCapRow (data := spineData)).run history
    (by simp [K_eq_iff])

/-- Node `[150]`: append the cold-mass inequality to `[148]`'s literal
no-residual. -/
noncomputable def selectedColdMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldHotEntropyCap, K .coldRoute8AtOrAbove,
        K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  (coldMassRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[151]`: append the ambient-cubic loss bound without rebuilding or
copying any predecessor fact. -/
noncomputable def selectedColdAmbientCubic
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMass, K .coldHotEntropyCap, K .coldRoute8AtOrAbove,
        K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  (coldAmbientCubicRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[152]`: append the selected branch-excess inequality to the same
residual. -/
noncomputable def selectedColdStubExcess
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldAmbientCubic, K .coldMass, K .coldHotEntropyCap,
        K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  (coldStubExcessRow (data := spineData)).run history (by simp [K_eq_iff])

noncomputable def openSelectedCounterexample
    (input : EGInput) (avoids : ¬ Target input.object) :
    OpenedScope EGSelectionKey := by
  letI :
      FactSystem
        (Input BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData) :=
    instFactSystem
  exact openMinimalCounterexampleScope EGTarget
    (Graph.Strategy.Spine.progress BranchState
      Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile spineData)
    (fun _ => ())
    EGSelectionKey
    (fun context =>
      ⟨by
        simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData,
          Core.Strategy.selectedInput]
          using context.avoids,
      by
        intro smaller smallerLt baseline
        simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
          using context.minimal smaller smallerLt baseline⟩)
    input (by
      simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
        using avoids)

/-- A closed selected residual proves the registered target on every baseline
object. -/
theorem target_closure_of_selectedLedgerClosure
    (selectedLedgerClosure :
      ∀ {selected : EGInput.{u}},
        ExactLedger EGInput.{u} selected [EGSelectionKey] → False) :
    ∀ object : Graph.FiniteObject.{u},
      Baseline object → Target object := by
  intro object baseline
  by_cases hasTarget : Target object
  · exact hasTarget
  · let input : EGInput :=
      { object := object
        baseline := baseline
        branchState := () }
    let opened := openSelectedCounterexample input hasTarget
    let selected : EGInput.{u} := by
      simpa [EGInput] using opened.selected
    have history : ExactLedger EGInput.{u} selected [EGSelectionKey] := by
      simpa [selected, EGInput] using opened.history
    exact (selectedLedgerClosure (selected := selected) history).elim

/-- Final public theorem, once the exact-ledger selected residual closure has
been assembled from the rows. -/
theorem erdos_64_of_selectedLedgerClosure
    (selectedLedgerClosure :
      ∀ {selected : EGInput.{u}},
        ExactLedger EGInput.{u} selected [EGSelectionKey] → False) :
    OfficialStatement.{u} :=
  EGTarget.target_to_statement
    (target_closure_of_selectedLedgerClosure selectedLedgerClosure)

/-! The two node-[19] arms are separate exact-ledger cursors.  Node `[20]`
is the strict-surplus sibling; only the at-or-below sibling reaches node `[21]`.
Neither branch reads or publishes a fact owned by the other. -/

noncomputable def selectedNearCubicNode21
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  let enumerated :=
    (barrierEnumerationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [barrierEnumerationRow, K_eq_iff])
  let separated :=
    (windowPackageRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      enumerated (by simp [windowPackageRow, K_eq_iff])
  (skeletonDominatesRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    separated (by simp [skeletonDominatesRow, K_eq_iff])

/-! Node `[20]` and the post-`[21]` continuation are explicit branch
functions.  Their arguments and results are exact-ledger indices, so the
strict and near-cubic cursors cannot be accidentally exchanged. -/

noncomputable def selectedStrictSurplusBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  match selectedStrictSeparatedWindowClassDichotomy history with
  | .left windowHistory =>
      match selectedWindowOverloadCapsDichotomy windowHistory with
      | .left capsHistory =>
          exact selectedWindowHomogeneousCapsEstimate capsHistory
      | .right patternHistory =>
          exact selectedWindowOverloadBridgeSublinearHistory patternHistory
  | .right windowAbsentHistory =>
      match selectedRemainderClassDichotomy windowAbsentHistory with
      | .left remainderHistory =>
          match selectedRemainderOverloadCapsDichotomy remainderHistory with
          | .left capsHistory =>
              exact selectedRemainderHomogeneousCapsEstimate capsHistory
          | .right patternHistory =>
              exact selectedRemainderOverloadBridgeSublinearHistory patternHistory
      | .right remainderAbsentHistory =>
          match selectedPrimitiveOverloadCapsDichotomy remainderAbsentHistory with
          | .left capsHistory =>
              exact selectedPrimitiveHomogeneousCapsEstimate capsHistory
          | .right patternHistory =>
              exact selectedPrimitiveOverloadBridgeSublinearHistory patternHistory

noncomputable def selectedNearCubicBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .wedgeSupply, K .stubSupply, K .boundaryDemand,
        K .remainderNormalized, K .densityCap,
        K .barrierCap, K .hotColdPartition,
        K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let enumerated := selectedNearCubicNode21 history
  match selectedBarrierDichotomy enumerated with
  | .left capHistory =>
      let densityHistory := selectedDensityBudget capHistory
      let remainderHistory :=
        (remainderNormalizationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          densityHistory (by
            simp [remainderNormalizationRow, selectedDensityBudget, K_eq_iff])
      let boundaryHistory :=
        (boundaryDemandRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          remainderHistory (by
            simp [boundaryDemandRow, remainderNormalizationRow,
              selectedDensityBudget, K_eq_iff])
      let stubHistory :=
        (stubSupplyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          boundaryHistory (by
            simp [stubSupplyRow, boundaryDemandRow, remainderNormalizationRow,
              selectedDensityBudget, K_eq_iff])
      exact
        (wedgeSupplyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          stubHistory (by
            simp [wedgeSupplyRow, stubSupplyRow, boundaryDemandRow,
              remainderNormalizationRow, selectedDensityBudget, K_eq_iff])
  | .right overflowHistory =>
      exact False.elim (selectedBarrierOverflowCloses overflowHistory)


/-- Selected-root closure, assembled directly from the exact-ledger rows. -/
theorem selectedLedgerClosure
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) : False := by
  match selectedSurplusDichotomy history with
  | .left strictHistory =>
      exact selectedStrictSurplusBranch strictHistory
  | .right nearCubicHistory =>
      exact selectedNearCubicBranch nearCubicHistory

/-- Final public theorem for Erdős Problem 64. -/
theorem erdos_64 : OfficialStatement.{u} :=
  erdos_64_of_selectedLedgerClosure
    (fun {selected} history =>
      selectedLedgerClosure (selected := selected) history)

end HypostructureErdos64EG
