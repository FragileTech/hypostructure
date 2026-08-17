import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun
import Hypostructure.Graph.Strategy.BranchDClosure
import Hypostructure.Graph.Strategy.EntropyClosure

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

/-- Node `[22]`: the canonical hot/cold partition (`def:cold-window-ledger`),
then the live-hot entropy cap decision on `𝒫_hot`.

The comparison is formed from the current object's own registered quantities:
`skeletonBudget` against `2 ^ (rate · scales · |𝒫_hot|)`.  The overflow cursor
is the live-hot terminal `[23]`; the cap cursor is the literal no-arm residual
forwarded toward `[24]` and the cold continuation. -/
noncomputable def selectedBarrierDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff])
  Decision.run partitioned (K .barrierCap) (K .barrierOverflow)
    `HypostructureErdos64EG.selectedBarrierDichotomy
    (if overflow : Graph.skeletonBudget selected.object <
        2 ^ (spineData.{u}.windowRate *
          spineData.{u}.separatedScaleCount selected.object.vertexCount *
          (canonicalHotWindows spineData.{u} selected.object).card) then
      .inr ⟨overflow⟩
    else
      .inl ⟨Nat.le_of_not_lt overflow,
        fun _family member =>
          Graph.skeletonBudget_le_variableEdgeBudget selected.object member⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[23]`: the live-hot `P₁₃` window entropy overflow closes on the
literal overflow residual.  `𝒫_hot` is retained in the canonical entropy
comparison (`K .hotColdPartition`): its full package code
`2 ^ (bits · |𝒫_hot|)` is realized canonically by labelled skeletons of the
current class, `lem:skeleton-dominates` (`K .skeletonDominates`) bounds every
canonical state count by the skeleton budget, and `lem:p13-window-package`
(`K .windowPackageSeparated`) gives `rate · scales ≤ bits`; the overflow arm
says the budget is below `2 ^ (rate · scales · |𝒫_hot|)`.  This is
`lem:independent-target-entropy` on the incoming residual. -/
noncomputable def selectedBarrierOverflowCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierOverflow, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  have overflow := (history.get (K .barrierOverflow)).down
  have split := (history.get (K .hotColdPartition)).down
  have dominates := (history.get (K .skeletonDominates)).down
  have package := (history.get (K .windowPackageSeparated)).down
  obtain ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint, _cover⟩ :=
    split
  obtain ⟨_hotSubset, ⟨State, stateOf, realized⟩, _hotMaximal⟩ := hotFacts
  have realizedBound := dominates.2 State stateOf
  obtain ⟨_packing, _packingValid, _packingCard, _packingMaximal,
    _packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
  have exponentLe :
      spineData.{u}.windowRate *
          spineData.{u}.separatedScaleCount selected.object.vertexCount *
          (canonicalHotWindows spineData.{u} selected.object).card ≤
        windowPackageBits spineData.{u} selected.object *
          (canonicalHotWindows spineData.{u} selected.object).card :=
    Nat.mul_le_mul_right _ rateLe
  have := (Nat.pow_le_pow_right (by norm_num) exponentLe).trans
    (realized.trans realizedBound)
  exact absurd this (Nat.not_le_of_lt overflow)

/-- Node `[24]`: `prop:p13-density` "after closure" — on `[153]`'s bounded arm
(the cold branch forces no germ), the window-only density cap with its exact
`o(1)` is produced from `K .coldMass`, `K .coldMassBounded`,
`K .coldAmbientCubic`, and the split, on the literal residual. -/
noncomputable def selectedDensityBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .densityCap, K .coldMassBounded, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (densityBudgetRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[60]`, the order-regime split on the low-entropy Residual C arm. -/
noncomputable def selectedLowEntropyNetChargeOrderDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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
        K .boundaryDemand, K .stubSupply,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
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
        K .boundaryDemand, K .stubSupply,
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

/-- Node `[149]`: the live-hot entropy comparison closes on `[148]`'s literal
overflow residual.  On the `[22]` cap arm the ledger already carries
`2 ^ (rate·scales·|𝒫_hot|) ≤ skeletonBudget` (`K .barrierCap`); spending the
skeleton budget against the near-cubic spine (`K .surplusAtOrBelow` and the
standing baseline handshake) gives the exact finite cap
`2·rate·scales·|𝒫_hot| ≤ (⌊log₂ n⌋+1)(δn + T(n))`, which the overflow arm
denies.  This is `prop:p13-density`'s entropy step on the current residual. -/
noncomputable def selectedColdHotEntropyCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldHotEntropyOverflow, K .coldRoute8AtOrAbove,
        K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  have overflow := (history.get (K .coldHotEntropyOverflow)).down
  have cap := (history.get (K .barrierCap)).down
  have nearCubic := (history.get (K .surplusAtOrBelow)).down
  have spine : spineData.{u}.threshold * selected.object.vertexCount ≤
      2 * selected.object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount selected.object
      spineData.{u}.threshold fun vertex =>
        le_trans selected.baseline (selected.object.minDegree_le_degree vertex)
  have bound := Graph.two_mul_exponent_le_scale_mul_edgeBudget selected.object
    (spineData.{u}.windowRate *
      spineData.{u}.separatedScaleCount selected.object.vertexCount *
      (canonicalHotWindows spineData.{u} selected.object).card)
    spineData.{u}.threshold (spineData.{u}.surplusThreshold selected.object.vertexCount)
    cap.1 spine spineData.{u}.three_le_threshold nearCubic
  change coldSkeletonAllowance spineData.{u} selected.object <
    coldWindowBitRate spineData.{u} selected.object *
      (canonicalHotWindows spineData.{u} selected.object).card at overflow
  simp only [coldSkeletonAllowance, coldWindowBitRate] at overflow
  rw [Nat.mul_assoc] at overflow
  exact absurd bound (Nat.not_le_of_lt overflow)

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

/-- Node `[153]`: the exact finite germ-positivity comparison on the literal
`[152]` residual (`2·perWindow·σ(G) < perWindow·C`); the linear arm forces a
positive germ family (`lem:cold-germ-extraction`), the bounded arm continues to
`[24]`. -/
noncomputable def selectedColdMassDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldStubExcess, K .coldAmbientCubic, K .coldMass, K .coldHotEntropyCap,
        K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :=
  coldMassDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- `lem:bridgeless` on the literal `[153]` linear residual: the selected
object has no bridge; every oriented edge has a return. -/
noncomputable def selectedBridgeless
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (bridgelessRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
    (by simp [K_eq_iff])

/-- Node `[153]`, `def:cold-corridor-first-failure`: every boundary stub of every
outside component of `X_cold` has its cold return corridor. -/
noncomputable def selectedColdReturnCorridors
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldReturnCorridorRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`, `lem:cold-corridor-first-failure`: cut-states and (F1)--(F5)
routing on the literal linear residual. -/
noncomputable def selectedColdFirstFailureRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldFirstFailureRoutingRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`, `lem:cold-germ-extraction`: the exchange bound and the greedy
extraction, on the routed residual. -/
noncomputable def selectedColdGermExtraction
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldGermExtractionRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate germ family of
the selected branch-excess half-edges — its count, overlap bound, positivity
(the `[153]` linear arm) and its extracted disjoint subfamily — on the literal
extraction residual. -/
noncomputable def selectedColdGermCandidates
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldGermCandidatesRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Nodes `[154]`--`[156]`, `lem:cold-bounded-germ-trichotomy` and
`lem:cold-increment-arithmetic` on the literal extracted residual. -/
noncomputable def selectedColdGermTrichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected [K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldGermTrichotomyRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[157]`, `lem:cold-same-interface-table` with the short self-return
filter, on the literal trichotomy residual. -/
noncomputable def selectedColdSameInterfaceTable
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected [K .coldSameInterfaceTable, K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldSameInterfaceTableRow (data := spineData)).run history (by simp [K_eq_iff])

/-- `thm:cold-branch-quantitative-closure`: no terminal cold residual remains;
the branch is closed by routing to the target-defect and handoff ledgers. -/
noncomputable def selectedColdBranchClosed
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [K .coldSameInterfaceTable, K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected [K .coldBranchClosed, K .coldSameInterfaceTable, K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldBranchClosedRow (data := spineData)).run history (by simp [K_eq_iff])

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

/-- Branch D, nodes `[35]`--`[46]`, on the literal `[33]` ledger of a spine
arm: the context-validity test `[36]` with its target-defect terminal `[37]`,
the atom-compression test `[38]` with its terminal `[39]`, the delocalization
scope `[40]`/`[41]` with its proper-support terminal `[42]`, and the
whole-graph route `[43]`--`[45]` closed at `[46]`.  Every terminal is a
framework closure over the ledger of the arm against `K .selection`; the
freshness of the keys committed along the way is decided on the arm's exact
index at the call site. -/
noncomputable def selectedRankDropCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .branchDependence) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .selection) known]
    (defectFresh : K .contextDefect ∉ known)
    (universalFresh : K .contextUniversal ∉ known)
    (compressionFresh : K .atomCompression ∉ known)
    (delocalizedFresh : K .delocalizedSupport ∉ known)
    (properFresh : K .properDelocalization ∉ known)
    (globalFresh : K .globalDelocalization ∉ known)
    (repairFresh : K .repairIdentity ∉ known)
    (barrierFresh : K .globalBarrier ∉ known)
    (closureFresh : closed ∉ known) : False := by
  match contextValidityDichotomy (data := spineData) history defectFresh universalFresh with
  | .left defectHistory =>
      -- `[37]`: target-defective quotient — uninhabited (`lem:context-universality`).
      exact (closeImpossible defectHistory (K .contextDefect)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
  | .right universalHistory =>
      -- `[38]`: target-complete with a smaller proper representative?
      match atomCompressionDichotomy (data := spineData) universalHistory
          (by simp [K_eq_iff, compressionFresh]) (by simp [K_eq_iff, delocalizedFresh]) with
      | .left compressionHistory =>
          -- `[39]`: proper atom compression, forbidden by `cor:uncompressible`.
          exact (closeIncompatible compressionHistory (K .selection)
            (K .atomCompression) (by simp [K_eq_iff, closureFresh])).elimClosed
            (by infer_instance)
      | .right delocalizedHistory =>
          -- `[40]`/`[41]`: the enlarged connected support `Z ⊋ C`; is `Z ⊊ G`?
          match delocalizationScopeDichotomy (data := spineData) delocalizedHistory
              (by simp [K_eq_iff, properFresh]) (by simp [K_eq_iff, globalFresh]) with
          | .left properHistory =>
              -- `[42]`: proper-support smearing closure (`lem:proper-smearing`).
              exact (closeIncompatible properHistory (K .selection)
                (K .properDelocalization) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)
          | .right globalHistory =>
              -- `[43]`--`[45]`: whole-graph delocalization, the `1`--`3` repair
              -- identity, and the target/replacement/global-profile barrier.
              let repaired :=
                (repairIdentityRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  globalHistory (by simp [K_eq_iff, repairFresh])
              let barrier :=
                (globalBarrierRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  repaired (by simp [K_eq_iff, barrierFresh])
              -- `[46]`: rank-drop branch closed (`lem:no-silent-global-smearing`).
              exact (closeIncompatible barrier (K .selection) (K .globalBarrier)
                (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)

/-- **Nodes `[57]`--`[64]`: the large-budget net-charge split**, on the `[56]`
residual of either spine arm.  `[57]` enters the asymptotic order regime and
reads the large-budget net cap; `[58]` localizes the charge; `[59]` splits on the
sign; the nonnegative arm is the `[60]` net-cap contradiction (cap gives
`N₀(R) < 0`, the sibling gives `N₀(R) ≥ 0`); the negative arm selects a connected
negative support `[61]` and `[62]` routes it to Type A `[63]` or Type B `[64]`.
The small-order complement `[57]`, and the Type A / Type B continuations, are the
next loud producers.  It is index-polymorphic over the arm's ledger, so both the
density-cap and route-8 arms use the same definition. -/
noncomputable def selectedNetChargeContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .maximalPacking) known]
    (largeFresh : K .netChargeLarge ∉ known := by simp [K_eq_iff])
    (smallFresh : K .netChargeSmall ∉ known := by simp [K_eq_iff])
    (capFresh : K .netChargeCap ∉ known := by simp [K_eq_iff])
    (locFresh : K .netChargeLocalization ∉ known := by simp [K_eq_iff])
    (nonNegFresh : K .netChargeNonNegative ∉ known := by simp [K_eq_iff])
    (negFresh : K .netChargeNegative ∉ known := by simp [K_eq_iff])
    (supportFresh : K .negativeSupport ∉ known := by simp [K_eq_iff])
    (typeAFresh : K .typeALowSurplus ∉ known := by simp [K_eq_iff])
    (typeBFresh : K .typeBHighSurplus ∉ known := by simp [K_eq_iff]) : False := by
  match netChargeOrderDichotomy (data := spineData) history largeFresh smallFresh with
  | .right smallHistory =>
      -- `[57]` small-order complement: outside the manuscript's asymptotic
      -- regime; the finite-order residual is the next producer.
      exact selectedNetChargeSmallOrder smallHistory
  | .left largeHistory =>
      -- `[57]`: the large-budget net cap on the literal `[56]` residual.
      let capped :=
        (netChargeCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          largeHistory (by simp [K_eq_iff, capFresh])
      -- `[58]`: `lem:netcharge-superadd` localizes negative charge to a piece.
      let localized :=
        (netChargeLocalizationRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          capped (by simp [K_eq_iff, locFresh])
      -- `[59]`: `N₀(R) ≥ 0?`
      match netChargeDichotomy (data := spineData) localized
          (by simp [K_eq_iff, nonNegFresh]) (by simp [K_eq_iff, negFresh]) with
      | .left nonNegHistory =>
          -- `[60]`: the net-cap contradiction on the same canonical maximal
          -- packing.  The cap gives `N₀(R) < 0`; the sibling gives `N₀(R) ≥ 0`.
          obtain ⟨_positive, packing, valid, cardinality, maximal⟩ :=
            (nonNegHistory.get (K .maximalPacking)).down
          have negative :=
            (nonNegHistory.get (K .netChargeCap)).down packing valid cardinality
          have nonnegative :=
            (nonNegHistory.get (K .netChargeNonNegative)).down packing valid maximal
          exact ((selected.object.not_negativeNetCharge_iff
            (selected.object.remainderSupport packing) spineData.threshold
            spineData.dischargeScale).mpr nonnegative) negative
      | .right negativeHistory =>
          -- `[61]`: select the connected negative support.
          let support :=
            (negativeSupportRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              negativeHistory (by simp [K_eq_iff, supportFresh])
          -- `[62]`: high-degree surplus? Type A `[63]` / Type B `[64]`.
          match typeSplitDichotomy (data := spineData) support
              (by simp [K_eq_iff, typeAFresh]) (by simp [K_eq_iff, typeBFresh]) with
          | .left typeAHistory =>
              exact selectedTypeALowSurplusContinuation typeAHistory
          | .right typeBHistory =>
              exact selectedTypeBHighSurplusContinuation typeBHistory


/-- The near-cubic branch after node `[19]`: node `[21]`, the `[22]` split and
live-hot cap, and — on the cap arm, exactly as `[24]` prescribes — the cold
branch `[145]`--`[157]` on the literal cap residual.  Both spine arms — `[146]`'s
yes arm (`θ < 1/78`, node `[147]`: closed by the spine's route-8 closure with
`K .coldRoute8Below` as its private-carrier inequality) and `[153]`'s bounded
arm (`[24]`'s density cap) — run `[25]`--`[31]` on their literal residuals,
decide `[32]` and enter `[33]` (Branch D) or `[34]` (Residual B); `[35]`--`[46]`
and `[47]` onward fail loudly; the routed cold closure `[157]` fails loudly at
its target-defect/handoff discharge. -/
noncomputable def selectedNearCubicBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let enumerated := selectedNearCubicNode21 history
  match selectedBarrierDichotomy enumerated with
  | .left capHistory =>
      let split := selectedColdWindowLedgerSplit capHistory
      match selectedColdRoute8Dichotomy split with
      | .left belowHistory =>
          -- `[147]`: "If `θ < 1/78`, then `τ(θ) < 3/13` by
          -- `def:cold-window-ledger`; this is exactly the private-carrier
          -- inequality used in `thm:large-budget-route8-only`, so the route-8
          -- branch closes."  The private-carrier inequality is
          -- `K .coldRoute8Below` on this residual, and the closure it names is
          -- the spine's own large-budget/route-8 closure (`[25]` → `[55]` →
          -- `[63]` → `[110]`--`[124]`), which reads `τ < 1/4` at `[56]`/`[59]`
          -- and `τ < 3/13` at `[122]` from that fact in place of `[24]`'s
          -- density cap.  Run `[25]`--`[31]` on the literal `[146]` yes-residual;
          -- `[32]` onward on it is the next producer.
          let remainder :=
            (remainderNormalizationRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              belowHistory (by simp [K_eq_iff])
          let boundary :=
            (boundaryDemandRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              remainder (by simp [K_eq_iff])
          let stubSupply :=
            (stubSupplyRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              boundary (by simp [K_eq_iff])
          let wedge :=
            (wedgeSupplyRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              stubSupply (by simp [K_eq_iff])
          let rank :=
            (curvatureTargetRankRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              wedge (by simp [K_eq_iff])
          let circuit :=
            (targetRankCircuitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              rank (by simp [K_eq_iff])
          -- `[32]`: the exact finite rank split at the canonical maximal packing.
          match curvatureRankDichotomy (data := spineData) circuit
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .left dropHistory =>
              -- `[33]`: Branch D, the rank-reducing curvature dependence with its
              -- inclusion-minimal connected support; `[35]`--`[46]` on this
              -- residual is the next producer.
              let dependence :=
                (branchDependenceRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  dropHistory (by simp [K_eq_iff])
              exact selectedRankDropCloses dependence
                (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
          | .right fullRankHistory =>
          -- `[34]`: Residual B, no rank drop — `r_Ω(R) = W₂(R)` on the sibling
          -- ledger.  `[47]`/`[48]`: `cor:forced-curvature-cost` from `lem:full-rank`
          -- and `lem:wedge-lower`; `[49]`/`[50]`: the per-vertex remainder entropy
          -- split of `prop:two-budget`.
          let cost :=
            (forcedCurvatureCostRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              fullRankHistory (by simp [K_eq_iff])
          match remainderEntropyDichotomy (data := spineData) cost
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .left highHistory =>
              -- `[51]`/`[52]`: the high-entropy remainder branch and the window plus
              -- remainder accounting; `[53]`: the admissible entropy cap.
              let package :=
                (entropyPackageRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  highHistory (by simp [K_eq_iff])
              match entropyCapDichotomy (data := spineData) package
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left activeHistory =>
                  -- `[54]`: the entropy cap closes (`prop:entropy-high-theta`).  The
                  -- window package, remainder and forced-curvature bits "form one
                  -- independently target-testable coordinate family": the framework asks
                  -- whether that joint code is realized by the labelled skeletons of the
                  -- current class (`def:target-rank`, the exact-code equality retained on
                  -- the surviving hot residual).  Realized: the realized states exceed the
                  -- skeleton budget (`lem:independent-target-entropy`,
                  -- `lem:skeleton-dominates`).  Unrealized: the complementary residual,
                  -- passed forward as `prop:two-budget` prescribes; its continuation is
                  -- the next producer.
                  match jointCodeDichotomy (data := spineData) activeHistory
                      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                  | .left realizedHistory =>
                      exact entropyCap_closes realizedHistory
                  | .right unrealizedHistory =>
                      exact selectedRouteEightJointCodeUnrealizedRouted unrealizedHistory
              | .right largeHistory =>
                  -- `[55]`: Residual C on the high-entropy arm.
                  -- `[56]` on the route-8 arm: `Δ_net(R) < 1/4` from `τ(θ) < 3/13`
              -- (`K .coldRoute8Below`), which is the density input of this arm.
                  let netCap :=
                    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      largeHistory (by simp [K_eq_iff])
                  -- `[57]` onward on this residual is the next producer.
                  exact selectedNetChargeContinuation netCap
          | .right lowHistory =>
              -- `[55]`: Residual C on the low-entropy arm, routed forward unchanged.
              let large :=
                (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  lowHistory (by simp [K_eq_iff])
              -- `[56]` on the route-8 arm: `Δ_net(R) < 1/4` from `τ(θ) < 3/13`
              -- (`K .coldRoute8Below`), which is the density input of this arm.
              let netCap :=
                (routeEightNetDeficiencyCapRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  large (by simp [K_eq_iff])
              -- `[57]` onward on this residual is the next producer.
              exact selectedNetChargeContinuation netCap
      | .right atOrAboveHistory =>
          match selectedColdHotEntropyDichotomy atOrAboveHistory with
          | .left overflowHistory =>
              exact selectedColdHotEntropyCloses overflowHistory
          | .right hotCapHistory =>
              let mass := selectedColdMass hotCapHistory
              let cubic := selectedColdAmbientCubic mass
              let stubs := selectedColdStubExcess cubic
              match selectedColdMassDichotomy stubs with
              | .left linearHistory =>
                  -- `[153]`: `lem:bridgeless`, the return corridors, first-failure
                  -- routing, the exchange bound and extraction, and the (F5)
                  -- candidate germ family on the linear residual; then `[154]`.
                  let bridgeless := selectedBridgeless linearHistory
                  let corridors := selectedColdReturnCorridors bridgeless
                  let routed := selectedColdFirstFailureRouting corridors
                  let extracted := selectedColdGermExtraction routed
                  let candidates := selectedColdGermCandidates extracted
                  let trichotomy := selectedColdGermTrichotomy candidates
                  let table := selectedColdSameInterfaceTable trichotomy
                  let closed := selectedColdBranchClosed table
                  -- `thm:cold-branch-quantitative-closure`'s last step is not
                  -- yet derivable here, for two exact reasons.  (a) The `[153]`
                  -- (F5) candidates are `germOfSupport` germs whose second
                  -- representative is the support's own piece, so each identifies
                  -- `Q[x,y]` with itself: not realizing, not distinguishing,
                  -- `δ = 0`, and not a `TableRow`; they realize none of the
                  -- paper's outcomes, and `K .coldBranchClosed`
                  -- (`NoTerminalColdResidual`) is vacuous on them.  Genuine (F5)
                  -- representatives (repeat subcase: the shorter equal-state
                  -- prefix; terminal subcase: the terminal exchange
                  -- representative) are needed.  (b) The two routed outcomes —
                  -- G2, a target-defective identification (sparse exit /
                  -- Type A exit-(4) target-defect ledger), and table/(F4)
                  -- handoff (Type B / route-8 ledgers) — are discharged by
                  -- `def:surviving-cold-branch` (ii)–(v), ledgers of other
                  -- branches that no fact of this residual carries.  No terminal
                  -- is fabricated; the producer stays loud with exactly these
                  -- inputs.
                  exact selectedColdBranchRouted closed
              | .right boundedHistory =>
                  -- `[24]` → `[25]`--`[30]` on the literal bounded residual.
                  let density := selectedDensityBudget boundedHistory
                  let remainder :=
                    (remainderNormalizationRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      density (by simp [K_eq_iff])
                  let boundary :=
                    (boundaryDemandRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      remainder (by simp [K_eq_iff])
                  let stubSupply :=
                    (stubSupplyRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      boundary (by simp [K_eq_iff])
                  let wedge :=
                    (wedgeSupplyRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      stubSupply (by simp [K_eq_iff])
                  -- `[31]`: the curvature target-rank of the remainder and
                  -- `lem:target-rank-circuit`, on the literal `[30]` residual.
                  let rank :=
                    (curvatureTargetRankRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      wedge (by simp [K_eq_iff])
                  let circuit :=
                    (targetRankCircuitRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      rank (by simp [K_eq_iff])
                  -- `[32]`: the exact finite rank split at the canonical maximal packing.
                  match curvatureRankDichotomy (data := spineData) circuit
                      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                  | .left dropHistory =>
                      -- `[33]`: Branch D, the rank-reducing curvature dependence with its
                      -- inclusion-minimal connected support; `[35]`--`[46]` on this
                      -- residual is the next producer.
                      let dependence :=
                        (branchDependenceRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) spineData).run
                          dropHistory (by simp [K_eq_iff])
                      exact selectedRankDropCloses dependence
                        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                  | .right fullRankHistory =>
                  -- `[34]`: Residual B, no rank drop — `r_Ω(R) = W₂(R)` on the sibling
                  -- ledger.  `[47]`/`[48]`: `cor:forced-curvature-cost` from `lem:full-rank`
                  -- and `lem:wedge-lower`; `[49]`/`[50]`: the per-vertex remainder entropy
                  -- split of `prop:two-budget`.
                  let cost :=
                    (forcedCurvatureCostRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      fullRankHistory (by simp [K_eq_iff])
                  match remainderEntropyDichotomy (data := spineData) cost
                      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                  | .left highHistory =>
                      -- `[51]`/`[52]`: the high-entropy remainder branch and the window plus
                      -- remainder accounting; `[53]`: the admissible entropy cap.
                      let package :=
                        (entropyPackageRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) spineData).run
                          highHistory (by simp [K_eq_iff])
                      match entropyCapDichotomy (data := spineData) package
                          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                      | .left activeHistory =>
                          -- `[54]`: the entropy cap closes (`prop:entropy-high-theta`).  The
                          -- window package, remainder and forced-curvature bits "form one
                          -- independently target-testable coordinate family": the framework asks
                          -- whether that joint code is realized by the labelled skeletons of the
                          -- current class (`def:target-rank`, the exact-code equality retained on
                          -- the surviving hot residual).  Realized: the realized states exceed the
                          -- skeleton budget (`lem:independent-target-entropy`,
                          -- `lem:skeleton-dominates`).  Unrealized: the complementary residual,
                          -- passed forward as `prop:two-budget` prescribes; its continuation is
                          -- the next producer.
                          match jointCodeDichotomy (data := spineData) activeHistory
                              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                          | .left realizedHistory =>
                              exact entropyCap_closes realizedHistory
                          | .right unrealizedHistory =>
                              exact selectedJointCodeUnrealizedRouted unrealizedHistory
                      | .right largeHistory =>
                          -- `[55]`: Residual C on the high-entropy arm.
                          -- `[56]`: `Δ_net(R) ≤ τ_win + o(1) < 1/4` from `[24]`'s density cap.
                          let netCap :=
                            (netDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              largeHistory (by simp [K_eq_iff])
                          -- `[57]` onward on this residual is the next producer.
                          exact selectedNetChargeContinuation netCap
                  | .right lowHistory =>
                      -- `[55]`: Residual C on the low-entropy arm, routed forward unchanged.
                      let large :=
                        (lowEntropyLargeBudgetRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                          lowHistory (by simp [K_eq_iff])
                      -- `[56]`: `Δ_net(R) ≤ τ_win + o(1) < 1/4` from `[24]`'s density cap.
                      let netCap :=
                        (netDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                          large (by simp [K_eq_iff])
                      -- `[57]` onward on this residual is the next producer.
                      exact selectedNetChargeContinuation netCap
  | .right overflowHistory =>
      exact selectedBarrierOverflowCloses overflowHistory

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
