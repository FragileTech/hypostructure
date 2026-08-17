import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun
import Hypostructure.Graph.Strategy.BranchDClosure
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.TypeBClosure
import Hypostructure.Graph.Strategy.TypeAExitRun

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

/-- Node `[125]`, `def:named-surplus-exits`: the selected minimal counterexample
survives the sparse surplus exits, on the literal strict-surplus residual. -/
noncomputable def selectedSparseSurplusSurvivor
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (sparseSurplusSurvivorRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [sparseSurplusSurvivorRow, K_eq_iff])

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
      [K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .barrierOverflow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .windowPackageSeparated) known] : False := by
  have overflow := (history.get (K .barrierOverflow)).down
  have split := (history.get (K .hotColdPartition)).down
  have dominates := (history.get (K .skeletonDominates)).down
  have package := (history.get (K .windowPackageSeparated)).down
  obtain ⟨_valid, _attains, _maximal, hotFacts, _coldIff, _disjoint, _cover⟩ :=
    split
  obtain ⟨_hotSubset, retained, _hotMaximal⟩ := hotFacts
  obtain ⟨_packing, _packingValid, _packingCard, _packingMaximal,
    _packageCard, _packagesDisjoint, _familyCard, rateLe, _⟩ := package
  have exponentLe :
      spineData.{u}.windowRate *
          spineData.{u}.separatedScaleCount selected.object.vertexCount *
          (canonicalHotWindows spineData.{u} selected.object).card ≤
        windowPackageBits spineData.{u} selected.object *
          (canonicalHotWindows spineData.{u} selected.object).card :=
    Nat.mul_le_mul_right _ rateLe
  rcases retained with ⟨State, stateOf, realized, _code⟩ | ⟨hotEmpty, _unrealized⟩
  · have realizedBound := dominates.2 State stateOf
    have := (Nat.pow_le_pow_right (by norm_num) exponentLe).trans
      (realized.trans realizedBound)
    exact absurd this (Nat.not_le_of_lt overflow)
  · -- No window is hot: the overflow `budget < 2 ^ 0` says the skeleton class is
    -- empty, but it contains the selected object's own skeleton.
    change Graph.skeletonBudget selected.object <
      2 ^ (spineData.{u}.windowRate *
        spineData.{u}.separatedScaleCount selected.object.vertexCount *
        (canonicalHotWindows spineData.{u} selected.object).card) at overflow
    rw [hotEmpty] at overflow
    simp only [Finset.card_empty, Nat.mul_zero, pow_zero] at overflow
    exact absurd (Graph.skeletonBudget_pos selected.object) (Nat.not_lt.mpr
      (Nat.le_of_lt_succ overflow))

/-- Node `[24]`: `prop:p13-density` "after closure" — on `[153]`'s bounded arm
(the cold branch forces no germ), the window-only density cap with its exact
`o(1)` is produced from `K .coldMass`, `K .coldMassBounded`,
`K .coldAmbientCubic`, and the split, on the literal residual. -/
noncomputable def selectedDensityBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .densityCap, K .coldMassBounded, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .netDeficiencyCap, K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
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
        K .densityCap, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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

/-- Node `[145]`: record node `[22]`'s partition on the literal cold residual
after the density/spine entry.  The atomic row reads `K .hotColdPartition`
from this ExactLedger and appends only `K .coldWindowLedgerSplit`. -/
noncomputable def selectedColdWindowLedgerSplit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition,
        K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldWindowLedgerSplit, K .barrierCap,
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldHotEntropyOverflow) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .surplusAtOrBelow) known] : False := by
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
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
        K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldCorridorState, K .coldFailureCycle, K .coldFailureDefect,
        K .coldFailureCompression, K .coldFailureHandoff, K .coldFailureRouting,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .coldWindowLedgerSplit,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
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
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (coldBranchClosedRow (data := spineData)).run history (by simp [K_eq_iff])

/-- **`thm:cold-branch-quantitative-closure`, the closing step, on the routed
`[157]` residual.**  By `lem:p13-window-package` (`K .windowPackageRealized`)
the canonical comparison retains the whole packing's package, so by
`def:cold-window-ledger` every packed window is hot: the canonical hot family
is the maximal retained subfamily (`K .coldWindowLedgerSplit`), hence the whole
packing, and `𝒫_cold = ∅`, `C = 0`.  The linear arm's positivity
`(perWindow + B_cold)·σ(G) < perWindow·C` (`K .coldMassLinear`) is then
impossible.  A direct `False` derivation from the ledger's facts,
index-polymorphic over the arm's exact ledger. -/
theorem selectedColdLinearCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldWindowLedgerSplit) known]
    [FactKeys.Has (K .windowPackageRealized) known] : False := by
  classical
  have linear := (history.get (K .coldMassLinear)).down
  have split := (history.get (K .coldWindowLedgerSplit)).down
  have realized := (history.get (K .windowPackageRealized)).down
  obtain ⟨_valid, _attains, _maximal, ⟨hotSubset, _retained, hotMaximal⟩, coldIff,
    _disjoint, _cover⟩ := split
  have packingLe := hotMaximal _ (Finset.Subset.refl _) realized
  have hotEq : canonicalHotWindows spineData.{u} selected.object =
      canonicalWindowPacking spineData.{u} selected.object :=
    Finset.eq_of_subset_of_card_le hotSubset packingLe
  have coldEmpty : canonicalColdWindows spineData.{u} selected.object = ∅ := by
    ext window
    simp only [Finset.notMem_empty, iff_false]
    intro member
    have := (coldIff window).1 member
    exact this.2 (hotEq ▸ this.1)
  change (Graph.ColdCorridor.branchExcessOf (coldExternalStubCount spineData.{u}) +
      Graph.ColdCorridor.overlapBound spineData.{u}.threshold spineData.{u}.coldSignature) *
      selected.object.degreeSurplus spineData.{u}.threshold <
    Graph.ColdCorridor.branchExcessOf (coldExternalStubCount spineData.{u}) *
      (canonicalColdWindows spineData.{u} selected.object).card at linear
  rw [coldEmpty, Finset.card_empty, Nat.mul_zero] at linear
  exact Nat.not_lt_zero _ linear

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
      history (by simp [K_eq_iff])
  let separated :=
    (windowPackageRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      enumerated (by simp [K_eq_iff])
  (skeletonDominatesRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    separated (by simp [K_eq_iff])

/-- Node `[21]`, `lem:p13-window-package` / `def:target-rank` /
`prop:p13-density`: "all target-complete window states are realized by labelled
near-cubic skeletons".  Per the methodology this is a decision on the literal
`[21]` residual: the yes arm carries the retention of the whole packing's package
in the canonical comparison (`K .windowPackageRealized`) and continues the
manuscript's chain unchanged; the no arm is the residual on which that sentence
fails, carried as a branch of its own (`K .windowPackageUnrealized`). -/
noncomputable def selectedWindowPackageRealizationDichotomy
    {selected : EGInput.{u}}
    (dominated : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :=
  Decision.run dominated (K .windowPackageRealized) (K .windowPackageUnrealized)
    `HypostructureErdos64EG.selectedWindowPackageRealizationDichotomy
    (by
      classical
      exact if realized : WindowFamilyRealized spineData.{u} selected.object
          (canonicalWindowPacking spineData.{u} selected.object) then
        .inl ⟨realized⟩
      else
        .inr ⟨realized⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-! Node `[20]` and the post-`[21]` continuation are explicit branch
functions.  Their arguments and results are exact-ledger indices, so the
strict and near-cubic cursors cannot be accidentally exchanged. -/

/-- Node `[137]`, first production: `lem:exact-surplus-pair-charge-partition`
on the literal `[136]` residual. -/
noncomputable def selectedRoleFibrePartition
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .capacityTokenLedger, K .sparseUpperEnvelope,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .roleFibrePartition, K .capacityTokenLedger, K .sparseUpperEnvelope,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (roleFibrePartitionRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [roleFibrePartitionRow, K_eq_iff])

/-- Node `[20]`, the strict (non-near-cubic) surplus branch, run node by node
along the Part X/XI diagram on the literal `K .surplusAbove` ledger:

* `[125]` `sparseSurplusSurvivorRow` — `def:named-surplus-exits`: each of the
  five conclusions is a contradiction at the selected minimal counterexample,
  so the survivor fact is a row, not a decision (the manuscript's box);
* `[126]`--`[128]` activation, `[129]` baseline spine demand, `[130]` canonical
  pair split;
* `[130]` yes: `[131]` (mixed sparse-spine dependence, exact cubic baseline
  budget, incremental skeleton room, `lem:skeleton-dominates`), then the
  free-pair entropy sandwich into `[137]` (`selectedFreePairEntropySandwich`);
* `[130]` no: `[132]` blocked-pair routing — exit → `[133]` closes; blocker →
  `[134]` canonical pair ledger → `[135]` exact window-join pressure → `[136]`
  capacity-token ledger → `[137]` first production (`roleFibrePartitionRow`),
  then the coupled-excess decision `[137]` (`selectedCoupledExcessDichotomy`:
  no → `[138]`; yes → `[139]`/`[141]` class tests → `[140]`/`[142]`/`[143]`
  audits → `[144]`).

`selectedFreePairEntropySandwich` and `selectedCoupledExcessDichotomy` are the
next producers of this branch (see the audit rows `[131]`, `[137]`). -/
noncomputable def selectedStrictSurplusBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  -- `[125]`: the survivor fact, then `[126]`--`[128]` and `[129]`.
  let survivor := selectedSparseSurplusSurvivor history
  let activated := selectedSparseSurplusActivation survivor
  let baseline := selectedBaselineSpineDemand activated
  match selectedPairResponseIndependenceDichotomy baseline with
  | .left independentHistory =>
      -- `[131]`: the free-pair entropy sandwich, then `[137]`.
      let mixed := selectedMixedSparseSpineDependence independentHistory
      let budget := selectedExactCubicBaselineBudget mixed
      let room := selectedIncrementalSkeletonRoom budget
      let dominated := selectedSkeletonDominates room
      exact selectedFreePairEntropySandwich dominated
  | .right dependentHistory =>
      match selectedBlockedPairRoutingDichotomy dependentHistory with
      | .left exitHistory =>
          -- `[133]`: the exit contradicts the survivor fact of `[125]`.
          exact selectedSparsePairExitCloses exitHistory
      | .right blockerHistory =>
          -- `[134]`--`[136]`, then `[137]`'s first production.
          let pairs := selectedCanonicalPairFacts blockerHistory
          let joined := selectedExactWindowJoinPressure pairs
          let tokens := selectedCapacityTokenFacts joined
          let fibres := selectedRoleFibrePartition tokens
          exact selectedCoupledExcessDichotomy fibres

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

/-- **Nodes `[110]`--`[116]`: the route-8 residual of Part IX**, on the `[109]`
residual of the *silent* lane (`[94]`, `lem:typeA-unpeeled-silent-routing`;
index-polymorphic).  `[110]` `route8ResidualProfileRow`
(`def:typeA-silent-core-residual`: the saturated receiver survives only through
exit `(8)`, no decorated handoff fan); `[111]` `route8GlobalSqueezeRow` (the
profile lies on the large-budget branch, `K .largeBudgetResidual`); `[112]`
`route8BasinBurdenRow` (`lem:typeA-route8-burden` from the silent-excess count
`[94]`, `K .typeAVisibleFirstExcess`: `S_sil^exc(X) ≥ s·D_A(X)`); `[113]`
`route8LargeBudgetDeficitRow` (`def:typeA-large-budget-deficit`); `[114]`
`route8CarrierCoreRow` (canonical minimal target-complete carrier cores in the
declared `u`-supported response algebra); `[115]`--`[116]`
`route8SmallCoreCollapseRow` (`lem:typeA-one-terminal-collapse`: a zero/one
essential-core entry triggers exits `(4)`--`(7)`, absent here).  Next producer:
`[117]`, `selectedRouteEightCarrierDichotomy` — the paper's "some entry has
`π_𝒳(ξ) ≤ 2`?" on the indexed route-8 collection: its census inputs
(`entries` = the indexed trace-basin entries `(u, B_u)` of the extracted
collection `𝒳_A`, `core` = essential carrier cores, `supply` = the boundary
incidences `def⁺(R)`, `ambient = |R|`, and the private-carrier rate
`τ < 3/13` read from the arm's density fact) are what `K .route8TwoCarrierReduction`
/ `K .route8PrivateCarrierBudget` / `K .route8NoTwoCarrierContradiction` consume,
and they are not yet facts of this residual. -/
noncomputable def selectedRouteEightResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .typeAVisibleFirstExcess) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known) : False := by
  -- `[110]`
  let profile :=
    (route8ResidualProfileRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, profileFresh])
  -- `[111]`
  let squeezed :=
    (route8GlobalSqueezeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      profile (by simp [K_eq_iff, squeezeFresh])
  -- `[112]`
  let burdened :=
    (route8BasinBurdenRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      squeezed (by simp [K_eq_iff, burdenFresh])
  -- `[113]`
  let deficit :=
    (route8LargeBudgetDeficitRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      burdened (by simp [K_eq_iff, deficitFresh])
  -- `[114]`
  let cored :=
    (route8CarrierCoreRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      deficit (by simp [K_eq_iff, coreFresh])
  -- `[115]`--`[116]`
  let collapsed :=
    (route8SmallCoreCollapseRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cored (by simp [K_eq_iff, collapseFresh])
  -- `[117]`: the two-carrier decision on the indexed route-8 collection — the
  -- next producer.
  exact selectedRouteEightCarrierDichotomy collapsed

/-- **Node `[108]` → Type B `[65]` on the decorated envelope**: the admissible
Type B handoff interface committed at `[108]` (`K .typeAExitSevenHandoff`) enters
the Type B branch at `[65]` with the decorated envelope's assigned support
(`typeBDecoratedAssignedSupportRow`, `def:decorated-fan-envelope`,
`def:canonical-decomp`).  Next producer: `[67]`--`[85]` on the decorated envelope
(`selectedTypeBDecoratedContinuation`; the ordinary-support chain
`selectedTypeBHighSurplusContinuation` reads `K .typeBAssignedSupport` of the
ordinary support and its rows are stated on that support, so the decorated
envelope's `[67]`+ needs the envelope-context statements). -/
noncomputable def selectedTypeADecoratedHandoff
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known) : False := by
  let assigned :=
    (typeBDecoratedAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, decoratedFresh])
  exact selectedTypeBDecoratedContinuation assigned

/-- **Nodes `[76]`/`[77]` and `[85]` → `[123]`: the Type B mass residual joins the
large-budget closure.**  `prop:typeB-bridge-sublinear`: the Type B bridge/fan
residuals carry mass `o(|R|)`, so the linear large-budget deficit is not theirs;
`thm:branch-kill` records that on the large-budget residual with a negative
support (`branchKillClosedRow`: `K .largeBudgetResidual ∧` the selected negative
piece), and the residual is handed to `thm:large-budget-route8-only`, the
pressure descent `[123]` — the next producer `selectedLargeBudgetPressureDescent`
(the global join of the Type A target-defect/route-8 ledger, the Type B bridge
mass and the deficit `D_A ≥ (¼ − τ)|R| − o(|R|)`, with `τ` read from the arm's
density fact). -/
noncomputable def selectedTypeBRoute8Continuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (branchKillFresh : K .branchKillClosed ∉ known) : False := by
  let killed :=
    (branchKillClosedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, branchKillFresh])
  exact selectedLargeBudgetPressureDescent killed

/-- **Nodes `[103]`--`[109]`: exits `(5)`--`(7)` and the route-8 residual**, on the
saturated-handoff state after exit `(4)` is absent (index-polymorphic).
`[103]` exit `(5)`: a target-complete proper-support compression closes at
`[104]` against `cor:uncompressible`.  `[105]` exit `(6)`: a delocalizing
response equality is localized at `[106]` — proper scope closes against
`lem:replacement` (`K .replacementExclusion`), global scope against the
selection's minimality.  `[107]` exit `(7)`: the decorated handoff fan envelope
is committed with its admissible Type B interface at `[108]` and returns to the
Type B handoff (`[65]`), the next producer on that lane; its absence is `[109]`,
the route-8 residual continued in Part IX (`[110]`, the next producer). -/
noncomputable def selectedTypeAExitFiveToSeven
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (closureFresh : closed ∉ known) : False := by
  -- `[103]`
  match typeAExitFiveDichotomy (data := spineData) history fiveFresh fiveFreeFresh with
  | .left fiveHistory =>
      -- `[104]`
      exact (closeIncompatible fiveHistory (K .uncompressible) (K .typeAExitFive)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
  | .right fiveFree =>
      -- `[105]`
      match typeAExitSixDichotomy (data := spineData) fiveFree
          (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh]) with
      | .left sixHistory =>
          -- `[106]`
          match typeAExitSixScopeDichotomy (data := spineData) sixHistory
              (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh]) with
          | .left properHistory =>
              exact (closeIncompatible properHistory (K .replacementExclusion)
                (K .typeAExitSixProper) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)
          | .right globalHistory =>
              exact (closeIncompatible globalHistory (K .selection)
                (K .typeAExitSixGlobal) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)
      | .right sixFree =>
          -- `[107]`
          match typeAExitSevenDichotomy (data := spineData) sixFree
              (by simp [K_eq_iff, sevenProducedFresh])
              (by simp [K_eq_iff, sevenFreeFresh]) with
          | .left producedHistory =>
              -- `[108]`: the admissible Type B handoff interface; the decorated
              -- envelope enters Type B at `[65]` — the next producer.
              let handoff :=
                (typeAExitSevenHandoffRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  producedHistory (by simp [K_eq_iff, sevenHandoffFresh])
              exact selectedTypeADecoratedHandoff handoff (by simp [K_eq_iff, decoratedFresh])
          | .right route8History =>
              -- `[109]` on the *visible* lane: `lem:typeA-visible-entry` — a
              -- saturated receiver with a completion port carrying four visible
              -- receiver-entry returns realizes one of exits `(1)`--`(7)`
              -- (`lem:typeA-continuation-routing` on the four response
              -- coordinates, `lem:typeA-cubic-switch-absorption`,
              -- `lem:typeA-high-degree-handoff` force exit `(7)`), so exit
              -- `(8)` does not occur here — the next producer.
              exact selectedTypeAVisibleRouteEightImpossible route8History

/-- The silent-lane copy of `selectedTypeAExitFiveToSeven` (`[94]` →
`[101]`--`[109]`): identical exits `(5)`--`(7)`, and the exit-`(8)` residual
`[109]` continues into Part IX (`selectedRouteEightResidual`), which needs the
silent-excess count `[94]` and the large-budget residual on the ledger. -/
noncomputable def selectedTypeAExitFiveToSevenSilent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .typeAVisibleFirstExcess) known]
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (closureFresh : closed ∉ known) : False := by
  -- `[103]`
  match typeAExitFiveDichotomy (data := spineData) history fiveFresh fiveFreeFresh with
  | .left fiveHistory =>
      -- `[104]`
      exact (closeIncompatible fiveHistory (K .uncompressible) (K .typeAExitFive)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
  | .right fiveFree =>
      -- `[105]`
      match typeAExitSixDichotomy (data := spineData) fiveFree
          (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh]) with
      | .left sixHistory =>
          -- `[106]`
          match typeAExitSixScopeDichotomy (data := spineData) sixHistory
              (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh]) with
          | .left properHistory =>
              exact (closeIncompatible properHistory (K .replacementExclusion)
                (K .typeAExitSixProper) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)
          | .right globalHistory =>
              exact (closeIncompatible globalHistory (K .selection)
                (K .typeAExitSixGlobal) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)
      | .right sixFree =>
          -- `[107]`
          match typeAExitSevenDichotomy (data := spineData) sixFree
              (by simp [K_eq_iff, sevenProducedFresh])
              (by simp [K_eq_iff, sevenFreeFresh]) with
          | .left producedHistory =>
              -- `[108]`: the admissible Type B handoff interface; the decorated
              -- envelope enters Type B at `[65]` — the next producer.
              let handoff :=
                (typeAExitSevenHandoffRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  producedHistory (by simp [K_eq_iff, sevenHandoffFresh])
              exact selectedTypeADecoratedHandoff handoff (by simp [K_eq_iff, decoratedFresh])
          | .right route8History =>
              -- `[109]` → `[110]`: the route-8 residual of Part IX on the silent
              -- lane.
              exact selectedRouteEightResidual route8History
                (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, coreFresh]) (by simp [K_eq_iff, collapseFresh])

/-- **Nodes `[101]`--`[102]` and their loop back to `[89]`**, on the shared
saturated exit entry (index-polymorphic).  `lem:typeA-exit4-finite-descent` is
put on the ledger for `[123]`; then `[101]` tests exit `(4)` at the entry state.
Yes: `[102]` peels the witness's load (`lem:typeA-exit4-discharge`) and the
"recompute `L₄`" loop is the finite descent `typeAExitFourRetestDichotomy`,
which ends either at a saturated state with no further exit-`(4)` witness — the
hypothesis of exits `(5)`--`(8)` — or at an unsaturated peeled state whose
receiver charge is nonnegative (`lem:typeA-exit4-peeling-charge`) and whose
peeled loads are target-defect entries: the retest at `[89]` with the
target-defect ledger (Part IX `[123]`), the next producer.  No: exits
`(5)`--`(8)` at the entry state. -/
noncomputable def selectedTypeAExitFourChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (peeledFresh : K .typeAExitFourPeeled ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known)
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (closureFresh : closed ∉ known) : False := by
  -- `lem:typeA-exit4-finite-descent` on the ledger (read again at `[123]`).
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, descentFresh])
  -- `[101]`
  match typeAExitFourDichotomy (data := spineData) descended
      (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh]) with
  | .left exitFourHistory =>
      -- `[102]`
      let peeled :=
        (typeAExitFourPeelingStepRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          exitFourHistory (by simp [K_eq_iff, peeledFresh])
      -- `[102]` → `[89]`: recompute `L₄` — the finite exit-`(4)` descent.
      match typeAExitFourRetestDichotomy (data := spineData) peeled
          (by simp [K_eq_iff, exitFourFreeFresh]) (by simp [K_eq_iff, dischargedFresh]) with
      | .left terminalHistory =>
          exact selectedTypeAExitFiveToSeven terminalHistory
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right dischargedHistory =>
          -- `[89]` retest of the discharged receiver with its peeled
          -- target-defect loads (Part IX pressure ledger `[123]`) — the next
          -- producer.
          exact selectedTypeAExitFourDischargedRetest dischargedHistory
  | .right freeHistory =>
      exact selectedTypeAExitFiveToSeven freeHistory
        (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
        (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
        (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
        (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
        (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
        (by simp [K_eq_iff, closureFresh])

/-- The silent-lane copy of `selectedTypeAExitFourChain` (`[94]` → `[101]`--`[109]`
→ Part IX). -/
noncomputable def selectedTypeAExitFourChainSilent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .typeAVisibleFirstExcess) known]
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (peeledFresh : K .typeAExitFourPeeled ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known)
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (closureFresh : closed ∉ known) : False := by
  -- `lem:typeA-exit4-finite-descent` on the ledger (read again at `[123]`).
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, descentFresh])
  -- `[101]`
  match typeAExitFourDichotomy (data := spineData) descended
      (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh]) with
  | .left exitFourHistory =>
      -- `[102]`
      let peeled :=
        (typeAExitFourPeelingStepRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          exitFourHistory (by simp [K_eq_iff, peeledFresh])
      -- `[102]` → `[89]`: recompute `L₄` — the finite exit-`(4)` descent.
      match typeAExitFourRetestDichotomy (data := spineData) peeled
          (by simp [K_eq_iff, exitFourFreeFresh]) (by simp [K_eq_iff, dischargedFresh]) with
      | .left terminalHistory =>
          exact selectedTypeAExitFiveToSevenSilent terminalHistory
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, coreFresh]) (by simp [K_eq_iff, collapseFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right dischargedHistory =>
          -- `[89]` retest of the discharged receiver with its peeled
          -- target-defect loads (Part IX pressure ledger `[123]`) — the next
          -- producer.
          exact selectedTypeAExitFourDischargedRetest dischargedHistory
  | .right freeHistory =>
      exact selectedTypeAExitFiveToSevenSilent freeHistory
        (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
        (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
        (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
        (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
        (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
        (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
        (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
        (by simp [K_eq_iff, coreFresh]) (by simp [K_eq_iff, collapseFresh])
        (by simp [K_eq_iff, closureFresh])

/-- **Node `[99]` → `[101]`, the visible lane**: the shared saturated exit entry
at the empty peeling set (`lem:typeA-unpeeled-visible-routing`), then the exit
segment `[101]`--`[109]`. -/
noncomputable def selectedTypeAVisibleExitFour
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitThreeFree) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known)
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (peeledFresh : K .typeAExitFourPeeled ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known)
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (closureFresh : closed ∉ known) : False := by
  let entered :=
    (typeAVisibleExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, entryFresh])
  exact selectedTypeAExitFourChain entered
    (by simp [K_eq_iff, descentFresh]) (by simp [K_eq_iff, exitFourFresh])
    (by simp [K_eq_iff, exitFourFreeFresh]) (by simp [K_eq_iff, peeledFresh])
    (by simp [K_eq_iff, dischargedFresh])
    (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
    (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
    (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
    (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
    (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
    (by simp [K_eq_iff, closureFresh])

/-- **Node `[94]` → `[101]`, the silent lane**: the shared saturated exit entry
at the empty peeling set (`lem:typeA-unpeeled-silent-routing`), then the exit
segment `[101]`--`[109]`. -/
noncomputable def selectedTypeASilentExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAVisibleFirstExcess) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known)
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (peeledFresh : K .typeAExitFourPeeled ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known)
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (closureFresh : closed ∉ known) : False := by
  let entered :=
    (typeASilentExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, entryFresh])
  exact selectedTypeAExitFourChainSilent entered
    (by simp [K_eq_iff, descentFresh]) (by simp [K_eq_iff, exitFourFresh])
    (by simp [K_eq_iff, exitFourFreeFresh]) (by simp [K_eq_iff, peeledFresh])
    (by simp [K_eq_iff, dischargedFresh])
    (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
    (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
    (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
    (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
    (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
    (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
    (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
    (by simp [K_eq_iff, coreFresh]) (by simp [K_eq_iff, collapseFresh])
    (by simp [K_eq_iff, closureFresh])

/-- **Nodes `[95]`--`[100]`: the saturated exit chain, exits `(1)`--`(3)`**, on
the `[93]` visible-entry residual (index-polymorphic).  `def:typeA-saturated-exits`
and `lem:typeA-exits-discharged`: exit `(1)` — an anchored return through the
saturated receiver's completion port of Mersenne length — is a power-of-two
cycle by `lem:return-equivalence`, closed at `[96]` against the return-avoidance
invariant `[5]`--`[7]`; exit `(2)` — two internally disjoint receiver-entry
returns through one port with accepted total length — is a cycle
(`lem:typeA-common-port-return-cycle`), closed at `[98]` against the selection;
exit `(3)` — a `P₁₃` label collision — closes at `[100]` against the selection.
The exit-`(3)`-free residual enters exit `(4)`, `[101]`, the next producer. -/
noncomputable def selectedTypeAVisibleExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAVisibleEntry) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    (returnFresh : K .typeAExitOneReturn ∉ known)
    (oneFreeFresh : K .typeAExitOneFree ∉ known)
    (thetaFresh : K .typeAExitTwoTheta ∉ known)
    (twoFreeFresh : K .typeAExitTwoFree ∉ known)
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (threeFreeFresh : K .typeAExitThreeFree ∉ known)
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known)
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known)
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known)
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known)
    (peeledFresh : K .typeAExitFourPeeled ∉ known)
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known)
    (fiveFresh : K .typeAExitFive ∉ known)
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known)
    (sixFresh : K .typeAExitSix ∉ known)
    (sixFreeFresh : K .typeAExitSixFree ∉ known)
    (sixProperFresh : K .typeAExitSixProper ∉ known)
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known)
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known)
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known)
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known)
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (closureFresh : closed ∉ known) : False := by
  -- `[95]`
  match typeAExitOneDichotomy (data := spineData) history returnFresh oneFreeFresh with
  | .left returnHistory =>
      -- `[96]`
      exact (closeIncompatible returnHistory (K .returnAvoidance) (K .typeAExitOneReturn)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
  | .right oneFree =>
      -- `[97]`
      match typeAExitTwoDichotomy (data := spineData) oneFree
          (by simp [K_eq_iff, thetaFresh]) (by simp [K_eq_iff, twoFreeFresh]) with
      | .left thetaHistory =>
          -- `[98]`
          exact (closeIncompatible thetaHistory (K .selection) (K .typeAExitTwoTheta)
            (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
      | .right twoFree =>
          -- `[99]`
          match typeAExitThreeDichotomy (data := spineData) twoFree
              (by simp [K_eq_iff, collisionFresh]) (by simp [K_eq_iff, threeFreeFresh]) with
          | .left collisionHistory =>
              -- `[100]`
              exact (closeIncompatible collisionHistory (K .selection)
                (K .typeAExitThreeCollision)
                (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
          | .right threeFree =>
              -- `[101]`--`[109]`: exit `(4)` and the rest of the exit segment on
              -- the visible lane.
              exact selectedTypeAVisibleExitFour threeFree
                (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
                (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
                (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
                (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
                (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
                (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
                (by simp [K_eq_iff, sevenProducedFresh])
                (by simp [K_eq_iff, sevenFreeFresh]) (by simp [K_eq_iff, sevenHandoffFresh])
                (by simp [K_eq_iff, decoratedFresh])
                (by simp [K_eq_iff, closureFresh])

/-- **Nodes `[63]`, `[86]`--`[94]`: the Type A entry**, on the `[62]` Type A
residual of either spine arm (index-polymorphic, as `selectedNetChargeContinuation`).

`[86]`--`[88]`: `def:typeA-support` is `def:admissible` with `σ(X) = 0`; the
receiver routing `lem:typeA-receiver-loads` and the threshold algebra
`lem:typeA-threshold-algebra` (`H₀ ≤ 4, H₁ ≤ 8, H₂ ≤ 12` at the registered
values) are `typeAReceiverRoutingRow`.  `[89]` asks whether some receiver is
saturated (`L(w) ≥ s·q(w)`).  No: `[90]` `L(w) ≤ s·q(w) − 1`, `[91]`
`lem:typeA-unsaturated-discharge` gives `|X| ≤ s·def⁺(X)`, and `[92]` closes
against the support's negative net charge `s·def⁺(X) < |X| + s·σ(X)` with
`σ(X) = 0`.  Yes: `lem:typeA-port-return` (every completion port has an
anchored return, from `lem:bridgeless`) and `[93]`: does a port of the
saturated receiver see `s` visible receiver-entry returns?  Yes → the exit
chain `[95]`--`[107]`; no → `[94]` `S_sil^exc(X) ≥ s·D_A(X)` → exits
`[101]`--`[107]`.  Both exit lanes are the next loud producers. -/
noncomputable def selectedTypeALowSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .selection) known]
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by simp [K_eq_iff])
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by simp [K_eq_iff])
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by simp [K_eq_iff])
    (portFresh : K .typeAPortReturn ∉ known := by simp [K_eq_iff])
    (visibleFresh : K .typeAVisibleEntry ∉ known := by simp [K_eq_iff])
    (excessFresh : K .typeAVisibleFirstExcess ∉ known := by simp [K_eq_iff])
    -- exits `(1)`--`(3)`, `[95]`--`[100]`
    [FactKeys.Has (K .returnAvoidance) known]
    (returnFresh : K .typeAExitOneReturn ∉ known := by simp [K_eq_iff])
    (oneFreeFresh : K .typeAExitOneFree ∉ known := by simp [K_eq_iff])
    (thetaFresh : K .typeAExitTwoTheta ∉ known := by simp [K_eq_iff])
    (twoFreeFresh : K .typeAExitTwoFree ∉ known := by simp [K_eq_iff])
    (collisionFresh : K .typeAExitThreeCollision ∉ known := by simp [K_eq_iff])
    (threeFreeFresh : K .typeAExitThreeFree ∉ known := by simp [K_eq_iff])
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known := by simp [K_eq_iff])
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known := by simp [K_eq_iff])
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known := by simp [K_eq_iff])
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known := by simp [K_eq_iff])
    (peeledFresh : K .typeAExitFourPeeled ∉ known := by simp [K_eq_iff])
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known := by simp [K_eq_iff])
    (fiveFresh : K .typeAExitFive ∉ known := by simp [K_eq_iff])
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known := by simp [K_eq_iff])
    (sixFresh : K .typeAExitSix ∉ known := by simp [K_eq_iff])
    (sixFreeFresh : K .typeAExitSixFree ∉ known := by simp [K_eq_iff])
    (sixProperFresh : K .typeAExitSixProper ∉ known := by simp [K_eq_iff])
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known := by simp [K_eq_iff])
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known := by simp [K_eq_iff])
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known := by simp [K_eq_iff])
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known := by simp [K_eq_iff])
    -- `[108]` → Type B `[65]` (decorated) and `[109]` → Part IX `[110]`--`[116]`.
    [FactKeys.Has (K .largeBudgetResidual) known]
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by simp [K_eq_iff])
    (profileFresh : K .route8ResidualProfile ∉ known := by simp [K_eq_iff])
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by simp [K_eq_iff])
    (burdenFresh : K .route8BasinBurden ∉ known := by simp [K_eq_iff])
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by simp [K_eq_iff])
    (coreFresh : K .route8CarrierCore ∉ known := by simp [K_eq_iff])
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff]) :
    False := by
  -- `[86]`--`[88]`
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      history (by simp [K_eq_iff, routingFresh])
  -- `[89]`
  match typeASaturationDichotomy (data := spineData) routed
      (by simp [K_eq_iff, saturatedFresh]) (by simp [K_eq_iff, unsaturatedFresh]) with
  | .right unsaturatedHistory =>
      -- `[90]`--`[91]`
      let discharged :=
        (typeAUnsaturatedDischargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unsaturatedHistory (by simp [K_eq_iff, dischargeFresh])
      -- `[92]`: `|X| ≤ s·def⁺(X)` against `s·def⁺(X) < |X| + s·σ(X)`, `σ(X) = 0`.
      obtain ⟨packing, _valid, _maximal, component, _present, negative, zero, bound⟩ :=
        (discharged.get (K .typeAUnsaturatedDischarge)).down
      have negative' := negative
      unfold Graph.FiniteObject.NegativeNetCharge at negative'
      rw [zero] at negative'
      omega
  | .left saturatedHistory =>
      -- `lem:typeA-port-return`
      let ports :=
        (typeAPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          saturatedHistory (by simp [K_eq_iff, portFresh])
      -- `[93]`
      match typeAVisibleEntryDichotomy (data := spineData) ports
          (by simp [K_eq_iff, visibleFresh]) (by simp [K_eq_iff, excessFresh]) with
      | .left visibleHistory =>
          -- `[95]`--`[107]`: the saturated exit chain on the visible arm.
          exact selectedTypeAVisibleExitChain visibleHistory
            (by simp [K_eq_iff, returnFresh]) (by simp [K_eq_iff, oneFreeFresh])
            (by simp [K_eq_iff, thetaFresh]) (by simp [K_eq_iff, twoFreeFresh])
            (by simp [K_eq_iff, collisionFresh]) (by simp [K_eq_iff, threeFreeFresh])
            (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
            (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
            (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right excessHistory =>
          -- `[94]` → `[101]`--`[107]`: the exit chain from exit `(4)` on the
          -- silent-excess arm.
          exact selectedTypeASilentExitChain excessHistory
            (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
            (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
            (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, coreFresh]) (by simp [K_eq_iff, collapseFresh])
            (by simp [K_eq_iff, closureFresh])

/-- **Nodes `[72]`--`[76]` / `[81]`--`[85]`: the certificate-marked Type B
ledger**, on any residual carrying `K .fanCertificateMarked` (the `[71]` yes arm on
the heavy path, the `[80]` yes arm on the degree-four path).  `[72]`/`[81]` first
half: `directCycleDichotomy` (`lem:typeB-direct-fan-window-cycles`,
`lem:typeB-two-window-cycles`) — the configuration arm builds a cycle of accepted
length, refuted by the selection; second half: `b2AssignmentDichotomy` (B2 of
`def:typeB-bridge-statements`, `lem:typeB-bridge-to-overlap`).  B2 yes: `[74]`/`[82]`
`hybridEntryRow` (`lem:typeB-hybrid-B1`), `disjointPostLedgerComponentsRow` (the
exact augmented-ledger refinement and post-ledger core hygiene), the `[76]`/`[85]`
charge rows (`typeBSelectedFanChargeRow`, `typeBExclusionChargeRow`,
`prop:typeB-bridge-reduction`) and `typeBExclusionDichotomy`: excluded ⇒
`N₀(X) ≥ 0` against the negative support (`closeImpossible`); residual ⇒
`typeBExclusionResidualMassRow` (`def:typeB-residual-mass`).  B2 no: `[73]`/`[83]`
minimal overlap obstruction ⇒ `typeBOverlapObstructionMassRow` (`[75]`/`[84]`).
Every mass residual is `[76]`/`[85]`'s "Type B cannot carry the linear deficit
outside route 8" input and is handed to `[77]`, the route-8 continuation of Part
IX (`prop:typeB-bridge-sublinear`, `thm:large-budget-route8-only`) — the next
producer `selectedTypeBRoute8Continuation`.  Index-polymorphic over the arm's
ledger. -/
noncomputable def selectedTypeBMarkedLedger
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fanCertificateMarked) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (branchKillFresh : K .branchKillClosed ∉ known := by simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (selectedChargeFresh : K .typeBSelectedFanCharge ∉ known := by simp [K_eq_iff])
    (exclusionChargeFresh : K .typeBExclusionCharge ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff]) :
    False := by
  -- `[72]`/`[81]`, first half: a direct fan-window cycle?
  match directCycleDichotomy (data := spineData) history
      (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh]) with
  | .left cycleHistory =>
      -- The configuration is a cycle of accepted length in the selected object.
      obtain ⟨packing, valid, _maximal, _component, _present, _charge, _positive,
        _centre, _member, _high, directCycle⟩ :=
        (cycleHistory.get (K .typeBDirectCycle)).down
      exact (cycleHistory.get (K .selection)).down.1
        (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
          valid directCycle)
  | .right freeHistory =>
      -- `[72]`/`[81]`, second half: the B2 disjoint ledger?
      match b2AssignmentDichotomy (data := spineData) freeHistory
          (by simp [K_eq_iff, choiceFresh]) (by simp [K_eq_iff, obstructionFresh]) with
      | .left choiceHistory =>
          -- `[74]`/`[82]`: the hybrid B1 ledger and the exact disjoint post-ledger.
          let hybrid :=
            (hybridEntryRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              choiceHistory (by simp [K_eq_iff, hybridFresh])
          let ledger :=
            (disjointPostLedgerComponentsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              hybrid (by simp [K_eq_iff, ledgerFresh])
          -- `[76]`/`[85]`: the selected-entry charge and the B-ledger implication.
          let selectedCharge :=
            (typeBSelectedFanChargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              ledger (by simp [K_eq_iff, selectedChargeFresh])
          let charge :=
            (typeBExclusionChargeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              selectedCharge (by simp [K_eq_iff, exclusionChargeFresh])
          match typeBExclusionDichotomy (data := spineData) charge
              (by simp [K_eq_iff, excludedFresh])
              (by simp [K_eq_iff, exclusionResidualFresh]) with
          | .left excludedHistory =>
              -- `[74]`/`[82]` closes: `N₀(X) ≥ 0` against the negative support.
              exact (closeImpossible excludedHistory (K .typeBExcluded)
                (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)
          | .right residualHistory =>
              -- `[76]`/`[85]`: the exclusion residual's fan mass; `[77]` next.
              let mass :=
                (typeBExclusionResidualMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  residualHistory (by simp [K_eq_iff, exclusionMassFresh])
              exact selectedTypeBRoute8Continuation mass (by simp [K_eq_iff, branchKillFresh])
      | .right obstructionHistory =>
          -- `[73]`/`[83]`: minimal overlap obstruction; `[75]`/`[84]` fan mass.
          let mass :=
            (typeBOverlapObstructionMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              obstructionHistory (by simp [K_eq_iff, obstructionMassFresh])
          exact selectedTypeBRoute8Continuation mass (by simp [K_eq_iff, branchKillFresh])

/-- **Node `[64]`: the ordinary Type B entry**, on the `[62]` yes-residual of any
arm.  `[65]` (`typeBAssignedSupportRow`: the support's assigned fan centres are
its high centres, `def:canonical-decomp`), `[67]`
(`highCentreNormalFormRow`, `lem:heavy-neighbourhood-normal-form`), the `[68]`
heavy-centre split (`typeBFanDegreeDichotomy`); on the heavy arm `[69]`
(`typeBFanLocalDichotomyRow`, `cor:heavy-center-local-dichotomy`), `[70]`
(`fanCertificateCapRow`, `lem:fan-certificate`) and the `[71]` certificate split
(`fanCertificateDichotomy`, `def:marked-typeB-fan`).  Next producers: `[72]`
(the local fan-window ledger / B2 question) on the marked arm, `[75]` (bridge
fan-mass) on the residual arm, and `[78]` (the degree-four Part VII branch) on the
`[68]` no arm.  Index-polymorphic over the arm's ledger. -/
noncomputable def selectedTypeBHighSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBHighSurplus) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .tightEndpoint) known]
    (assignedFresh : K .typeBAssignedSupport ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (capFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    -- `[72]`--`[85]` on the same ledger (`selectedTypeBMarkedLedger`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (branchKillFresh : K .branchKillClosed ∉ known := by simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (selectedChargeFresh : K .typeBSelectedFanCharge ∉ known := by simp [K_eq_iff])
    (exclusionChargeFresh : K .typeBExclusionCharge ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff]) :
    False := by
  -- `[65]`: the ordinary Type B assigned support.
  let assigned :=
    (typeBAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, assignedFresh])
  -- `[67]`: `lem:heavy-neighbourhood-normal-form` at every high centre.
  let normal :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      assigned (by simp [K_eq_iff, normalFormFresh])
  -- `[68]`: some assigned fan centre heavy?
  match typeBFanDegreeDichotomy (data := spineData) normal
      (by simp [K_eq_iff, heavyFresh]) (by simp [K_eq_iff, degreeFourFresh]) with
  | .left heavyHistory =>
      -- `[69]`: `cor:heavy-center-local-dichotomy` at every heavy fan centre.
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by simp [K_eq_iff, localFresh])
      -- `[70]`: `lem:fan-certificate`, the certificate-marked degree cap.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          localDichotomy (by simp [K_eq_iff, capFresh])
      -- `[71]`: certificate labelling present at every assigned centre?
      match fanCertificateDichotomy (data := spineData) capped
          (by simp [K_eq_iff, markedFresh]) (by simp [K_eq_iff, residualFresh]) with
      | .left markedHistory =>
          -- `[72]`--`[76]`: the certificate-marked ledger; `[77]` next.
          exact selectedTypeBMarkedLedger markedHistory
            (by simp [K_eq_iff, branchKillFresh])
            (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh])
            (by simp [K_eq_iff, choiceFresh]) (by simp [K_eq_iff, obstructionFresh])
            (by simp [K_eq_iff, hybridFresh]) (by simp [K_eq_iff, ledgerFresh])
            (by simp [K_eq_iff, selectedChargeFresh])
            (by simp [K_eq_iff, exclusionChargeFresh])
            (by simp [K_eq_iff, excludedFresh]) (by simp [K_eq_iff, exclusionResidualFresh])
            (by simp [K_eq_iff, exclusionMassFresh]) (by simp [K_eq_iff, obstructionMassFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right residualHistory =>
          -- `[75]`: the fan-certificate residual centre is charged to the bridge
          -- fan mass (`def:typeB-residual-mass`); `[76]`/`[77]` next.
          let mass :=
            (fanCertificateResidualMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              residualHistory (by simp [K_eq_iff, certificateMassFresh])
          exact selectedTypeBRoute8Continuation mass (by simp [K_eq_iff, branchKillFresh])
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`: every assigned fan centre has degree `δ + 1`; the
      -- degree-four fan profile (`cor:degree-four-local-activation`).
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, degreeFourProfileFresh])
      -- `lem:fan-certificate` (the `[70]` cap, a fact of the object: every
      -- certificate-marked centre is capped by the label packing number), which
      -- `[82]`'s certificate-closed entries and the B1 budget read.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, capFresh])
      -- `[80]`: certificate labelling present at every assigned centre?
      match fanCertificateDichotomy (data := spineData) capped
          (by simp [K_eq_iff, markedFresh]) (by simp [K_eq_iff, residualFresh]) with
      | .left markedHistory =>
          -- `[81]`--`[85]`: the same certificate-marked ledger — `c ≤ 1` is the
          -- certificate-closed case of the B2 ledger, `c ≥ 2` its bridge-paid
          -- case; `[82]` closes, `[83]`/`[84]` charge the fan mass; `[85]` next.
          exact selectedTypeBMarkedLedger markedHistory
            (by simp [K_eq_iff, branchKillFresh])
            (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh])
            (by simp [K_eq_iff, choiceFresh]) (by simp [K_eq_iff, obstructionFresh])
            (by simp [K_eq_iff, hybridFresh]) (by simp [K_eq_iff, ledgerFresh])
            (by simp [K_eq_iff, selectedChargeFresh])
            (by simp [K_eq_iff, exclusionChargeFresh])
            (by simp [K_eq_iff, excludedFresh]) (by simp [K_eq_iff, exclusionResidualFresh])
            (by simp [K_eq_iff, exclusionMassFresh]) (by simp [K_eq_iff, obstructionMassFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right residualHistory =>
          -- `[84]`: certificate failure charged to the fan mass; `[85]` next.
          let mass :=
            (fanCertificateResidualMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              residualHistory (by simp [K_eq_iff, certificateMassFresh])
          exact selectedTypeBRoute8Continuation mass (by simp [K_eq_iff, branchKillFresh])

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
    [FactKeys.Has (K .largeBudgetResidual) known]
    (largeFresh : K .netChargeLarge ∉ known := by simp [K_eq_iff])
    (smallFresh : K .netChargeSmall ∉ known := by simp [K_eq_iff])
    (capFresh : K .netChargeCap ∉ known := by simp [K_eq_iff])
    (locFresh : K .netChargeLocalization ∉ known := by simp [K_eq_iff])
    (nonNegFresh : K .netChargeNonNegative ∉ known := by simp [K_eq_iff])
    (negFresh : K .netChargeNegative ∉ known := by simp [K_eq_iff])
    (supportFresh : K .negativeSupport ∉ known := by simp [K_eq_iff])
    (typeAFresh : K .typeALowSurplus ∉ known := by simp [K_eq_iff])
    (typeBFresh : K .typeBHighSurplus ∉ known := by simp [K_eq_iff])
    -- Type A `[63]`, `[86]`--`[94]` freshness on the same ledger.
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .selection) known]
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by simp [K_eq_iff])
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by simp [K_eq_iff])
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by simp [K_eq_iff])
    (portFresh : K .typeAPortReturn ∉ known := by simp [K_eq_iff])
    (visibleFresh : K .typeAVisibleEntry ∉ known := by simp [K_eq_iff])
    (excessFresh : K .typeAVisibleFirstExcess ∉ known := by simp [K_eq_iff])
    [FactKeys.Has (K .returnAvoidance) known]
    (returnFresh : K .typeAExitOneReturn ∉ known := by simp [K_eq_iff])
    (oneFreeFresh : K .typeAExitOneFree ∉ known := by simp [K_eq_iff])
    (thetaFresh : K .typeAExitTwoTheta ∉ known := by simp [K_eq_iff])
    (twoFreeFresh : K .typeAExitTwoFree ∉ known := by simp [K_eq_iff])
    (collisionFresh : K .typeAExitThreeCollision ∉ known := by simp [K_eq_iff])
    (threeFreeFresh : K .typeAExitThreeFree ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff])
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    (entryFresh : K .typeASaturatedExitEntry ∉ known := by simp [K_eq_iff])
    (descentFresh : K .typeAExitFourFiniteDescent ∉ known := by simp [K_eq_iff])
    (exitFourFresh : K .typeASaturatedHandoffExitFour ∉ known := by simp [K_eq_iff])
    (exitFourFreeFresh : K .typeASaturatedHandoffExitFourFree ∉ known := by simp [K_eq_iff])
    (peeledFresh : K .typeAExitFourPeeled ∉ known := by simp [K_eq_iff])
    (dischargedFresh : K .typeAExitFourReceiverDischarged ∉ known := by simp [K_eq_iff])
    (fiveFresh : K .typeAExitFive ∉ known := by simp [K_eq_iff])
    (fiveFreeFresh : K .typeAExitFiveFree ∉ known := by simp [K_eq_iff])
    (sixFresh : K .typeAExitSix ∉ known := by simp [K_eq_iff])
    (sixFreeFresh : K .typeAExitSixFree ∉ known := by simp [K_eq_iff])
    (sixProperFresh : K .typeAExitSixProper ∉ known := by simp [K_eq_iff])
    (sixGlobalFresh : K .typeAExitSixGlobal ∉ known := by simp [K_eq_iff])
    (sevenProducedFresh : K .typeAExitSevenProduced ∉ known := by simp [K_eq_iff])
    (sevenFreeFresh : K .typeAExitSevenFree ∉ known := by simp [K_eq_iff])
    (sevenHandoffFresh : K .typeAExitSevenHandoff ∉ known := by simp [K_eq_iff])
    -- Type B `[64]`+ keys (`selectedTypeBHighSurplusContinuation`).
    [FactKeys.Has (K .tightEndpoint) known]
    (typeBAssignedFresh : K .typeBAssignedSupport ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (fanHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (fanDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (fanLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (fanCapFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (fanMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (fanResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    -- Type B `[72]`--`[85]` keys (`selectedTypeBMarkedLedger`).
    [FactKeys.Has (K .uncompressible) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (selectedChargeFresh : K .typeBSelectedFanCharge ∉ known := by simp [K_eq_iff])
    (exclusionChargeFresh : K .typeBExclusionCharge ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    -- `[108]` decorated handoff, `[110]`--`[116]` route 8, `[76]`/`[85]` → `[123]`.
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by simp [K_eq_iff])
    (profileFresh : K .route8ResidualProfile ∉ known := by simp [K_eq_iff])
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by simp [K_eq_iff])
    (burdenFresh : K .route8BasinBurden ∉ known := by simp [K_eq_iff])
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by simp [K_eq_iff])
    (coreFresh : K .route8CarrierCore ∉ known := by simp [K_eq_iff])
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by simp [K_eq_iff])
    (branchKillFresh : K .branchKillClosed ∉ known := by simp [K_eq_iff]) :
    False := by
  match netChargeOrderDichotomy (data := spineData) history largeFresh smallFresh with
  | .right smallHistory =>
      -- `[57]` small-order complement, `K .netChargeSmall`: the current
      -- object's order is below the registered `netCapCutoff`.  The manuscript
      -- proves `thm:main` only under its standing convention ("`for large n`
      -- abbreviates `for all sufficiently large n`", Conventions) — no sentence
      -- of the manuscript covers this finite range and it names no finite
      -- verification; the official statement is for every order, so the
      -- producer below needs a registered finite check of the presentation
      -- that the manuscript does not contain.  Left loud, deliberately.
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
                (by simp [K_eq_iff, routingFresh]) (by simp [K_eq_iff, saturatedFresh])
                (by simp [K_eq_iff, unsaturatedFresh]) (by simp [K_eq_iff, dischargeFresh])
                (by simp [K_eq_iff, portFresh]) (by simp [K_eq_iff, visibleFresh])
                (by simp [K_eq_iff, excessFresh])
                (by simp [K_eq_iff, returnFresh]) (by simp [K_eq_iff, oneFreeFresh])
                (by simp [K_eq_iff, thetaFresh]) (by simp [K_eq_iff, twoFreeFresh])
                (by simp [K_eq_iff, collisionFresh]) (by simp [K_eq_iff, threeFreeFresh])
                (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
                (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
                (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
                (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
                (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
                (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
                (by simp [K_eq_iff, sevenProducedFresh])
                (by simp [K_eq_iff, sevenFreeFresh]) (by simp [K_eq_iff, sevenHandoffFresh])
                (by simp [K_eq_iff, decoratedFresh])
                (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, coreFresh]) (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, closureFresh])
          | .right typeBHistory =>
              exact selectedTypeBHighSurplusContinuation typeBHistory
                (by simp [K_eq_iff, typeBAssignedFresh]) (by simp [K_eq_iff, normalFormFresh])
                (by simp [K_eq_iff, fanHeavyFresh]) (by simp [K_eq_iff, fanDegreeFourFresh])
                (by simp [K_eq_iff, fanLocalFresh]) (by simp [K_eq_iff, fanCapFresh])
                (by simp [K_eq_iff, fanMarkedFresh]) (by simp [K_eq_iff, fanResidualFresh])
                (by simp [K_eq_iff, branchKillFresh])
                (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh])
                (by simp [K_eq_iff, choiceFresh]) (by simp [K_eq_iff, obstructionFresh])
                (by simp [K_eq_iff, hybridFresh]) (by simp [K_eq_iff, ledgerFresh])
                (by simp [K_eq_iff, selectedChargeFresh])
                (by simp [K_eq_iff, exclusionChargeFresh])
                (by simp [K_eq_iff, excludedFresh]) (by simp [K_eq_iff, exclusionResidualFresh])
                (by simp [K_eq_iff, exclusionMassFresh]) (by simp [K_eq_iff, obstructionMassFresh])
                (by simp [K_eq_iff, certificateMassFresh])
                (by simp [K_eq_iff, degreeFourProfileFresh])
                (by simp [K_eq_iff, closureFresh])



/-! ## Nodes `[25]`--`[55]` on any near-cubic residual

The remainder normalization, boundary demand, stub supply, wedge lower bound,
curvature target-rank and circuit (`[25]`--`[31]`), the rank split `[32]` with
Branch D closed on its yes arm (`[33]`--`[46]`), `cor:forced-curvature-cost`
`[48]`, the remainder-entropy split `[49]`/`[50]`, the window-plus-remainder
accounting and entropy cap `[52]`/`[53]` with `[54]` closed when the comparison
retains a code, and Residual C `[55]` on both entropy arms.  The rows are the
same on every arm of the spine; only node `[56]`'s density input differs, so
this def returns the two surviving Residual C cursors and, separately, the
`[53]`-active cursor on which the `[22]` comparison retains no code at all
(`def:curvature-target-rank`'s complementary cold residual), for the caller to
close from its own arm's facts. -/
noncomputable def selectedSpineToLargeBudget
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    (remainderFresh : K .remainderNormalized ∉ known := by simp [K_eq_iff])
    (boundaryFresh : K .boundaryDemand ∉ known := by simp [K_eq_iff])
    (stubFresh : K .stubSupply ∉ known := by simp [K_eq_iff])
    (wedgeFresh : K .wedgeSupply ∉ known := by simp [K_eq_iff])
    (profileFresh : K .exactResponseProfile ∉ known := by simp [K_eq_iff])
    (admissibleFresh : K .admissibleRankQuotient ∉ known := by simp [K_eq_iff])
    (rankFresh : K .curvatureTargetRank ∉ known := by simp [K_eq_iff])
    (circuitFresh : K .targetRankCircuit ∉ known := by simp [K_eq_iff])
    (dropFresh : K .curvatureRankDrop ∉ known := by simp [K_eq_iff])
    (fullFresh : K .curvatureFullRank ∉ known := by simp [K_eq_iff])
    (dependenceFresh : K .branchDependence ∉ known := by simp [K_eq_iff])
    (defectFresh : K .contextDefect ∉ known := by simp [K_eq_iff])
    (universalFresh : K .contextUniversal ∉ known := by simp [K_eq_iff])
    (compressionFresh : K .atomCompression ∉ known := by simp [K_eq_iff])
    (delocalizedFresh : K .delocalizedSupport ∉ known := by simp [K_eq_iff])
    (properFresh : K .properDelocalization ∉ known := by simp [K_eq_iff])
    (globalFresh : K .globalDelocalization ∉ known := by simp [K_eq_iff])
    (repairFresh : K .repairIdentity ∉ known := by simp [K_eq_iff])
    (barrierFresh : K .globalBarrier ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff])
    (costFresh : K .forcedCurvatureCost ∉ known := by simp [K_eq_iff])
    (highFresh : K .remainderEntropyHigh ∉ known := by simp [K_eq_iff])
    (lowFresh : K .remainderEntropyLow ∉ known := by simp [K_eq_iff])
    (packageFresh : K .entropyPackageDemand ∉ known := by simp [K_eq_iff])
    (activeFresh : K .entropyCapActive ∉ known := by simp [K_eq_iff])
    (largeFresh : K .largeBudgetResidual ∉ known := by simp [K_eq_iff]) :
    Sum
      (Sum
        (ExactLedger EGInput.{u} selected
          (K .largeBudgetResidual :: K .entropyPackageDemand :: K .remainderEntropyHigh ::
            K .forcedCurvatureCost :: K .curvatureFullRank :: K .targetRankCircuit ::
            K .exactResponseProfile :: K .admissibleRankQuotient :: K .curvatureTargetRank ::
            K .wedgeSupply :: K .stubSupply :: K .boundaryDemand :: K .remainderNormalized ::
            known))
        (ExactLedger EGInput.{u} selected
          (K .largeBudgetResidual :: K .remainderEntropyLow ::
            K .forcedCurvatureCost :: K .curvatureFullRank :: K .targetRankCircuit ::
            K .exactResponseProfile :: K .admissibleRankQuotient :: K .curvatureTargetRank ::
            K .wedgeSupply :: K .stubSupply :: K .boundaryDemand :: K .remainderNormalized ::
            known)))
      (ExactLedger EGInput.{u} selected
        (K .entropyCapActive :: K .entropyPackageDemand :: K .remainderEntropyHigh ::
          K .forcedCurvatureCost :: K .curvatureFullRank :: K .targetRankCircuit ::
          K .exactResponseProfile :: K .admissibleRankQuotient :: K .curvatureTargetRank ::
          K .wedgeSupply :: K .stubSupply :: K .boundaryDemand :: K .remainderNormalized ::
          known)) := by
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        history (by simp [K_eq_iff, remainderFresh])
  let boundary :=
    (boundaryDemandRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        remainder (by simp [K_eq_iff, boundaryFresh])
  let stubSupply :=
    (stubSupplyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        boundary (by simp [K_eq_iff, stubFresh])
  let wedge :=
    (wedgeSupplyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        stubSupply (by simp [K_eq_iff, wedgeFresh])
  -- `[31]`: the curvature target-rank of the remainder and `lem:target-rank-circuit`.
  let rank :=
    (curvatureTargetRankRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        wedge (by simp [K_eq_iff, profileFresh, admissibleFresh, rankFresh])
  let circuit :=
    (targetRankCircuitRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        rank (by simp [K_eq_iff, circuitFresh])
  -- `[32]`: the exact finite rank split at the canonical maximal packing.
  match curvatureRankDichotomy (data := spineData) circuit
      (by simp [K_eq_iff, dropFresh]) (by simp [K_eq_iff, fullFresh]) with
  | .left dropHistory =>
      -- `[33]`--`[46]`: Branch D, closed.
      let dependence :=
        (branchDependenceRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) spineData).run
        dropHistory (by simp [K_eq_iff, dependenceFresh])
      exact (selectedRankDropCloses dependence
        (by simp [K_eq_iff, defectFresh]) (by simp [K_eq_iff, universalFresh])
        (by simp [K_eq_iff, compressionFresh]) (by simp [K_eq_iff, delocalizedFresh])
        (by simp [K_eq_iff, properFresh]) (by simp [K_eq_iff, globalFresh])
        (by simp [K_eq_iff, repairFresh]) (by simp [K_eq_iff, barrierFresh])
        (by simp [K_eq_iff, closureFresh])).elim
  | .right fullRankHistory =>
  -- `[34]`/`[47]`/`[48]`: full rank and `cor:forced-curvature-cost`.
  let cost :=
    (forcedCurvatureCostRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        fullRankHistory (by simp [K_eq_iff, costFresh])
  match remainderEntropyDichotomy (data := spineData) cost
      (by simp [K_eq_iff, highFresh]) (by simp [K_eq_iff, lowFresh]) with
  | .left highHistory =>
      -- `[51]`/`[52]`/`[53]`.
      let package :=
        (entropyPackageRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) spineData).run
        highHistory (by simp [K_eq_iff, packageFresh])
      match entropyCapDichotomy (data := spineData) package
          (by simp [K_eq_iff, activeFresh]) (by simp [K_eq_iff, largeFresh]) with
      | .left activeHistory =>
          -- `[54]`: closes when the `[22]` comparison retains the hot family's
          -- code (`lem:independent-target-entropy`); the all-cold comparison
          -- residual is returned to the caller.
          classical
          exact if retained : WindowFamilyRealized spineData.{u} selected.object
              (canonicalHotWindows spineData.{u} selected.object) then
            (entropyCap_closes activeHistory retained).elim
          else
            .inr activeHistory
      | .right largeHistory =>
          exact .inl (.inl largeHistory)
  | .right lowHistory =>
      let large :=
        (lowEntropyLargeBudgetRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        lowHistory (by simp [K_eq_iff, largeFresh])
      exact .inl (.inr large)

set_option maxHeartbeats 4000000 in
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
  match selectedWindowPackageRealizationDichotomy (selectedNearCubicNode21 history) with
  | .right unrealizedHistory =>
      -- The residual on which the manuscript's `[21]` realization sentence
      -- fails (dense packing: `2^{bits·p}` exceeds the skeleton states).  The
      -- manuscript's own nodes are run on it: `[22]`'s partition, then the
      -- `τ(θ) < 1/4` reading of `prop:negative-net-charge` as a decision.
      let partition :=
        (hotColdPartitionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unrealizedHistory (by simp [K_eq_iff])
      match Decision.run partition (K .denseDeficiencyBelow) (K .denseDeficiencyAtOrAbove)
          `HypostructureErdos64EG.selectedDenseDeficiencyDichotomy
          (by
            classical
            exact if below : DenseDeficiencyBelowStatement spineData.{u} selected.object then
              .inl ⟨below⟩
            else
              .inr ⟨below⟩)
          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
      | .left belowHistory =>
          -- `τ(θ) < 1/4`: the net-charge collision, `[25]`--`[62]` and the Type A/B
          -- branches, with `[56]` read from the decision.
          match selectedSpineToLargeBudget belowHistory with
          | .inl (.inl highHistory) =>
              let netCap :=
                (denseNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  highHistory (by simp [K_eq_iff])
              exact selectedNetChargeContinuation netCap
          | .inl (.inr lowHistory) =>
              let netCap :=
                (denseNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  lowHistory (by simp [K_eq_iff])
              exact selectedNetChargeContinuation netCap
          | .inr activeHistory =>
              rcases hotFamily_retained_or_cold activeHistory with retained | _cold
              · exact entropyCap_closes activeHistory retained
              · exact selectedDenseAllColdComparison activeHistory
      | .right denseHistory =>
          -- `τ(θ) ≥ 1/4`, the dense residual: `[22]`'s live-hot cap decision and the
          -- cold branch `[145]`--`[157]` on it.
          match Decision.run denseHistory (K .barrierCap) (K .barrierOverflow)
              `HypostructureErdos64EG.selectedDenseBarrierDichotomy
              (if overflow : Graph.skeletonBudget selected.object <
                  2 ^ (spineData.{u}.windowRate *
                    spineData.{u}.separatedScaleCount selected.object.vertexCount *
                    (canonicalHotWindows spineData.{u} selected.object).card) then
                .inr ⟨overflow⟩
              else
                .inl ⟨Nat.le_of_not_lt overflow,
                  fun _family member =>
                    Graph.skeletonBudget_le_variableEdgeBudget selected.object member⟩)
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .right overflowHistory =>
              exact selectedBarrierOverflowCloses overflowHistory
          | .left capHistory =>
          let split :=
            (coldWindowLedgerSplitRow (data := spineData)).run capHistory (by simp [K_eq_iff])
          match coldRoute8Dichotomy (data := spineData) split
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .left belowHistory =>
              -- `[147]`: `τ(θ) < 3/13`, the spine's route-8 closure with that
              -- inequality as `[56]`'s input.
              match selectedSpineToLargeBudget belowHistory with
              | .inl (.inl highHistory) =>
                  let netCap :=
                    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      highHistory (by simp [K_eq_iff])
                  exact selectedNetChargeContinuation netCap
              | .inl (.inr lowHistory) =>
                  let netCap :=
                    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      lowHistory (by simp [K_eq_iff])
                  exact selectedNetChargeContinuation netCap
              | .inr activeHistory =>
                  rcases hotFamily_retained_or_cold activeHistory with retained | _cold
                  · exact entropyCap_closes activeHistory retained
                  · exact selectedDenseAllColdComparison activeHistory
          | .right atOrAboveHistory =>
          match coldHotEntropyDichotomy (data := spineData) atOrAboveHistory
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .left overflowHistory =>
              exact selectedColdHotEntropyCloses overflowHistory
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
              -- `[153]`--`[157]` on the dense linear residual: `lem:bridgeless`,
              -- return corridors, first-failure routing, exchange bound and
              -- extraction, the (F5) candidate family, the germ trichotomy and
              -- the same-interface table.  (F1)/G1 close by `K .selection`,
              -- (F2)/G2 by `lem:context-universality`, (F3)/G3 by
              -- `K .replacementExclusion`; the residual after them is the
              -- neutral equal-length terminal germ, the next producer.
              let bridgeless :=
                (bridgelessRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  linearHistory (by simp [K_eq_iff])
              let corridors :=
                (coldReturnCorridorRow (data := spineData)).run bridgeless (by simp [K_eq_iff])
              let routed :=
                (coldFirstFailureRoutingRow (data := spineData)).run corridors
                  (by simp [K_eq_iff])
              let extracted :=
                (coldGermExtractionRow (data := spineData)).run routed (by simp [K_eq_iff])
              let candidates :=
                (coldGermCandidatesRow (data := spineData)).run extracted (by simp [K_eq_iff])
              let trichotomy :=
                (coldGermTrichotomyRow (data := spineData)).run candidates (by simp [K_eq_iff])
              let table :=
                (coldSameInterfaceTableRow (data := spineData)).run trichotomy
                  (by simp [K_eq_iff])
              let closed :=
                (coldBranchClosedRow (data := spineData)).run table (by simp [K_eq_iff])
              exact selectedDenseNeutralGerm closed
          | .right boundedHistory =>
              -- `[24]`: the density cap on the bounded arm, then the spine.
              let density :=
                (densityBudgetRow (data := spineData)).run boundedHistory (by simp [K_eq_iff])
              match selectedSpineToLargeBudget density with
              | .inl (.inl highHistory) =>
                  let netCap :=
                    (netDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      highHistory (by simp [K_eq_iff])
                  exact selectedNetChargeContinuation netCap
              | .inl (.inr lowHistory) =>
                  let netCap :=
                    (netDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      lowHistory (by simp [K_eq_iff])
                  exact selectedNetChargeContinuation netCap
              | .inr activeHistory =>
                  rcases hotFamily_retained_or_cold activeHistory with retained | _cold
                  · exact entropyCap_closes activeHistory retained
                  · exact selectedDenseAllColdComparison activeHistory
  | .left enumerated =>
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
                  -- independently target-testable coordinate family": node `[22]`'s
                  -- comparison retains the hot family's code, realized by the labelled
                  -- skeletons of the class (`K .hotColdPartition`), so the realized states
                  -- exceed the skeleton budget (`lem:independent-target-entropy`,
                  -- `lem:skeleton-dominates`).  If the comparison retains no code at all
                  -- (every window cold, not even the empty family's remainder-and-curvature
                  -- code realized), the residual is `def:curvature-target-rank`'s
                  -- complementary cold residual; its treatment is the next producer.
                  rcases hotFamily_retained_or_cold activeHistory with retained | cold
                  · exact entropyCap_closes activeHistory retained
                  · exact absurd (WindowFamilyRealized.mono (Finset.empty_subset _)
                      (activeHistory.get (K .windowPackageRealized)).down) cold.2
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
                  -- `thm:cold-branch-quantitative-closure`, closing step: by
                  -- `lem:p13-window-package` (`K .windowPackageRealized`) the
                  -- canonical comparison retains the whole packing's package, so
                  -- by `def:cold-window-ledger` every packed window is hot,
                  -- `𝒫_cold = ∅` and `C = 0`; the linear arm's positivity
                  -- (`K .coldMassLinear`) is impossible.  The `[153]`--`[157]`
                  -- rows above are the manuscript's nodes executed on this
                  -- residual; their outcomes are vacuous once `C = 0`.
                  exact selectedColdLinearCloses closed
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
                          -- independently target-testable coordinate family": node `[22]`'s
                          -- comparison retains the hot family's code, realized by the labelled
                          -- skeletons of the class (`K .hotColdPartition`), so the realized states
                          -- exceed the skeleton budget (`lem:independent-target-entropy`,
                          -- `lem:skeleton-dominates`).  If the comparison retains no code at all
                          -- (every window cold, not even the empty family's remainder-and-curvature
                          -- code realized), the residual is `def:curvature-target-rank`'s
                          -- complementary cold residual; its treatment is the next producer.
                          rcases hotFamily_retained_or_cold activeHistory with retained | cold
                          · exact entropyCap_closes activeHistory retained
                          · exact absurd (WindowFamilyRealized.mono (Finset.empty_subset _)
                              (activeHistory.get (K .windowPackageRealized)).down) cold.2
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
