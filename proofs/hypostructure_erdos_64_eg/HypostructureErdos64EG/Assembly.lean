import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun
import Hypostructure.Graph.Strategy.BranchDClosure
import Hypostructure.Graph.Strategy.EntropyClosure
import Hypostructure.Graph.Strategy.TypeBClosure
import Hypostructure.Graph.Strategy.TypeAExitRun
import Hypostructure.Graph.Strategy.BlockedCompressionRows

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

universe u w

-- EG-NODE none (establishes no manuscript DAG node)
noncomputable abbrev EGProblem :=
  Graph.Strategy.Spine.problem BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile spineData

-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def EGTarget : Core.Target EGProblem :=
  Graph.minimumDegreeCycleTarget erdosReceiverLoadProfile.baselineDegree
    BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    PowerOfTwoLength (fun exponent => exponent ≥ 2) (fun exponent => 2 ^ exponent)
    powerOfTwoLength_iff

-- EG-NODE none (establishes no manuscript DAG node)
noncomputable abbrev EGInput : Type (u + 1) :=
  Core.Strategy.ProblemInput EGProblem

-- EG-NODE none (establishes no manuscript DAG node)
noncomputable abbrev EGSelectionKey : FactKey EGInput :=
  K (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData) .selection

/-- The entry prefix `[5]`--`[18]`, run on the selected exact ledger. -/
-- EG-NODE [5] target algebra: R_e(G) cap Mers = empty for every oriented edge
-- EG-NODE [6] Mersenne return exists?
-- EG-NODE [8] no proper subgraph with minimum degree 3
-- EG-NODE [9] edge deletion critical; every edge touches a degree-3 vertex
-- EG-NODE [10] V_{>=4}(G) independent
-- EG-NODE [13] replacement lemma
-- EG-NODE [14] hereditary target-uncompressibility of proper supports
-- EG-NODE [15] G is P_13-free?
-- EG-NODE [17] maximal disjoint induced-P_13 packing P
-- EG-NODE [18] P_13 label algebra: 399 labels; relations C_s; curvature Omega_2
-- EG-NODE [7] power-of-two cycle (refuted arm of [6]: returnAvoidance iff, forward direction)
-- EG-NODE [11] boundaried atoms; boundary degree profile d_partial
-- EG-NODE [12] context-universality for target-complete identifications
-- EG-NODE [16] HSS theorem gives target cycle (refuted arm of [15], via freeForcesTarget)
noncomputable def selectedEntryPrefix
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    ExactLedger EGInput.{u} selected
      [K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres,
        K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure,
        K .relabelingDensityCap,
        K .cubicBaseline, K .selection] := by
  let hCubic :=
    (cubicBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [cubicBaselineRow, EGSelectionKey, K_eq_iff])
  let hDensity :=
    (relabelingDensityCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hCubic (by
        simp [relabelingDensityCapRow, cubicBaselineRow, EGSelectionKey, K_eq_iff])
  let hGadget :=
    (gadgetClosureRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hDensity (by
        simp [gadgetClosureRow, relabelingDensityCapRow, cubicBaselineRow,
          EGSelectionKey, K_eq_iff])
  let hCritical :=
    (contractionCriticalRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hGadget (by
        simp [contractionCriticalRow, gadgetClosureRow, cubicBaselineRow, EGSelectionKey,
          K_eq_iff])
  let h1 :=
    (returnAvoidanceRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hCritical (by
        simp [returnAvoidanceRow, contractionCriticalRow, cubicBaselineRow,
          EGSelectionKey, K_eq_iff])
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
  let hRank :=
    (cycleRankConstraintRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [cycleRankConstraintRow, deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h11 :=
    (degreeProfileFibresRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      hRank (by
        simp [degreeProfileFibresRow, cycleRankConstraintRow,
          deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h12 :=
    (targetCompleteContextUniversalityRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h11 (by
        simp [targetCompleteContextUniversalityRow, degreeProfileFibresRow,
          cycleRankConstraintRow,
          deletionCriticalityRow, noProperBaselineRow, returnAvoidanceRow,
          EGSelectionKey, K_eq_iff])
  let h13 :=
    (replacementExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h12 (by
        simp [replacementExclusionRow, targetCompleteContextUniversalityRow,
          degreeProfileFibresRow, cycleRankConstraintRow,
          deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h4 :=
    (interfaceReplacementRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h13 (by
        simp [interfaceReplacementRow, replacementExclusionRow,
          targetCompleteContextUniversalityRow, degreeProfileFibresRow,
          cycleRankConstraintRow,
          deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGSelectionKey, K_eq_iff])
  let h5 :=
    (obstructionPackingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h4 (by
        simp [obstructionPackingRow, interfaceReplacementRow,
          replacementExclusionRow, targetCompleteContextUniversalityRow,
          degreeProfileFibresRow, cycleRankConstraintRow,
          deletionCriticalityRow,
          noProperBaselineRow, returnAvoidanceRow, EGTarget, EGSelectionKey,
          K_eq_iff])
  exact
    (localAlgebraRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h5 (by
        simp [localAlgebraRow, obstructionPackingRow, interfaceReplacementRow,
          replacementExclusionRow, targetCompleteContextUniversalityRow,
          degreeProfileFibresRow, cycleRankConstraintRow,
          deletionCriticalityRow, noProperBaselineRow, returnAvoidanceRow, EGTarget,
          EGSelectionKey, K_eq_iff])

/-- Node `[19]`, run on the selected exact-ledger prefix. -/
-- EG-NODE [19] non-near-cubic surplus? sigma(G)>C_sp sqrt n
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

/-- The enclosing node-`[20]` routing performs `def:named-surplus-exits` before
node `[125]`.  Its left ledger carries a named sparse exit; its right ledger is
the paper's literal "after P13 label algebra and sparse exits" survivor
residual, which is the sole input accepted by `[125]`. -/
-- EG-NODE [20] named sparse-surplus exit classification before node [125]
noncomputable def selectedSparseSurplusDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    Decision (K .sparsePairExit) (K .sparseSurplusSurvivor) history :=
  sparseSurplusSurvivorDichotomy (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData) history
      (by simp [K_eq_iff])
      (by simp [K_eq_iff])

/-- The enclosing node-`[20]` exact named-exit continuation.  Direct target,
replacement, delocalization, and suppression-arithmetic exits terminate in the
sealed row.  Its only output is the concrete target-defect residual, retaining
the complete strict-surplus ancestry for the later peeling handoff.  This is
not an output of node `[125]`. -/
noncomputable def selectedSparseSurplusExitContinuation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePairExit, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseTargetDefectResidual, K .sparsePairExit, K .surplusAbove,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (sparseSurplusExitRoutingRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [sparseSurplusExitRoutingRow, K_eq_iff])

/-- Node `[125]` is the manuscript's routing-only survivor node.  It accepts
only an incoming ledger on which the enclosing sparse-exit classification has
already published `K .sparseSurplusSurvivor`, and passes that exact ledger on
without proving, reconstructing, dropping, or appending any fact. -/
-- EG-NODE [125] sparse-load survivor after P13 label algebra and sparse exits
@[reducible] def selectedSparseSurplusSurvivorNode125
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .sparseSurplusSurvivor) known] :
    ExactLedger EGInput.{u} selected known :=
  history

/-- Nodes `[126]`--`[128]`, sparse-surplus activation on node `[125]`'s
unchanged literal survivor residual. -/
-- EG-NODE [126] sparse envelope m<=2n-2, sigma=n-6-2 lambda
-- EG-NODE [127] excess-port extraction A=P_exc, |A|=sigma(G)
-- EG-NODE [128] canonical activation returns R_p; open Q_p; triangular response
noncomputable def selectedSparseSurplusActivation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection] := by
  let suppressionDefined :=
    (openPortSuppressionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [openPortSuppressionRow, K_eq_iff])
  let suppressionSafe :=
    (openPortSuppressionSafeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      suppressionDefined (by
        simp [openPortSuppressionSafeRow, openPortSuppressionRow, K_eq_iff])
  let singleSuppressionWitnessed :=
    (singleOpenPortSuppressionWitnessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      suppressionSafe (by
        simp [singleOpenPortSuppressionWitnessRow, openPortSuppressionSafeRow,
          openPortSuppressionRow, K_eq_iff])
  let familyCritical :=
    (suppressedFamilyCriticalCycleRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      singleSuppressionWitnessed (by
        simp [suppressedFamilyCriticalCycleRow,
          singleOpenPortSuppressionWitnessRow, openPortSuppressionSafeRow,
          openPortSuppressionRow, K_eq_iff])
  let h2 :=
    (sparseSlackSurplusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      familyCritical (by
        simp [sparseSlackSurplusRow, suppressedFamilyCriticalCycleRow,
          singleOpenPortSuppressionWitnessRow, openPortSuppressionSafeRow,
          openPortSuppressionRow, K_eq_iff])
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

/-- Node `[129]`, the paper's full active family and baseline spine demand.
The row reads the literal `[125]` survivor, the active surplus demands, and the
strict-surplus fact from this ledger; it writes only the resulting baseline
demand fact. -/
-- EG-NODE [129] full active family and baseline spine demand
noncomputable def selectedBaselineSpineDemand
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (baselineSpineDemandRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
      (by simp [baselineSpineDemandRow, K_eq_iff])

/-- Node `[130]`: the full pair-response family, split into the paper's
independent and dependent residuals on the literal `[129]` ledger. -/
-- EG-NODE [130] canonical pair split: blocker-free?
noncomputable def selectedPairResponseIndependenceDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands, K .sparsePortActivation,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    Decision (K .independentPairFamily) (K .dependentPairFamily) history :=
  pairResponseIndependenceDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[132]`, the sparse-pair routing split after baseline demand. -/
-- EG-NODE [132] blocked-pair routing: exit or canonical blocker?
noncomputable def selectedBlockedPairRoutingDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
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
-- EG-NODE [133] sparse surplus exit closes
noncomputable def selectedSparsePairExitCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePairExit, K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) : False := by
  exact (history.get (K .sparseSurplusSurvivor)).down
    (history.get (K .sparsePairExit)).down

/-- Node `[134]`: construct the full canonical blocker ledger on the literal
blocker arm.  The row reads the `[132]` certificate through `ExactLedger` and
writes only the canonical partition and no-overcount facts prescribed by the
paper. -/
-- EG-NODE [134] canonical blocker ledger: one B_pi and one capacity token per blocked pair
noncomputable def selectedCanonicalPairFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands,
        K .sparsePortActivation, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (canonicalPairLedgerRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [canonicalPairLedgerRow, K_eq_iff])

/-- Node `[135]`, exact window-join pressure on the literal `[134]` residual. -/
-- EG-NODE [135] exact window-join pressure e(R,W)+2e_x(W)=15p13+sigma_W
noncomputable def selectedExactWindowJoinPressure
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (exactWindowJoinPressureRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [exactWindowJoinPressureRow, K_eq_iff])

/-- Node `[136]`, capacity tokens on the literal `[135]` residual. -/
-- EG-NODE [136] tokenized blocked-pair ledger |Pi_blk|=sum ell(t,r)
noncomputable def selectedCapacityTokenFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .capacityTokenLedger, K .sparseUpperEnvelope,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection] :=
  (capacityTokenLedgerRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [capacityTokenLedgerRow, K_eq_iff])

/-- **Node `[138]`, the near-cubic outcome of the strict branch**, on the literal
residual of any of its routes (`[131]` at the free pair schedule, `[137]`'s capped
arm, `[144]`'s caps arm): the spine surplus estimate `σ(G) ≤ C_sp ⌈√n⌉` published
on this branch contradicts node `[19]`'s strict lower bound on the same object,
so the residual is exactly the near-cubic spine already handled by the other
arm of `[19]`. -/
-- EG-NODE [138] no coupled overload: quadratic bound on sigma; near-cubic spine
noncomputable def selectedSpineSurplusEstimateCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .spineSurplusEstimate) known]
    [FactKeys.Has (K .surplusAbove) known] : False := by
  have lower :
      spineData.surplusThreshold selected.object.vertexCount <
        selected.object.degreeSurplus spineData.threshold :=
    (history.get (K .surplusAbove)).down
  have upper :
      selected.object.degreeSurplus spineData.threshold ≤
        spineData.spineScale * Core.ceilSqrt selected.object.vertexCount :=
    (history.get (K .spineSurplusEstimate)).down
  exact Nat.not_lt_of_ge (by
    simpa [Graph.Strategy.Spine.Data.surplusThreshold] using upper) lower

/-- **Node `[144]`, same-token bottleneck discharge.**  Run the
paper's routing lemma on the literal overload ledger.  Sparse exits are
incompatible with the retained survivor fact, so the surviving output is the
decorated same-token Type B handoff.  Node `[65]` then appends the common
`typeBFanEntry` key for exactly that packing, core, envelope, and decoration
data.  This boundary returns the routed ledger; it does not assert closure or
import facts from the low-surplus Type B branch. -/
-- EG-NODE [144] bottleneck discharge: sparse exit, Type B, or near-cubic spine
noncomputable def selectedBottleneckDischarge
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .homogeneousBottleneckPattern) known]
    [FactKeys.Has (K .sparsePressureOverload) known]
    [FactKeys.Has (K .blockedPairEntropySandwich) known]
    [FactKeys.Has (K .roleFibrePartition) known]
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .baselineSpineDemand) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .sparsePortActivation) known]
    [FactKeys.Has (K .activeSurplusFamily) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .canonicalPairLedger) known]
    [FactKeys.Has (K .canonicalBlockerRoute) known]
    [FactKeys.Has (K .dependentPairFamily) known]
    [FactKeys.Has (K .sparseUpperEnvelope) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .admissibleRankQuotient) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (routingFresh : K .bottleneckRouting ∉ known)
    (handoffFresh : K .typeBHandoff ∉ known)
    (fanEntryFresh : K .typeBFanEntry ∉ known) :
    ExactLedger EGInput.{u} selected
      ([K .typeBFanEntry, K .bottleneckRouting, K .typeBHandoff] ++ known) := by
  let routed :=
    (sameTokenBottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [routingFresh, handoffFresh])
  exact
    (sameTokenTypeBFanEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      routed (by simp [K_eq_iff, fanEntryFresh])

/-- Node `[22]`: the canonical hot/cold partition (`def:cold-window-ledger`),
then the live-hot entropy cap decision on `𝒫_hot`.

The comparison is formed from the current object's own registered quantities:
`skeletonBudget` against `2 ^ (rate · scales · |𝒫_hot|)`.  The overflow cursor
is the live-hot terminal `[23]`; the cap cursor is the literal no-arm residual
forwarded toward `[24]` and the cold continuation. -/
-- EG-NODE [22] hot/cold split P = P_hot sqcup P_cold; live-hot entropy cap closes?
noncomputable def selectedBarrierDichotomy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .hotColdPartition) known]
    (capFresh : K .barrierCap ∉ known)
    (overflowFresh : K .barrierOverflow ∉ known) :
    Decision (K .barrierCap) (K .barrierOverflow) history := by
  classical
  let _split := (history.get (K .hotColdPartition)).down
  exact Decision.run history (K .barrierCap) (K .barrierOverflow)
    `HypostructureErdos64EG.selectedBarrierDichotomy
    (if overflow : Graph.skeletonBudget selected.object <
        2 ^ (spineData.{u}.windowRate *
          spineData.{u}.separatedScaleCount selected.object.vertexCount *
          (canonicalHotWindows spineData.{u} selected.object).card) then
      .inr ⟨overflow⟩
    else
      .inl ⟨Nat.le_of_not_lt overflow⟩)
    capFresh overflowFresh

/-- Node `[23]`: the live-hot `P₁₃` window entropy overflow closes on the
literal overflow residual.  `liveHotBarrierCapRow` reads the retained hot
package, the package-rate inequality, and the skeleton state-count bound from
that exact ledger and publishes the manuscript's opposite cap.  The framework
atomically runs that row and closes its cap against the visible overflow arm;
the application eliminates only the resulting distinguished closure fact. -/
-- EG-NODE [23] live-hot P13 window entropy overflow
noncomputable def selectedBarrierOverflowCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .barrierOverflow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    (capFresh : K .barrierCap ∉ known)
    (closureFresh : closed ∉ known) : False := by
  let closedHistory :=
    (liveHotBarrierCapRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).runAndCloseIncompatible
      history (K .barrierOverflow) (K .barrierCap)
      (by simpa using capFresh) (by simp [closureFresh])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[24]`: `prop:p13-density` "after closure" — on `[153]`'s bounded arm
(the cold branch forces no germ), the window-only density cap with its exact
`o(1)` is produced from `K .coldMass`, `K .coldMassBounded`,
`K .coldAmbientCubic`, and the split, on the literal residual. -/
-- EG-NODE [24] bounded cold-mass return from [153]: theta <= theta_win + o(1)
noncomputable def selectedDensityBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .densityCap, K .coldMassBounded, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (densityBudgetRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[145]` is a control-flow edge: node `[146]` reads node `[22]`'s
`K .hotColdPartition` directly from the same ExactLedger.  The two outputs of
`[146]` are sibling ledgers; neither output is appended to the other. -/
-- EG-NODE [145] direct cold-branch handoff from the no-edge of [22]
-- EG-NODE [146] theta < 1/78 ?
noncomputable def selectedColdRoute8Dichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  coldRoute8Dichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- Node `[148]`: only the no arm of `[146]` reaches the live-hot entropy
decision. -/
-- EG-NODE [148] live-hot entropy cap closes?
noncomputable def selectedColdHotEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
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
-- EG-NODE [149] P13 density cap
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
    cap spine spineData.{u}.three_le_threshold nearCubic
  change coldSkeletonAllowance spineData.{u} selected.object <
    coldWindowBitRate spineData.{u} selected.object *
      (canonicalHotWindows spineData.{u} selected.object).card at overflow
  simp only [coldSkeletonAllowance, coldWindowBitRate] at overflow
  rw [Nat.mul_assoc] at overflow
  exact absurd bound (Nat.not_le_of_lt overflow)

/-- Node `[150]`: append the cold-mass inequality to `[148]`'s literal
no-residual. -/
-- EG-NODE [150] hot failure forces cold mass C >= (theta-theta_win) n - o(n)
noncomputable def selectedColdMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldHotEntropyCap, K .coldRoute8AtOrAbove,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  (coldMassRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[151]`: append the ambient-cubic loss bound without rebuilding or
copying any predecessor fact. -/
-- EG-NODE [151] all but o(n) cold windows ambient-cubic
noncomputable def selectedColdAmbientCubic
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMass, K .coldHotEntropyCap, K .coldRoute8AtOrAbove,
        K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  (coldAmbientCubicRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[152]`, with node `[168]`'s endpoint repair: append the selected
interior branch-excess inequality to the same residual. -/
-- EG-NODE [152] selected interior stub excess b_int(S_cold) >= 9C - o(n)
noncomputable def selectedColdStubExcess
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldAmbientCubic, K .coldMass, K .coldHotEntropyCap,
        K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  (coldStubExcessRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`: the exact finite germ-positivity comparison on the literal
`[152]` residual
(`(perWindow + (threshold+1)·B_cold)·σ(G) < perWindow·C`); the linear arm forces a
positive germ family (`lem:cold-germ-extraction`), the bounded arm continues to
`[24]`. -/
-- EG-NODE [153] linear first-failure extraction? N_germ >= 9C/D_cold - o(n)
noncomputable def selectedColdMassDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass, K .coldHotEntropyCap,
        K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates, K .windowPackageSeparated,
        K .barrierEnumeration, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  coldMassDichotomy (data := spineData) history
    (by simp [K_eq_iff]) (by simp [K_eq_iff])

/-- `lem:bridgeless` on the literal `[153]` linear residual: the selected
object has no bridge; every oriented edge has a return. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedBridgeless
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (bridgelessRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history
    (by simp [K_eq_iff])

/-- Node `[153]`, `def:cold-corridor-first-failure`: every boundary stub of every
outside component of `X_cold` has its cold return corridor. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedColdReturnCorridors
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (coldReturnCorridorRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`, `lem:cold-corridor-first-failure`: cut-states and (F1)--(F5)
routing on the literal linear residual. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedColdFirstFailureRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .coldReturnCorridors, K .bridgeless,
        K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
        K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldFailureRouting, K .coldHandoffTransfer, K .coldFailureHandoff,
        K .coldFailureCompression, K .coldFailureDefect,
        K .coldFailureDefectRoute, K .coldFailureCycle,
        K .coldFirstFailureOccurrence, K .coldCorridorState,
        K .coldDeclaredHandoffLedger, K .sparseSurplusSurvivor,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear,
        K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] := by
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run history
      (by simp [K_eq_iff])
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by simp [K_eq_iff])
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run state
      (by simp [K_eq_iff])
  let cycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by simp [K_eq_iff])
  let defect :=
    (coldFailureDefectRow (data := spineData)).run cycle
      (by simp [K_eq_iff])
  let compression :=
    (coldFailureCompressionRow (data := spineData)).run defect
      (by simp [K_eq_iff])
  let handoff :=
    (coldFailureHandoffRow (data := spineData)).run compression
      (by simp [K_eq_iff])
  let transferred :=
    (coldHandoffTransferRow (data := spineData)).run handoff
      (by simp [K_eq_iff])
  exact
    (coldFirstFailureRoutingRow (data := spineData)).run transferred
      (by simp [K_eq_iff])

/-- Node `[153]`, `lem:cold-germ-extraction`: the exchange bound and the greedy
extraction, on the routed residual. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedColdGermExtraction
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (coldGermExtractionRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`, `lem:cold-germ-extraction`: the (F5) candidate germ family of
the selected branch-excess half-edges — its count, overlap bound, and extracted
disjoint subfamily — on the literal extraction residual.  Positivity is proved
by `selectedColdGermFamilyPositive` from this fact and the linear-arm facts. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedColdGermCandidates
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (coldGermCandidatesRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[153]`, terminal linear-arm obligation: pay the two registered
surplus losses and publish that node `[153]`'s literal extracted disjoint germ
family is nonempty. -/
noncomputable def selectedColdGermFamilyPositive
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    (fresh : K .coldGermFamilyPositive ∉ known := by simp [K_eq_iff]) :
    ExactLedger EGInput.{u} selected (K .coldGermFamilyPositive :: known) :=
  (coldGermFamilyPositiveRow (data := spineData)).run history
    (by simp [K_eq_iff, fresh])

/-- Nodes `[154]`--`[156]`, `lem:cold-bounded-germ-trichotomy` and
`lem:cold-increment-arithmetic` on the literal extracted residual. -/
-- EG-NODE [154] bounded germ case?
-- EG-NODE [155] G1: dyadic cycle
-- EG-NODE [156] G2: target defect, exit (4), or handoff
noncomputable def selectedColdGermTrichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [K .coldGermFamilyPositive, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected [K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermFamilyPositive, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (coldGermTrichotomyRow (data := spineData)).run history (by simp [K_eq_iff])

/-- Node `[157]`, `lem:cold-same-interface-table` with the short self-return
filter, on the literal trichotomy residual. -/
-- EG-NODE [157] G3 or same-interface table: compression
noncomputable def selectedColdSameInterfaceTable
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermFamilyPositive, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected [K .coldSameInterfaceTable, K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermFamilyPositive, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (coldSameInterfaceTableRow (data := spineData)).run history (by simp [K_eq_iff])

/-- `thm:cold-branch-quantitative-closure`: no terminal cold residual remains;
the branch is closed by routing to the target-defect and handoff ledgers. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedColdBranchClosed
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [K .coldSameInterfaceTable, K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermFamilyPositive, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected [K .coldBranchClosed, K .coldSameInterfaceTable, K .coldGermRealized, K .coldGermDistinguished, K .coldGermSilent,
        K .coldGermRouted, K .coldGermFamilyPositive, K .coldGermCandidates, K .coldExchangeBound, K .coldGermExtraction,
        K .coldCorridorState, K .coldFirstFailureOccurrence, K .coldFailureRouting, K .coldFailureCycle,
        K .coldFailureDefect, K .coldFailureCompression, K .coldFailureHandoff, K .coldHandoffTransfer,
        K .coldReturnCorridors, K .bridgeless, K .coldMassLinear, K .coldSelectedBranchExcess, K .coldAmbientCubicStubExcess,
          K .coldStubExcess, K .coldAmbientCubic, K .coldMass,
        K .coldHotEntropyCap, K .coldRoute8AtOrAbove, K .barrierCap, K .hotColdPartition, K .windowPackageRealized, K .skeletonDominates,
        K .windowPackageSeparated, K .barrierEnumeration, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (coldBranchClosedRow (data := spineData)).run history (by simp [K_eq_iff])

-- EG-NODE [4] choose lexicographically minimal counterexample
noncomputable def openSelectedCounterexample
    (input : EGInput) (avoids : ¬ Target input.object) :
    OpenedScope EGSelectionKey := by
  letI :
      FactSystem
        (Input BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData) :=
    instFactSystem
  exact openMinimalCounterexampleScope EGTarget
    (Graph.Strategy.Spine.refinedProgress BranchState
      Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile spineData)
    (fun _ => ())
    EGSelectionKey
    (fun context =>
      ⟨by
        simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData,
          Core.Strategy.selectedInput]
          using context.avoids,
      { sizeMinimal := by
          intro smaller smallerLt baseline
          have refinedLt :
              (Graph.Strategy.Spine.refinedProgress BranchState
                Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
                spineData).Smaller smaller context.G := by
            exact Graph.Strategy.Spine.refinedProgress_smaller_of_size_smaller
              BranchState Graph.ReceiverLoad.LoadCapacityProfile
              erdosReceiverLoadProfile spineData smallerLt
          simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
            using context.minimal smaller refinedLt baseline
        refinedMinimal := by
          intro smaller smallerLt baseline
          simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
            using context.minimal smaller smallerLt baseline }⟩)
    input (by
      simpa [EGTarget, Graph.minimumDegreeCycleTarget, Target, spineData]
        using avoids)

/-! The two node-[19] arms are separate exact-ledger cursors.  Node `[20]`
is the strict-surplus sibling; only the at-or-below sibling reaches node `[21]`.
Neither branch reads or publishes a fact owned by the other. -/

-- EG-NODE [21] finite enumeration: c_Omega, c_13
noncomputable def selectedNearCubicNode21
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection] :=
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
-- EG-NODE [158] joint window package realized in the labelled class?
noncomputable def selectedWindowPackageRealizationDichotomy
    {selected : EGInput.{u}}
    (dominated : ExactLedger EGInput.{u} selected
      [K .skeletonDominates, K .windowPackageSeparated, K .barrierEnumeration,
        K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .replacementExclusion, K .targetCompleteContextUniversality,
        K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :=
  Decision.run dominated (K .windowPackageRealized) (K .windowPackageUnrealized)
    `HypostructureErdos64EG.selectedWindowPackageRealizationDichotomy
    (by
      classical
      exact if realized : WindowPackageRealized spineData.{u} selected.object
          (canonicalWindowPacking spineData.{u} selected.object) then
        .inl ⟨realized⟩
      else
        .inr ⟨realized⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-! Node `[20]` and the post-`[21]` continuation are explicit branch
functions.  Their arguments and results are exact-ledger indices, so the
strict and near-cubic cursors cannot be accidentally exchanged. -/

/-- Node `[137]`, the manuscript's literal coupled-excess test on the
post-pressure residual.  The decision consumes every quantitative fact its two
arms use through `ExactLedger` and preserves the complete ancestry on either
result. -/
-- EG-NODE [137] coupled excess D_all > 0 ?
noncomputable def selectedCoupledExcessDichotomy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .surplusAbove) known]
    (nearCubicFresh : K .sparsePressureNearCubic ∉ known)
    (overloadFresh : K .sparsePressureOverload ∉ known) :
    Decision (K .sparsePressureNearCubic) (K .sparsePressureOverload) history :=
  coupledExcessDichotomy (data := spineData) history nearCubicFresh overloadFresh

/-! Node `[20]`, the strict (non-near-cubic) surplus branch, run node by node
along the Part X/XI diagram on the literal `K .surplusAbove` ledger:

* the enclosing `[20]` routing runs `sparseSurplusSurvivorDichotomy` for
  `def:named-surplus-exits`; the five named exits form the left arm, while
  their joint negation is exactly the incoming residual of routing-only
  `[125]`, "after P13 label algebra and sparse exits";
* `[126]`--`[128]` activation, `[129]` baseline spine demand, `[130]` canonical
  pair split;
* `[130]` yes: `[131]` decides the paper's full-pair code count on the exact
  `[129]` baseline witness and, on its realized arm, publishes both that count
  and the cleared free-pair entropy sandwich;
* `[130]` no: `[132]` blocked-pair routing — exit → `[133]` closes; blocker →
  `[134]` canonical pair ledger → `[135]` exact window-join pressure → `[136]`
  capacity-token ledger → `[137]` free-side count, exact role-fibre
  partition, and coupled-excess decision (`selectedCoupledExcessDichotomy`:
  no → `[138]`; yes → `[139]`/`[141]` class tests → `[140]`/`[142]`/`[143]`
  audits → `[144]`).

`selectedFreePairEntropySandwich` and `selectedCoupledExcessDichotomy` are the
next producers of this branch (see the audit rows `[131]`, `[137]`). -/
-- EG-NODE [20] surplus-pair accounting branch
-- EG-NODE [131] free-pair entropy sandwich
-- EG-NODE [137] coupled excess D_all > 0 ?
-- EG-NODE [138] no coupled overload: quadratic bound on sigma
-- EG-NODE [178] pair-code unrealized residual: entropy count of [131]/[137] fails

set_option maxHeartbeats 2000000 in
/-- **`lem:refined-minimality-swap`, node `[165]`, size-reducing case.**  A
neutral germ whose canonical representative `E` has strictly fewer internal
vertices than its corridor piece `Q`: exchanging `Q` for `E` inside the germ's
own completion yields a graph with fewer vertices, the same target status (the
germ is neutral, so `Q` and `E` are context-equivalent, and the completion is
`G` itself, which avoids the target), and the inherited baseline — a strictly
smaller counterexample, contradicting the selection's minimality. -/
-- EG-NODE [165] canonical replacement E != Q: swap Q->E gives a same-size counterexample
noncomputable def selectedCanonicalSwapCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldCanonicalSwapSmaller) known]
    [FactKeys.Has (K .selection) known] : False := by
  obtain ⟨germ, neutral, smaller⟩ := (history.get (K .coldCanonicalSwapSmaller)).down
  have selectedFacts := (history.get (K .selection)).down
  -- `G` is the germ's own completion, up to the decomposition's reconstruction.
  have reconstruction : (Graph.glue germ.piece germ.atom.outside).Isomorphic selected.object :=
    ⟨germ.atom.reconstructionIso⟩
  have baselineInvariant := Graph.minimumDegreeAtLeast_isomorphismInvariant spineData.{u}.threshold
  have targetInvariant := (Graph.cycleTargetInterface spineData.{u}.LengthOK).isomorphismInvariant
  have completionBaseline :
      Graph.MinimumDegreeAtLeast spineData.{u}.threshold (Graph.glue germ.piece germ.atom.outside) :=
    (baselineInvariant.iff_of_iso reconstruction).2 selected.baseline
  have completionAvoids :
      ¬ Graph.HasCycleWithLength spineData.{u}.LengthOK (Graph.glue germ.piece germ.atom.outside) :=
    fun hit => selectedFacts.1 ((targetInvariant.iff_of_iso reconstruction).1 hit)
  obtain ⟨vertexLt, swappedBaseline, swappedAvoids⟩ :=
    Graph.CanonicalPiece.swap_smaller_counterexample baselineInvariant targetInvariant
      germ.piece germ.atom.outside smaller completionBaseline completionAvoids
  have vertexEq : (Graph.glue germ.piece germ.atom.outside).vertexCount = selected.object.vertexCount :=
    Graph.FiniteObject.vertexCount_eq_of_isomorphic reconstruction
  exact swappedAvoids (selectedFacts.2 _
    (Graph.FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by rw [← vertexEq]; exact vertexLt))
    swappedBaseline)

/-- Branch D, nodes `[36]`--`[46]`, on the literal ledger returned by node
`[35]`.  The displayed state at `[35]` repeats `[33]` verbatim, while the
separate `separatedTestersRow` appends exactly `lem:separated-testers` without
altering that state.  This continuation begins with the context-validity
decision at `[36]`.  That test, with its target-defect terminal `[37]`,
the atom-compression test `[38]` with its terminal `[39]`, the delocalization
scope `[40]`/`[41]` with its proper-support terminal `[42]`, and the
whole-graph route `[43]`--`[45]` closed at `[46]`.  Every terminal is a
framework closure over the ledger of the arm against `K .selection`; the
freshness of the keys committed along the way is decided on the arm's exact
index at the call site. -/
-- EG-NODE [35] Branch D: rank-reducing obstruction dependence
-- EG-NODE [36] valid against every outside context?
-- EG-NODE [37] target-defective quotient
-- EG-NODE [38] target-complete with smaller proper representative?
-- EG-NODE [39] proper atom compression
-- EG-NODE [40] requires enlarged connected support Z supsetneq C
-- EG-NODE [41] Z subsetneq G ?
-- EG-NODE [42] proper-support smearing closure
-- EG-NODE [43] Z=G: whole-graph delocalization
-- EG-NODE [44] 1-3 repair identity s=p-2+2beta-sigma
-- EG-NODE [45] target / replacement / global profile barrier
-- EG-NODE [46] rank-drop branch closed
-- EG-NODE [12] context-universality for target-complete identifications
noncomputable def selectedRankDropCloses
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .branchDependence) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
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

/-- **Node `[123]`, the shared unified-demand continuation.**

This continuation reads the unified deficit (`K .route8UnifiedDeficit`), the
receiver-routing fact (`K .typeAReceiverRouting`), and the per-entry census
(`K .route8UnifiedEntryCensus`); it performs the recorded finite exit-`(4)`
descent and decides the terminal stage.  Every true two-support survivor is
closed through node `[124]`.  A failed-rate stage retains the exact peeled
accounting, runs the full demand/absorption/window-blocker ledger, and is
published as the explicit residual at node `[181]`. -/
noncomputable def selectedRouteEightCensus
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .selection) known]
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (terminalFresh : K .route8TerminalNoGo ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known) :
    ExactLedger EGInput.{u} selected
      ([K .route8PeeledDemandResidual, K .route8WindowBlockers,
        K .route8DemandAbsorption, K .route8DemandLedger,
        K .route8StageRateFailed, K .route8PeelingDescent] ++ known) := by
  let descended :=
    (route8PeelingDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [peelingFresh])
  match route8StageOutcomeDichotomy (data := spineData) descended
      (by simp [K_eq_iff, unifiedTrueFresh])
      (by simp [K_eq_iff, stageFailedFresh]) with
  | .left trueStage =>
      -- `[124]`: construct Q5 locally and contradict the same entry's committed
      -- no-exit-`(4)` fact.
      let closed :=
        (route8UnifiedTerminalNoGoRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          trueStage (by simp [K_eq_iff, terminalFresh])
      exact (closed.get (K .route8TerminalNoGo)).down.elim
  | .right failedStage =>
      match route8DemandLedgerDichotomy (data := spineData) failedStage
          (by simp [K_eq_iff, unifiedTrueFresh])
          (by simp [K_eq_iff, demandLedgerFresh]) with
      | .left trueEntry =>
          -- The demand-ledger L1 terminal is the same `[124]` obstruction;
          -- reuse its sole producer instead of duplicating the deletion proof.
          let closed :=
            (route8UnifiedTerminalNoGoRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              trueEntry (by simp [K_eq_iff, terminalFresh])
          exact (closed.get (K .route8TerminalNoGo)).down.elim
      | .right demandHistory =>
          let absorbed :=
            (route8DemandAbsorptionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              demandHistory (by simp [K_eq_iff, demandAbsorptionFresh])
          let blocked :=
            (route8WindowBlockersRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              absorbed (by simp [K_eq_iff, windowBlockersFresh])
          exact
            (route8PeeledDemandResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              blocked (by simp [K_eq_iff, demandResidualFresh])

/-- **Node `[123]`: exact large-budget descent.**

The unified deficit and entry census are literal prerequisites of this node.
The node performs only the finite exit-`(4)` descent prescribed by
`thm:large-budget-route8-only`: true route-8 entries close at `[124]`, while a
failed reduced-rate stage is returned as the exact peeled-demand ledger at
`[181]`.  In particular this wrapper does not claim `False` from `[181]` and
does not absorb the earlier quotient or Type B residual decisions into node
`[123]`. -/
-- EG-NODE [123] exact descent to [124] or [181]
noncomputable def selectedLargeBudgetPressureCensus
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (terminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by
      simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      simp [K_eq_iff]) :
    ExactLedger EGInput.{u} selected
      ([K .route8PeeledDemandResidual, K .route8WindowBlockers,
        K .route8DemandAbsorption, K .route8DemandLedger,
        K .route8StageRateFailed, K .route8PeelingDescent] ++ known) :=
  selectedRouteEightCensus history
    (by simp [K_eq_iff, peelingFresh])
    (by simp [K_eq_iff, unifiedTrueFresh])
    (by simp [K_eq_iff, stageFailedFresh])
    (by simp [K_eq_iff, terminalFresh])
    (by simp [K_eq_iff, demandLedgerFresh])
    (by simp [K_eq_iff, demandAbsorptionFresh])
    (by simp [K_eq_iff, windowBlockersFresh])
    (by simp [K_eq_iff, demandResidualFresh])

/-- **Nodes `[110]`--`[116]`: the route-8 residual of Part IX**, on the shared
  `[109]` residual reached by the no-edge of exit `(7)` (index-polymorphic).
  This is exactly the edge drawn in Part VIII after the visible/silent
  residual routing and any finite exit-`(4)` peeling.  `[110]`
  `route8ResidualProfileRow`
(`def:typeA-silent-core-residual`: the saturated receiver survives only through
exit `(8)`, no decorated handoff fan); `[111]` `route8GlobalSqueezeRow` (the
  canonical route-8 Type A subcollection and its cleared `D_A` sum); `[112]`
  `route8BasinBurdenRow` (`lem:typeA-route8-burden`: for every member of that
  exact collection, `[111]` supplies the silent-first route-8 entry family and
  `[88]`, `K .typeAReceiverRouting`, supplies total routing; the row sums
  `S_sil^exc(X) ≥ s·D_A(X)` over the collection); `[113]`
`route8LargeBudgetDeficitRow` (`def:typeA-large-budget-deficit`), whose positive
arm is exactly the displayed route-8-only bound and whose negative arm enters
the unified target-defect/route-8 ledger required by `rem:why-unified`; `[114]`
`route8CarrierCoreRow` (canonical minimal target-complete carrier cores in the
declared `u`-supported response algebra), `route8TrueResidualRow` (the exact
true route-8 residual conditions `(R1)`--`(R4)` for every actual indexed entry),
and `route8CarrierCutParityRow` (`lem:typeA-carrier-cut-parity` for precisely
the surviving mixed events of those entries);
`[115]`--`[116]`
`route8SmallCoreCollapseRow` (`lem:typeA-one-terminal-collapse`: a zero/one
essential-core entry triggers exits `(4)`--`(7)`, absent here); then the
object-level census `K .route8Census` (`Graph.Route8Census`: the indexed entries
`(piece, receiver, silent-excess load)` of the Type A pieces `𝒳_A`, their selected
trace basins and canonical essential cores, the supply `∂R`; the deficit
`|R| ≤ N_basin + s·|∂R|` and the private-carrier rate — its row is the next
producer `route8CensusRow`), `[117]` `route8CarrierDichotomy` on it,
`[119]`--`[122]` closed inline by `Graph.Route8Census.false_of_noTwoCarrier`
(`rem:route8-carrier-margin`), and the two-carrier arm `[118]`--`[124]` handed to
the next producer `selectedRouteEightTwoCarrierEntry`. -/
-- EG-NODE [110] exit (8): route-8 residual profile
-- EG-NODE [111] global squeeze extracts route-8 Type A collection X_A
-- EG-NODE [112] route-8 burden N_basin >= 4 D_A
-- EG-NODE [113] large-budget deficit D_A >= (1/4-tau_win)|R|-o(|R|)
-- EG-NODE [114] canonical carrier core and two essential incidences for every surviving mixed event
-- EG-NODE [115] some entry has alpha(xi) <= 1 ?
-- EG-NODE [116] exits (4)-(7) occur
-- EG-NODE [117] some entry has pi(xi) <= 2 ?
-- EG-NODE [118] two-carrier route-8 entry
-- EG-NODE [119] no two-carrier entry: at least three private essential carriers
-- EG-NODE [120] private-carrier budget 3N_basin <= defp(R)+o(|R|)
-- EG-NODE [121] burden plus deficit N_basin >= 4(1/4-tau)|R|
-- EG-NODE [122] contradiction tau_win >= 12(1/4-tau_win)
-- EG-NODE [123] large-budget pressure descent: target-defect entries peel by exit (4)
abbrev SelectedRouteEightBoundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearResidual
      selected.object ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8QuotientResidual
        selected.object ∨
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8PeeledDemandResidual
        selected.object

noncomputable def selectedRouteEightResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known] :
    SelectedRouteEightBoundary selected := by
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
  -- `[113]`: the route-8-only lower bound is tested, because the manuscript's
  -- unified-demand correction explicitly forbids deriving it from the residual-C
  -- marker while target-defect supports may still carry negative mass.
  match route8LargeBudgetDeficitRow (data := spineData) burdened
      (by simp [K_eq_iff, deficitFresh])
      (by simp [K_eq_iff, deficitFailsFresh]) with
  | .left deficit =>
      -- `[114]`--`[116]` are the conditional route-8 reduction on the exact
      -- positive `[113]` ledger.
      let cored :=
        (route8CarrierCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          deficit (by simp [K_eq_iff, coreFresh])
      let trueResidual :=
        (route8TrueResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          cored (by simp [K_eq_iff, trueResidualFresh])
      let cutParity :=
        (route8CarrierCutParityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          trueResidual (by simp [K_eq_iff, cutParityFresh])
      match route8SmallCoreCollapseRow (data := spineData) cutParity
          (by simp [K_eq_iff, smallFresh])
          (by simp [K_eq_iff, noSmallFresh]) with
      | .left small =>
          let collapsed :=
            (route8SmallCoreExitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              small (by simp [K_eq_iff, collapseFresh])
          have trueFacts := (collapsed.get (K .route8TrueResidual)).down
          have collapseFacts := (collapsed.get (K .route8SmallCoreCollapse)).down
          obtain ⟨_componentCore, component, componentMem, receiver, receiverMem,
            load, loadMem, _alphaSmall, alternatives⟩ := collapseFacts
          have minimal :=
            (trueFacts.2 component componentMem).2 receiver receiverMem |>.2.2
              load loadMem |>.2.1
          rcases alternatives with localDefect | compression | delocalization | separator
          · exact (minimal.2.1 localDefect).elim
          · -- `[116]`: the nontrivial target-complete quotient `ρ°_𝒞` is
            -- alternative (b) of `def:typeA-trace-basin` itself.
            exact (minimal.2.2.1 compression).elim
          · exact (minimal.2.2.2.1 delocalization).elim
          · exact (minimal.2.2.2.2 separator).elim
      | .right noSmall =>
          -- `[117]`: run the carrier decision on the exact `Ξ(𝒳_A)` census.
          let census :=
            (route8CensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              noSmall (by simp [K_eq_iff, censusFresh])
          match route8CarrierDichotomy (data := spineData) census
              (by simp [K_eq_iff, twoFresh])
              (by simp [K_eq_iff, noTwoFresh]) with
          | .right noTwo =>
              -- `[119]`--`[122]`: publish the exact private-incidence budget,
              -- then publish its contradiction with the census readings.
              let budgeted :=
                (route8PrivateCarrierBudgetRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run noTwo
                  (by simp [K_eq_iff, privateBudgetFresh])
              let contradicted :=
                (route8NoTwoCarrierContradictionRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run budgeted
                  (by simp [K_eq_iff, noTwoContradictionFresh])
              exact (contradicted.get
                (K .route8NoTwoCarrierContradiction)).down.elim
          | .left twoCarrier =>
              -- `[118]`: attach the true-residual no-exit fact and every
              -- essential-carrier deletion witness to the selected entry.
              let trueEntry :=
                (route8TrueTwoCarrierEntryRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run twoCarrier
                  (by simp [K_eq_iff, trueEntryFresh])
              let witnessed :=
                (route8CarrierDeletionWitnessesRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run trueEntry
                  (by simp [K_eq_iff, deletionWitnessesFresh])
              -- `[124]`: canonical Q5 contradicts the no-exit-(4) fact on
              -- this same monotone ledger.
              let closed :=
                (route8TerminalNoGoRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run witnessed
                  (by simp [K_eq_iff, terminalNoGoFresh])
              exact (closed.get (K .route8TerminalNoGo)).down.elim
  | .right deficitFails =>
      -- The negative `[113]` fact remains in the ledger while the Type B
      -- allowance and unified target-defect/route-8 collection are recorded.
      let bridgeMass :=
        (bridgeFanMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          deficitFails (by simp [K_eq_iff, bridgeMassFresh])
      let bridgeSublinear :=
        (typeBBridgeSublinearRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          bridgeMass (by simp [K_eq_iff, bridgeSublinearFresh])
      -- `[123]`: publish the unified negative collection on this residual.
      let unifiedNegative :=
        (route8UnifiedNegativeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          bridgeSublinear (by simp [K_eq_iff, unifiedNegativeFresh])
      let typeAExcluded :=
        (typeAExclusionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unifiedNegative (by simp [K_eq_iff, typeAExclusionFresh])
      let typeBReduced :=
        (typeBBridgeReductionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          typeAExcluded (by simp [K_eq_iff, typeBBridgeReductionFresh])
      let classified :=
        (route8PiecesClassifiedRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          typeBReduced (by simp [K_eq_iff, piecesClassifiedFresh])
      match typeBSublinearDichotomy (data := spineData) classified
          (by simp [K_eq_iff, sublinearLedgerFresh])
          (by simp [K_eq_iff, sublinearResidualFresh]) with
      | .right residualHistory =>
          exact Or.inl
            (residualHistory.get (K .typeBSublinearResidual)).down
      | .left sublinearHistory =>
          let unifiedDeficit :=
            (route8UnifiedDeficitRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              sublinearHistory (by simp [K_eq_iff, unifiedDeficitFresh])
          match route8QuotientDichotomy (data := spineData) unifiedDeficit
              (by simp [K_eq_iff, quotientFreeFresh])
              (by simp [K_eq_iff, quotientResidualFresh]) with
          | .right residualHistory =>
              exact Or.inr (Or.inl
                (residualHistory.get (K .route8QuotientResidual)).down)
          | .left quotientFreeHistory =>
              let census :=
                (route8UnifiedEntryCensusRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run quotientFreeHistory
                    (by simp [K_eq_iff, unifiedCensusFresh])
              let peeled := selectedLargeBudgetPressureCensus census
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (unifiedTrueFresh := by
                  simp [K_eq_iff, unifiedTrueFresh])
                (stageFailedFresh := by
                  simp [K_eq_iff, stageFailedFresh])
                (terminalFresh := by
                  simp [K_eq_iff, unifiedTerminalFresh])
                (demandLedgerFresh := by
                  simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by
                  simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by
                  simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by
                  simp [K_eq_iff, demandResidualFresh])
              exact Or.inr (Or.inr
                (peeled.get (K .route8PeeledDemandResidual)).down)

/- The ordinary negative-support wrapper is retained separately from the
absorbed `[177]` carrier.  Its existing enclosing branches already provide the
selected Type A routing fact and use their own Part IX continuation. -/
noncomputable def selectedTypeBRoute8Continuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by
      simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by
      simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff]) :
    SelectedRouteEightBoundary selected := by
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, bridgeMassFresh])
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by simp [K_eq_iff, bridgeSublinearFresh])
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeSublinear (by simp [K_eq_iff, unifiedNegativeFresh])
  let typeAExcluded :=
    (typeAExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unifiedNegative (by simp [K_eq_iff, typeAExclusionFresh])
  let typeBReduced :=
    (typeBBridgeReductionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeAExcluded (by simp [K_eq_iff, typeBBridgeReductionFresh])
  let classified :=
    (route8PiecesClassifiedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeBReduced (by simp [K_eq_iff, piecesClassifiedFresh])
  match typeBSublinearDichotomy (data := spineData) classified
      (by simp [K_eq_iff, sublinearLedgerFresh])
      (by simp [K_eq_iff, sublinearResidualFresh]) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let deficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by simp [K_eq_iff, unifiedDeficitFresh])
      match route8QuotientDichotomy (data := spineData) deficit
          (by simp [K_eq_iff, quotientFreeFresh])
          (by simp [K_eq_iff, quotientResidualFresh]) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory
                (by simp [K_eq_iff, unifiedCensusFresh])
          let peeled := selectedLargeBudgetPressureCensus census
            (peelingFresh := by simp [K_eq_iff, peelingFresh])
            (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
            (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
            (terminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
            (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
            (demandAbsorptionFresh := by
              simp [K_eq_iff, demandAbsorptionFresh])
            (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
            (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
          exact Or.inr (Or.inr
            (peeled.get (K .route8PeeledDemandResidual)).down)

/- The four non-closing outputs of the common Type B certificate calculation.
They are exactly the paper's two local-payment and two fan-mass boundaries:
certificate failure `[75]/[84]`, successful B2 `[74]/[82]`, the surviving
canonical post-ledger core, and B2 overlap `[73]/[83]`.  No quantitative fact
from the incoming branch is included in this type. -/
private abbrev TypeBCertificateBoundary
    (selected : EGInput.{u}) (known : FactKeys EGInput.{u}) :=
  Sum
    (ExactLedger EGInput.{u} selected
      ([K .fanCertificateResidualMass, K .fanCertificateResidual] ++ known))
    (Sum
      (ExactLedger EGInput.{u} selected
        ([K .typeBExcluded, K .typeBDisjointLedger, K .typeBB2Choice,
          K .typeBHybridEntry, K .typeBDirectCycleFree,
          K .fanCertificateMarked] ++ known))
      (Sum
        (ExactLedger EGInput.{u} selected
          ([K .typeBExclusionResidualMass, K .typeBExclusionResidual,
            K .typeBDisjointLedger, K .typeBB2Choice,
            K .typeBHybridEntry, K .typeBDirectCycleFree,
            K .fanCertificateMarked] ++ known))
        (ExactLedger EGInput.{u} selected
          ([K .typeBOverlapObstructionMass, K .typeBOverlapObstruction,
            K .typeBHybridEntry, K .typeBDirectCycleFree,
            K .fanCertificateMarked] ++ known))))

/-- The paper's common `[72]` port-routing prefix.  Each fact is published by
its registered producer exactly once; later local alternatives retrieve these
facts from the resulting ExactLedger. -/
private noncomputable def selectedTypeBPortRoutingPrefix
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    (fanClosedFresh : K .fanClosedPort ∉ known)
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known)
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known)
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known) :
    ExactLedger EGInput selected
      ([K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort] ++ known) := by
  let fanClosed :=
    (fanClosedPortRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, fanClosedFresh])
  let compatibleClosure :=
    (compatiblePairFanClosureRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      fanClosed (by simp [K_eq_iff, compatibleClosureFresh])
  let fanClosedRouting :=
    (fanClosedPortTypeBRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      compatibleClosure (by simp [K_eq_iff, fanClosedRoutingFresh])
  exact
    (compatiblePairTypeBRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      fanClosedRouting (by simp [K_eq_iff, compatibleRoutingFresh])

/-- **The common Type B core `[71]`--`[75]` / `[80]`--`[84]`.**

This function consumes only the facts named by those nodes.  Direct cycles and
the canonical B2-paid negative support close locally.  Every other arm returns
its literal paper residual.  In particular it does not assume the ordinary
`[64]` negative support, a route-8 rate, or a near-cubic surplus estimate; the
enclosing branch decides how `[76]`/`[85]` spends the returned mass. -/
-- EG-NODE [71] certificate labelling present?
-- EG-NODE [75] bridge fan-mass: fan-certificate centers and B2 failures charged
-- EG-NODE [80] certificate labelling present?
-- EG-NODE [84] fan-mass route: certificate failures and B2 failures charged
private noncomputable def selectedTypeBCertificateBoundaryAfterPortRouting
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .fanClosedPort) known]
    [FactKeys.Has (K .compatiblePairFanClosure) known]
    [FactKeys.Has (K .fanClosedPortTypeBRouting) known]
    [FactKeys.Has (K .compatiblePairTypeBRouting) known]
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
    :
    TypeBCertificateBoundary selected known := by
  -- `[71]`/`[80]`: certificate labelling present at every assigned centre?
  match fanCertificateDichotomy (data := spineData) history
      (by simp [K_eq_iff, markedFresh]) (by simp [K_eq_iff, residualFresh]) with
  | .right residualHistory =>
      -- `[75]`/`[84]`: the residual centre is charged to the bridge fan mass.
      let mass :=
        (fanCertificateResidualMassRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          residualHistory (by simp [K_eq_iff, certificateMassFresh])
      exact Sum.inl mass
  | .left markedHistory =>
      -- `[72]`--`[85]` on the common Type B carrier: the direct fan-window
      -- cycle test and the hybrid B1 reading preserve either the canonical
      -- assigned support or the indexed absorbed witness.  B2 is the next
      -- boundary: it may proceed only once its own literal carrier is present.
      match directCycleDichotomy (data := spineData) markedHistory
          (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh]) with
      | .left cycleHistory =>
          have impossible : False := by
            rcases (cycleHistory.get (K .typeBDirectCycle)).down with
              canonical | absorbed | sameToken
            · obtain ⟨packing, valid, _maximal, _component, _present, _centres,
                _assigned, _centre, _member, _high, directCycle⟩ := canonical
              exact (cycleHistory.get (K .selection)).down.1
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid directCycle)
            · obtain ⟨_marked, _germ, _centre, _witness, directCycle⟩ :=
                absorbed
              have valid : selected.object.IsWindowPacking spineData.windowOrder
                  (canonicalWindowPacking spineData selected.object) :=
                (Classical.choose_spec
                  (selected.object.exists_windowPacking_card_eq
                    spineData.windowOrder)).1
              exact (cycleHistory.get (K .selection)).down.1
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid directCycle)
            · obtain ⟨packing, valid, _maximal, _core, _envelope, _coreEq,
                  _nonempty, _marked, _centre, _member, _high, directCycle⟩ :=
                sameToken
              exact (cycleHistory.get (K .selection)).down.1
                (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
                  valid directCycle)
          exact impossible.elim
      | .right freeHistory =>
          -- B1 is a fact of every direct-cycle-free marked fan, independently
          -- of whether B2 succeeds.  Publish it before the B2 split so both
          -- resulting exact ledgers retain the same local incidence proof.
          let hybrid :=
            (hybridEntryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              freeHistory (by simp [K_eq_iff, hybridFresh])
          match b2AssignmentDichotomy (data := spineData) hybrid
              (by simp [K_eq_iff, choiceFresh])
              (by simp [K_eq_iff, obstructionFresh]) with
          | .left choiceHistory =>
              let ledger :=
                (disjointPostLedgerComponentsRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  choiceHistory (by simp [K_eq_iff, ledgerFresh])
              match typeBExclusionDichotomy (data := spineData) ledger
                  (by simp [K_eq_iff, excludedFresh])
                  (by simp [K_eq_iff, exclusionResidualFresh]) with
              | .left excludedHistory =>
                  -- The exact paid ledger is returned without inspecting its
                  -- carrier.  Ordinary `[64]` closes its canonical alternative;
                  -- `[144]` and `[177]` retain their own handoff alternative.
                  exact Sum.inr (Sum.inl excludedHistory)
              | .right residualHistory =>
                  let mass :=
                    (typeBExclusionResidualMassRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      residualHistory (by simp [K_eq_iff, exclusionMassFresh])
                  exact Sum.inr (Sum.inr (Sum.inl mass))
          | .right obstructionHistory =>
              let mass :=
                (typeBOverlapObstructionMassRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  obstructionHistory (by simp [K_eq_iff, obstructionMassFresh])
              exact Sum.inr (Sum.inr (Sum.inr mass))

/-- Compatibility wrapper for callers entering the common Type-B certificate
walk before node `[72]`.  It runs the four registered port producers and then
hands their literal output ledger to the certificate core. -/
noncomputable def selectedTypeBCertificateBoundary
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff]) :
    TypeBCertificateBoundary selected
      ([K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort] ++ known) := by
  let routed := selectedTypeBPortRoutingPrefix history fanClosedFresh
    compatibleClosureFresh fanClosedRoutingFresh compatibleRoutingFresh
  exact selectedTypeBCertificateBoundaryAfterPortRouting routed
    (by simp [K_eq_iff, markedFresh])
    (by simp [K_eq_iff, residualFresh])
    (by simp [K_eq_iff, certificateMassFresh])
    (by simp [K_eq_iff, cycleFresh])
    (by simp [K_eq_iff, freeFresh])
    (by simp [K_eq_iff, choiceFresh])
    (by simp [K_eq_iff, obstructionFresh])
    (by simp [K_eq_iff, hybridFresh])
    (by simp [K_eq_iff, ledgerFresh])
    (by simp [K_eq_iff, excludedFresh])
    (by simp [K_eq_iff, exclusionResidualFresh])
    (by simp [K_eq_iff, exclusionMassFresh])
    (by simp [K_eq_iff, obstructionMassFresh])

/- The complete carrier-neutral output of nodes `[67]`--`[85]`.  The outer
sum remembers the literal degree arm of `[68]`; the inner boundary remembers
the first Type B ledger edge that still needs the enclosing branch's global
accounting.  Both indices contain every fact actually proved on that arm. -/
private abbrev TypeBContinuationBoundary
    (selected : EGInput.{u}) (known : FactKeys EGInput.{u}) :=
  Sum
    (TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .compatiblePairTypeBRouting,
        K .fanClosedPortTypeBRouting, K .compatiblePairFanClosure,
        K .fanClosedPort, K .typeBFanLocalDichotomy,
        K .sameCenterOpenPortCompatibility, K .typeBFanHeavyCentre,
        K .typeBFanSafe, K .highCentreNormalForm] ++ known))
    (TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .triangularPortTypeBRouting,
        K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort,
        K .triangularCrossShoulder,
        K .triangularFirstLanding,
        K .triangularPortReturn,
        K .triangularShoulderCompletion,
        K .triangularFanCore,
        K .typeBFanDegreeFourProfile, K .typeBFanDegreeFourCentres,
        K .typeBFanSafe, K .highCentreNormalForm] ++ known))

/- The same boundary when node `[67]` is already present on the incoming
ledger.  This is the literal situation at `[144]`: the bottleneck audit needs
the object-wide normal form before it constructs the same-token handoff, so
the common Type B continuation must resume at `[68]` without appending a
duplicate key. -/
private abbrev TypeBAfterNormalFormBoundary
    (selected : EGInput.{u}) (known : FactKeys EGInput.{u}) :=
  Sum
    (TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .compatiblePairTypeBRouting,
        K .fanClosedPortTypeBRouting, K .compatiblePairFanClosure,
        K .fanClosedPort, K .typeBFanLocalDichotomy,
        K .sameCenterOpenPortCompatibility, K .typeBFanHeavyCentre,
        K .typeBFanSafe] ++ known))
    (TypeBCertificateBoundary selected
      ([K .fanCertificateCap, K .triangularPortTypeBRouting,
        K .compatiblePairTypeBRouting, K .fanClosedPortTypeBRouting,
        K .compatiblePairFanClosure, K .fanClosedPort,
        K .triangularCrossShoulder,
        K .triangularFirstLanding,
        K .triangularPortReturn,
        K .triangularShoulderCompletion,
        K .triangularFanCore,
        K .typeBFanDegreeFourProfile, K .typeBFanDegreeFourCentres,
        K .typeBFanSafe] ++ known))

/-- The common Type B continuation after `[67]` has already been published on
the same exact ledger.  No fact is reconstructed: `[68]` and every subsequent
owner read their inputs from `history`. -/
private noncomputable def selectedTypeBAfterNormalFormContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known)
    (localFresh : K .typeBFanLocalDichotomy ∉ known)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (triangularCoreFresh : K .triangularFanCore ∉ known)
    (capFresh : K .fanCertificateCap ∉ known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by
      simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by
      simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      simp [K_eq_iff])
    (fanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff]) :
    TypeBAfterNormalFormBoundary selected known := by
  let fanSafe :=
    (typeBFanSafeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, fanSafeFresh])
  match typeBFanDegreeDichotomy (data := spineData) fanSafe
      (by simp [K_eq_iff, heavyFresh])
      (by simp [K_eq_iff, degreeFourFresh]) with
  | .left heavyHistory =>
      let compatible :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by simp [K_eq_iff, compatibilityFresh])
      let localHistory :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatible (by simp [K_eq_iff, localFresh])
      let portRouted := selectedTypeBPortRoutingPrefix localHistory
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, capFresh])
      exact Sum.inl (selectedTypeBCertificateBoundaryAfterPortRouting capped
        (by simp [K_eq_iff, markedFresh])
        (by simp [K_eq_iff, residualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh]))
  | .right degreeFourHistory =>
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, profileFresh])
      let triangular :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, triangularCoreFresh])
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangular (by simp [K_eq_iff, shoulderCompletionFresh])
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by simp [K_eq_iff, portReturnFresh])
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by simp [K_eq_iff, firstLandingFresh])
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by simp [K_eq_iff, crossShoulderFresh])
      let portRouted := selectedTypeBPortRoutingPrefix crossShouldered
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, triangularRoutingFresh])
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by simp [K_eq_iff, capFresh])
      exact Sum.inr (selectedTypeBCertificateBoundaryAfterPortRouting capped
        (by simp [K_eq_iff, markedFresh])
        (by simp [K_eq_iff, residualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh]))

/-- **The common Type B continuation `[67]`--`[85]`.**

This is the literal continuation shared by the ordinary `[64]`, same-token
`[144]`, and absorbed-germ `[177]` entries at node `[65]`.  It reads only the
paper facts used by these nodes.  In particular it does not manufacture a
`cubicBaseline`, canonical negative support, route-8 rate, or near-cubic bridge
estimate for carriers that do not have those facts. -/
noncomputable def selectedTypeBContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [fanEntryHas : FactKeys.Has (K .typeBFanEntry) known]
    [selectionHas : FactKeys.Has (K .selection) known]
    [bridgelessHas : FactKeys.Has (K .bridgeless) known]
    [replacementHas : FactKeys.Has (K .replacementExclusion) known]
    [tightHas : FactKeys.Has (K .tightEndpoint) known]
    [uncompressibleHas : FactKeys.Has (K .uncompressible) known]
    [remainderHas : FactKeys.Has (K .remainderNormalized) known]
    [relabelingEntropyHas : FactKeys.Has (K .remainderRelabelingEntropy) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known)
    (localFresh : K .typeBFanLocalDichotomy ∉ known)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (triangularCoreFresh : K .triangularFanCore ∉ known)
    (capFresh : K .fanCertificateCap ∉ known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by
      simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by
      simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      simp [K_eq_iff])
    (fanSafeFresh : K .typeBFanSafe ∉ known := by simp [K_eq_iff]) :
    TypeBContinuationBoundary selected known := by
  -- `[67]`, `lem:heavy-neighbourhood-normal-form`, is already object-wide and
  -- uses exactly the selection and tight-endpoint facts in its manifest.
  let normal :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, normalFormFresh])
  letI : FactKeys.Has (K .typeBFanEntry)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail fanEntryHas.member⟩
  letI : FactKeys.Has (K .selection)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail selectionHas.member⟩
  letI : FactKeys.Has (K .bridgeless)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail bridgelessHas.member⟩
  letI : FactKeys.Has (K .replacementExclusion)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail replacementHas.member⟩
  letI : FactKeys.Has (K .tightEndpoint)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail tightHas.member⟩
  letI : FactKeys.Has (K .uncompressible)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail uncompressibleHas.member⟩
  letI : FactKeys.Has (K .remainderNormalized)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail remainderHas.member⟩
  letI : FactKeys.Has (K .remainderRelabelingEntropy)
      ([K .highCentreNormalForm] ++ known) :=
    ⟨.tail relabelingEntropyHas.member⟩
  exact selectedTypeBAfterNormalFormContinuation
      (known := [K .highCentreNormalForm] ++ known) normal
    (by simp [K_eq_iff, heavyFresh])
    (by simp [K_eq_iff, degreeFourFresh])
    (by simp [K_eq_iff, compatibilityFresh])
    (by simp [K_eq_iff, localFresh])
    (by simp [K_eq_iff, profileFresh])
    (by simp [K_eq_iff, triangularCoreFresh])
    (by simp [K_eq_iff, capFresh])
    (by simp [K_eq_iff, markedFresh])
    (by simp [K_eq_iff, residualFresh])
    (by simp [K_eq_iff, certificateMassFresh])
    (by simp [K_eq_iff, cycleFresh])
    (by simp [K_eq_iff, freeFresh])
    (by simp [K_eq_iff, choiceFresh])
    (by simp [K_eq_iff, obstructionFresh])
    (by simp [K_eq_iff, hybridFresh])
    (by simp [K_eq_iff, ledgerFresh])
    (by simp [K_eq_iff, excludedFresh])
    (by simp [K_eq_iff, exclusionResidualFresh])
    (by simp [K_eq_iff, exclusionMassFresh])
    (by simp [K_eq_iff, obstructionMassFresh])
    (fanClosedFresh := by simp [K_eq_iff, fanClosedFresh])
    (compatibleClosureFresh := by simp [K_eq_iff, compatibleClosureFresh])
    (fanClosedRoutingFresh := by simp [K_eq_iff, fanClosedRoutingFresh])
    (compatibleRoutingFresh := by simp [K_eq_iff, compatibleRoutingFresh])
    (triangularRoutingFresh := by simp [K_eq_iff, triangularRoutingFresh])
    (shoulderCompletionFresh := by simp [K_eq_iff, shoulderCompletionFresh])
    (portReturnFresh := by simp [K_eq_iff, portReturnFresh])
    (firstLandingFresh := by simp [K_eq_iff, firstLandingFresh])
    (crossShoulderFresh := by simp [K_eq_iff, crossShoulderFresh])
    (fanSafeFresh := by simp [K_eq_iff, fanSafeFresh])

/- The four literal accounting outputs of the common `[65]`--`[85]` path.
This proposition deliberately records only facts actually published by the
terminal owner on the active Type B arm. -/
private abbrev SelectedTypeBChargeBoundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateResidualMass
      selected.object ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .typeBExcluded selected.object ∨
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .typeBExclusionResidualMass
          selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .typeBOverlapObstructionMass
          selected.object

/- A type-valued sum of the same four terminal facts, used only while the
selected root is still transporting the concrete proof object returned by the
ledger.  Each summand is the canonical `Fact.At` type of its key. -/
private abbrev SelectedTypeBChargeOutcome (selected : EGInput.{u}) :=
  Sum ((K .fanCertificateResidualMass).At selected)
    (Sum ((K .typeBExcluded).At selected)
      (Sum ((K .typeBExclusionResidualMass).At selected)
        ((K .typeBOverlapObstructionMass).At selected)))

private noncomputable def selectedTypeBChargeBoundaryOfContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (boundary : TypeBAfterNormalFormBoundary selected known) :
    SelectedTypeBChargeOutcome selected := by
  rcases boundary with heavy | degreeFour
  · rcases heavy with mass | paid | mass | mass
    · exact Sum.inl (mass.get (K .fanCertificateResidualMass))
    · exact Sum.inr (Sum.inl (paid.get (K .typeBExcluded)))
    · exact Sum.inr (Sum.inr (Sum.inl
        (mass.get (K .typeBExclusionResidualMass))))
    · exact Sum.inr (Sum.inr (Sum.inr
        (mass.get (K .typeBOverlapObstructionMass))))
  · rcases degreeFour with mass | paid | mass | mass
    · exact Sum.inl (mass.get (K .fanCertificateResidualMass))
    · exact Sum.inr (Sum.inl (paid.get (K .typeBExcluded)))
    · exact Sum.inr (Sum.inr (Sum.inl
        (mass.get (K .typeBExclusionResidualMass))))
    · exact Sum.inr (Sum.inr (Sum.inr
        (mass.get (K .typeBOverlapObstructionMass))))

private noncomputable def selectedTypeBChargeOutcomeDown
    {selected : EGInput.{u}}
    (outcome : SelectedTypeBChargeOutcome selected) :
    SelectedTypeBChargeBoundary selected := by
  rcases outcome with mass | paid | mass | mass
  · exact Or.inl mass.down
  · exact Or.inr (Or.inl paid.down)
  · exact Or.inr (Or.inr (Or.inl mass.down))
  · exact Or.inr (Or.inr (Or.inr mass.down))

/-- `[144]` enters the common Type B continuation on its literal routed
ledger.  Its pre-audit has already published `[67]`, so this executor resumes
at `[68]` and returns the actual `[75]`/`[84]`, B2-paid, exclusion-residual, or
overlap-residual accounting fact. -/
private noncomputable def selectedSameTokenTypeBContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (triangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (capFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by
      simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by
      simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by
      simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by
      simp [K_eq_iff]) :
    SelectedTypeBChargeOutcome selected :=
  selectedTypeBChargeBoundaryOfContinuation
    (selectedTypeBAfterNormalFormContinuation history heavyFresh degreeFourFresh
      compatibilityFresh localFresh profileFresh triangularCoreFresh capFresh
      markedFresh residualFresh certificateMassFresh cycleFresh freeFresh
      choiceFresh obstructionFresh hybridFresh ledgerFresh excludedFresh
      exclusionResidualFresh exclusionMassFresh obstructionMassFresh
      (fanClosedFresh := fanClosedFresh)
      (compatibleClosureFresh := compatibleClosureFresh)
      (fanClosedRoutingFresh := fanClosedRoutingFresh)
      (compatibleRoutingFresh := compatibleRoutingFresh)
      (triangularRoutingFresh := triangularRoutingFresh)
      (shoulderCompletionFresh := shoulderCompletionFresh)
      (portReturnFresh := portReturnFresh)
      (firstLandingFresh := firstLandingFresh)
      (crossShoulderFresh := crossShoulderFresh))

noncomputable def selectedStrictSurplusBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    Sum
      (Sum ((K .typeBFanEntry).At selected)
        (SelectedTypeBChargeOutcome selected))
      ((K .pairConditionalFactorizationResidual).At selected) := by
  -- The enclosing `[20]` decision has already selected the survivor arm.
  -- `[125]` is the exact identity edge prescribed by the diagram; only that
  -- same ledger can enter `[126]`--`[128]` and `[129]`.
  let node125 := selectedSparseSurplusSurvivorNode125 history
  let activated := selectedSparseSurplusActivation node125
  let baseline := selectedBaselineSpineDemand activated
  match selectedPairResponseIndependenceDichotomy baseline with
  | .left independentHistory =>
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
              exact Sum.inr openResidual
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
                  exact Sum.inr openResidual
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
                      exact Sum.inl (Sum.inl typeBEntry)
                  | .right serialHistory =>
                      match pairIncrementCoveredDichotomy (data := spineData)
                          serialHistory (by simp [K_eq_iff])
                            (by simp [K_eq_iff]) with
                      | .right residualHistory =>
                          let openResidual := residualHistory.get
                            (K .pairConditionalFactorizationResidual)
                          change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
                          exact Sum.inr openResidual
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
                              exact Sum.inl (Sum.inl typeBEntry)
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
  | .right dependentHistory =>
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
                  exact Sum.inr openResidual
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
                      exact Sum.inr openResidual
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
                          exact Sum.inl (Sum.inl typeBEntry)
                      | .right serialHistory =>
                          match pairIncrementCoveredDichotomy (data := spineData)
                              serialHistory (by simp [K_eq_iff])
                                (by simp [K_eq_iff]) with
                          | .right residualHistory =>
                              let openResidual := residualHistory.get
                                (K .pairConditionalFactorizationResidual)
                              change ((K .pairConditionalFactorizationResidual).At selected) at openResidual
                              exact Sum.inr openResidual
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
                                  exact Sum.inl (Sum.inl typeBEntry)
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
                  let normal :=
                    (highCentreNormalFormRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run overloadHistory (by
                        simp [highCentreNormalFormRow, K_eq_iff])
                  -- `[144]` consumes the standing cubic-baseline equation as
                  -- an ExactLedger fact.  Append it here, once, instead of
                  -- reconstructing `threshold = 3` inside the bottleneck row.
                  let cubic :=
                    (cubicBaselineRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run normal (by
                        simp [cubicBaselineRow, highCentreNormalFormRow,
                          K_eq_iff])
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
                      exact Sum.inl (Sum.inr
                        (selectedSameTokenTypeBContinuation routed))
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
                          exact Sum.inl (Sum.inr
                            (selectedSameTokenTypeBContinuation routed))
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
                          exact Sum.inl (Sum.inr
                            (selectedSameTokenTypeBContinuation routed))

/-- The exact Part-IX output of nodes `[76]`/`[85]`: the census of the route-8
cores extracted from the centre-deleted Type-B pieces, together with the
sublinear bound on the bridge mass that remains after that extraction.  The
existential index keeps the complete incoming charge ledger; it does not coerce
the carrier to a canonical negative support. -/
abbrev SelectedExtractedTypeBRoute8Boundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ExtractedEntryCensus
      selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBBridgeSublinear selected.object

/-- `[76]`/`[85]` → `[77]`, on an already charged Type-B boundary.  The
registered owners read the surplus bound, selection, replacement exclusion,
and cubic baseline from this exact ledger and publish
`K .typeBBridgeSublinear` and `K .route8ExtractedEntryCensus`.  They never
manufacture the ordinary `K .negativeSupport`, the whole-remainder unified
census, or a quotient-test residual. -/
noncomputable def selectedTypeBExtractedRoute8Continuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by
      simp [K_eq_iff])
    (cubicFresh : K .cubicBaseline ∉ known := by simp [K_eq_iff])
    (extractedFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff]) :
    SelectedExtractedTypeBRoute8Boundary selected := by
  let cubic :=
    (cubicBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, cubicFresh])
  let extracted :=
    (route8ExtractedEntryCensusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, extractedFresh])
  let bridgeMass :=
    (bridgeFanMassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      extracted (by simp [K_eq_iff, bridgeMassFresh])
  let bridgeSublinear :=
    (typeBBridgeSublinearRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      bridgeMass (by simp [K_eq_iff, bridgeSublinearFresh])
  exact ⟨(bridgeSublinear.get (K .route8ExtractedEntryCensus)).down,
    (bridgeSublinear.get (K .typeBBridgeSublinear)).down⟩

/-- The common charged tail of the absorbed case-(ii) family.  Its input is
the literal `[177]` ledger, possibly already carrying `[176]`'s closure for the
case-(i) subfamily.  Every Type-B alternative is consumed at its registered
owner and then converted by the common `[76]`/`[85]` quantitative tail.  Thus a
mixed absorbed family never discards the facts appended before this call. -/
private noncomputable def selectedAbsorbedFanChargeContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (heavyFresh : K .typeBFanHeavyCentre ∉ known)
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known)
    (localFresh : K .typeBFanLocalDichotomy ∉ known)
    (profileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (triangularFresh : K .triangularFanCore ∉ known)
    (capFresh : K .fanCertificateCap ∉ known)
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (cubicFresh : K .cubicBaseline ∉ known)
    (extractedFresh : K .route8ExtractedEntryCensus ∉ known) :
    SelectedExtractedTypeBRoute8Boundary selected := by
  let boundary := selectedTypeBContinuation history
    (by simp [K_eq_iff, normalFormFresh])
    (by simp [K_eq_iff, heavyFresh])
    (by simp [K_eq_iff, degreeFourFresh])
    (by simp [K_eq_iff, compatibilityFresh])
    (by simp [K_eq_iff, localFresh])
    (by simp [K_eq_iff, profileFresh])
    (by simp [K_eq_iff, triangularFresh])
    (by simp [K_eq_iff, capFresh])
    (by simp [K_eq_iff, markedFresh])
    (by simp [K_eq_iff, residualFresh])
    (by simp [K_eq_iff, certificateMassFresh])
    (by simp [K_eq_iff, cycleFresh])
    (by simp [K_eq_iff, freeFresh])
    (by simp [K_eq_iff, choiceFresh])
    (by simp [K_eq_iff, obstructionFresh])
    (by simp [K_eq_iff, hybridFresh])
    (by simp [K_eq_iff, ledgerFresh])
    (by simp [K_eq_iff, excludedFresh])
    (by simp [K_eq_iff, exclusionResidualFresh])
    (by simp [K_eq_iff, exclusionMassFresh])
    (by simp [K_eq_iff, obstructionMassFresh])
  match boundary with
  | .inl (.inl mass) =>
      exact selectedTypeBExtractedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inl (.inr (.inl paid)) =>
      exact selectedTypeBExtractedRoute8Continuation paid
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inl (.inr (.inr (.inl mass))) =>
      exact selectedTypeBExtractedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inl (.inr (.inr (.inr mass))) =>
      exact selectedTypeBExtractedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inr (.inl mass) =>
      exact selectedTypeBExtractedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inr (.inr (.inl paid)) =>
      exact selectedTypeBExtractedRoute8Continuation paid
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inr (.inr (.inr (.inl mass))) =>
      exact selectedTypeBExtractedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])
  | .inr (.inr (.inr (.inr mass))) =>
      exact selectedTypeBExtractedRoute8Continuation mass
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicFresh])
        (by simp [K_eq_iff, extractedFresh])

/-- The quantitative tail of `[76]`/`[85]` on the near-cubic inputs for which
the paper actually supplies the ordinary route-8 census facts.  This wrapper is
deliberately separate from `selectedTypeBCertificateBoundary`; `[144]` and
`[177]` cannot enter it merely because they also reach node `[65]`. -/
noncomputable def selectedTypeBNearCubicCertificateAfterPortRouting
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .fanClosedPort) known]
    [FactKeys.Has (K .compatiblePairFanClosure) known]
    [FactKeys.Has (K .fanClosedPortTypeBRouting) known]
    [FactKeys.Has (K .compatiblePairTypeBRouting) known]
    (markedFresh : K .fanCertificateMarked ∉ known)
    (residualFresh : K .fanCertificateResidual ∉ known)
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (cycleFresh : K .typeBDirectCycle ∉ known)
    (freeFresh : K .typeBDirectCycleFree ∉ known)
    (choiceFresh : K .typeBB2Choice ∉ known)
    (obstructionFresh : K .typeBOverlapObstruction ∉ known)
    (hybridFresh : K .typeBHybridEntry ∉ known)
    (ledgerFresh : K .typeBDisjointLedger ∉ known)
    (excludedFresh : K .typeBExcluded ∉ known)
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (bridgeMassFresh : K .typeBBridgeMass ∉ known)
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by
      simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by
      simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by
      simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known) :
    SelectedRouteEightBoundary selected := by
  match selectedTypeBCertificateBoundaryAfterPortRouting history markedFresh residualFresh
      certificateMassFresh cycleFresh freeFresh choiceFresh obstructionFresh
      hybridFresh ledgerFresh excludedFresh exclusionResidualFresh
      exclusionMassFresh obstructionMassFresh with
  | .inl mass =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
        (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
  | .inr (.inl paid) =>
      rcases (paid.get (K .typeBExcluded)).down with canonical | _handoff
      · obtain ⟨_packing, _valid, _maximal, canonicalPiece,
          _centres, assigned, nonnegative⟩ := canonical
        have negative : selected.object.NegativeNetCharge
            canonicalPiece.vertices spineData.threshold
            spineData.dischargeScale := by
          rcases assigned with ⟨negative, _, _⟩ | ⟨negative, _, _⟩ <;>
            exact negative
        exact ((selected.object.not_negativeNetCharge_iff
          canonicalPiece.vertices spineData.threshold
            spineData.dischargeScale).mpr nonnegative negative).elim
      · exact selectedTypeBRoute8Continuation paid
          (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
          (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
          (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
          (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
          (typeBBridgeReductionFresh := by
            simp [K_eq_iff, typeBBridgeReductionFresh])
          (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
          (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
          (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
          (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
          (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
          (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
          (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
          (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
          (peelingFresh := by simp [K_eq_iff, peelingFresh])
          (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
          (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
          (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
          (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
          (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
          (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
  | .inr (.inr (.inl mass)) =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
        (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
  | .inr (.inr (.inr mass)) =>
      exact selectedTypeBRoute8Continuation mass
        (bridgeMassFresh := by simp [K_eq_iff, bridgeMassFresh])
        (bridgeSublinearFresh := by simp [K_eq_iff, bridgeSublinearFresh])
        (unifiedNegativeFresh := by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])

/-- Compatibility name for callers that already carry the common `[72]`
port-routing ledger.  New branch assembly uses the explicit
`AfterPortRouting` name so duplicate publication is impossible. -/
noncomputable abbrev selectedTypeBNearCubicCertificate :=
  @selectedTypeBNearCubicCertificateAfterPortRouting

/-- **Type B `[67]`--`[70]` on the decorated envelope** (`def:decorated-fan-envelope`,
`def:typeB-assigned-ledger`), on the `[108]`/`[65]` decorated residual
(index-polymorphic).  `[67]` `lem:heavy-neighbourhood-normal-form` and the
registered cubic baseline (object-level rows), `[68]` the single degree split at
the common assigned centres (`typeBFanDegreeDichotomy`), heavy → `[69]`
`cor:heavy-center-local-dichotomy` (`typeBFanLocalDichotomyRow`),
degree-four → `[78]`--`[79]` `cor:degree-four-local-activation`
(`typeBFanDegreeFourProfileRow`); both arms then read `[70]` `lem:fan-certificate`
(`fanCertificateCapRow`); both arms then enter `[71]`/`[80]` on the common
Type B fan support (`selectedTypeBDecoratedCertificate`). -/
-- EG-NODE [67] high-degree centers independent; fan neighbours cubic
-- EG-NODE [68] some center has d_G(h) > 4 ?
-- EG-NODE [69] degree >4 local dichotomy: fan-compatible open pair or ports
-- EG-NODE [70] fan-safe graph, P13 certificate graph, cap d_G(h)<=8
-- EG-NODE [78] degree-4 branch: d_G(h)=4
-- EG-NODE [79] degree-4 fan profile: center surplus 1, 0<=c<=4, D_B=c-7/4
noncomputable def selectedTypeBDecoratedContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBDecoratedAssignedSupport) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff]) :
    SelectedRouteEightBoundary selected := by
  -- `[67]`
  let normalForm :=
    (highCentreNormalFormRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, normalFormFresh])
  -- `[68]` at the decorated envelope's assigned centres.
  match typeBFanDegreeDichotomy (data := spineData) normalForm
      (by simp [K_eq_iff, decoratedHeavyFresh])
      (by simp [K_eq_iff, decoratedDegreeFourFresh]) with
  | .left heavyHistory =>
      -- `[69]`: the compatibility lemma is a first-class ledger fact consumed
      -- by the heavy-centre dichotomy on this same decorated envelope.
      let compatibleHistory :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory
            (by simp [K_eq_iff, decoratedCompatibilityFresh])
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatibleHistory (by simp [K_eq_iff, decoratedLocalFresh])
      let portRouted := selectedTypeBPortRoutingPrefix localDichotomy
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      -- `[70]`
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, fanCapFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, decoratedMarkedFresh])
        (by simp [K_eq_iff, decoratedResidualFresh])
        (by simp [K_eq_iff, decoratedCertificateMassFresh])
        (by simp [K_eq_iff, decoratedCycleFresh])
        (by simp [K_eq_iff, decoratedFreeFresh])
        (by simp [K_eq_iff, decoratedB2ChoiceFresh])
        (by simp [K_eq_iff, decoratedB2ObstructionFresh])
        (by simp [K_eq_iff, decoratedHybridFresh])
        (by simp [K_eq_iff, decoratedLedgerFresh])
        (by simp [K_eq_iff, decoratedExcludedFresh])
        (by simp [K_eq_iff, decoratedExclusionResidualFresh])
        (by simp [K_eq_iff, decoratedExclusionMassFresh])
        (by simp [K_eq_iff, decoratedObstructionMassFresh])
        (by simp [K_eq_iff, decoratedBridgeMassFresh])
        (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, decoratedProfileFresh])
      let triangularCore :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, decoratedTriangularCoreFresh])
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularCore (by simp [K_eq_iff, shoulderCompletionFresh])
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by simp [K_eq_iff, portReturnFresh])
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by simp [K_eq_iff, firstLandingFresh])
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by simp [K_eq_iff, crossShoulderFresh])
      let portRouted := selectedTypeBPortRoutingPrefix crossShouldered
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, triangularRoutingFresh])
      -- `[70]`/`[80]`
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by simp [K_eq_iff, fanCapFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, decoratedMarkedFresh])
        (by simp [K_eq_iff, decoratedResidualFresh])
        (by simp [K_eq_iff, decoratedCertificateMassFresh])
        (by simp [K_eq_iff, decoratedCycleFresh])
        (by simp [K_eq_iff, decoratedFreeFresh])
        (by simp [K_eq_iff, decoratedB2ChoiceFresh])
        (by simp [K_eq_iff, decoratedB2ObstructionFresh])
        (by simp [K_eq_iff, decoratedHybridFresh])
        (by simp [K_eq_iff, decoratedLedgerFresh])
        (by simp [K_eq_iff, decoratedExcludedFresh])
        (by simp [K_eq_iff, decoratedExclusionResidualFresh])
        (by simp [K_eq_iff, decoratedExclusionMassFresh])
        (by simp [K_eq_iff, decoratedObstructionMassFresh])
        (by simp [K_eq_iff, decoratedBridgeMassFresh])
        (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by
          simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])

/-- **Node `[108]` → Type B `[65]` on the decorated envelope**: the exact
envelope committed at `[108]` (`K .typeAExitSevenHandoff`) enters the Type B
branch at `[65]`.  There `typeBDecoratedAssignedSupportRow` reads the inherited
selection, normalization, and uncompressibility facts, proves
`lem:decorated-fan-admissibility`, and commits the envelope's assigned support.
Then `[67]`--`[70]` run on that decorated envelope
(`selectedTypeBDecoratedContinuation`). -/
-- EG-NODE [65] Type B assigned support: high-degree fan centers and decorated envelope
noncomputable def selectedTypeADecoratedHandoff
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known)
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known) :
    SelectedRouteEightBoundary selected := by
  let assigned :=
    (typeBDecoratedAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, decoratedFresh, decoratedFanEntryFresh])
  exact selectedTypeBDecoratedContinuation assigned
    (by simp [K_eq_iff, normalFormFresh])
    (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh])
    (by simp [K_eq_iff, decoratedLocalFresh])
    (by simp [K_eq_iff, decoratedCompatibilityFresh])
    (by simp [K_eq_iff, decoratedProfileFresh])
    (by simp [K_eq_iff, decoratedTriangularCoreFresh])
    (by simp [K_eq_iff, fanCapFresh])
    (by simp [K_eq_iff, decoratedMarkedFresh])
    (by simp [K_eq_iff, decoratedResidualFresh])
    (by simp [K_eq_iff, decoratedCertificateMassFresh])
    (by simp [K_eq_iff, decoratedCycleFresh])
    (by simp [K_eq_iff, decoratedFreeFresh])
    (by simp [K_eq_iff, decoratedB2ChoiceFresh])
    (by simp [K_eq_iff, decoratedB2ObstructionFresh])
    (by simp [K_eq_iff, decoratedHybridFresh])
    (by simp [K_eq_iff, decoratedLedgerFresh])
    (by simp [K_eq_iff, decoratedBridgeMassFresh])
    (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
    (by simp [K_eq_iff, unifiedNegativeFresh])
    (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
    (typeBBridgeReductionFresh := by
      simp [K_eq_iff, typeBBridgeReductionFresh])
    (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
    (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
    (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
    (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
    (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
    (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
    (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
    (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
    (peelingFresh := by simp [K_eq_iff, peelingFresh])
    (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
    (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
    (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
    (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
    (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
    (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
    (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
    (decoratedExclusionResidualFresh := by
      simp [K_eq_iff, decoratedExclusionResidualFresh])
    (decoratedExclusionMassFresh := by
      simp [K_eq_iff, decoratedExclusionMassFresh])
    (decoratedObstructionMassFresh := by
      simp [K_eq_iff, decoratedObstructionMassFresh])

/-- **Nodes `[103]`--`[109]`: exits `(5)`--`(7)` and the route-8 residual**, on the
saturated-handoff state after exit `(4)` is absent (index-polymorphic).
`[103]` exit `(5)`: a target-complete proper-support compression closes at
`[104]` against `cor:uncompressible`.  `[105]` exit `(6)`: a delocalizing
response equality is localized at `[106]` — proper scope closes against
`lem:replacement` (`K .replacementExclusion`), global scope against the
selection's minimality.  `[107]` exit `(7)`: the decorated handoff fan envelope
is committed as the Type B handoff at `[108]`; its admissibility is proved at
`[65]`, the next producer on that lane.  Its absence is `[109]`, the route-8
residual continued in Part IX (`[110]`, the next producer). -/
-- EG-NODE [103] exit 5? target-complete response compression
-- EG-NODE [104] uncompressibility contradiction
-- EG-NODE [105] exit 6? proper/global delocalization
-- EG-NODE [106] delocalization branch closes
-- EG-NODE [107] exit 7? decorated handoff fan
-- EG-NODE [108] returns to Type B handoff
-- EG-NODE [66] Type A exit 7 input from the Part VIII handoff
noncomputable def selectedTypeAExitFiveToSeven
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
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
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
  -- `[103]`
  match typeAExitFiveDichotomy (data := spineData) history fiveFresh fiveFreeFresh with
  | .left fiveHistory =>
      -- `[104]`
      exact ((closeIncompatible fiveHistory (K .uncompressible) (K .typeAExitFive)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)).elim
  | .right fiveFree =>
      -- `[105]`
      match typeAExitSixDichotomy (data := spineData) fiveFree
          (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh]) with
      | .left sixHistory =>
          -- `[106]`
          match typeAExitSixScopeDichotomy (data := spineData) sixHistory
              (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh]) with
          | .left properHistory =>
              exact ((closeIncompatible properHistory (K .replacementExclusion)
                (K .typeAExitSixProper) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)).elim
          | .right globalHistory =>
              exact ((closeIncompatible globalHistory (K .selection)
                (K .typeAExitSixGlobal) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)).elim
      | .right sixFree =>
          -- `[107]`
          match typeAExitSevenDichotomy (data := spineData) sixFree
              (by simp [K_eq_iff, sevenProducedFresh])
              (by simp [K_eq_iff, sevenFreeFresh]) with
          | .left producedHistory =>
              -- `[108]`: record the produced Type B handoff envelope; `[65]`
              -- proves its admissibility — the next producer.
              let handoff :=
                (typeAExitSevenHandoffRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  producedHistory (by simp [K_eq_iff, sevenHandoffFresh])
              exact selectedTypeADecoratedHandoff handoff (by simp [K_eq_iff, decoratedFresh])
                (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
                (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
                (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
                (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
                (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
          | .right route8History =>
              -- `[109]` is the shared no-exit-`(7)` residual drawn in Part
              -- VIII.  After any finite exit-`(4)` peeling the residual may be
              -- on the silent side of `lem:typeA-exit4-residual-routing`, so
              -- the paper sends this exact ledger to `[110]`; it has no
              -- visible-lane impossibility terminal.
              exact selectedRouteEightResidual route8History
                (by simp [K_eq_iff, profileFresh])
                (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh])
                (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, deficitFailsFresh])
                (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, decoratedBridgeMassFresh])
                (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
                (by simp [K_eq_iff, censusFresh])
                (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by
                  simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])

/-- The silent-lane copy of `selectedTypeAExitFiveToSeven` (`[94]` →
`[101]`--`[109]`): identical exits `(5)`--`(7)`, and the exit-`(8)` residual
`[109]` continues into Part IX (`selectedRouteEightResidual`), which needs the
silent-excess count `[94]` and the large-budget residual on the ledger. -/
-- EG-NODE [103] exit 5? target-complete response compression
-- EG-NODE [104] uncompressibility contradiction
-- EG-NODE [105] exit 6? proper/global delocalization
-- EG-NODE [106] delocalization branch closes
-- EG-NODE [107] exit 7? decorated handoff fan
-- EG-NODE [108] returns to Type B handoff
-- EG-NODE [109] route-8 residual continued in Part IX
noncomputable def selectedTypeAExitFiveToSevenSilent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
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
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
  -- `[103]`
  match typeAExitFiveDichotomy (data := spineData) history fiveFresh fiveFreeFresh with
  | .left fiveHistory =>
      -- `[104]`
      exact ((closeIncompatible fiveHistory (K .uncompressible) (K .typeAExitFive)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)).elim
  | .right fiveFree =>
      -- `[105]`
      match typeAExitSixDichotomy (data := spineData) fiveFree
          (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh]) with
      | .left sixHistory =>
          -- `[106]`
          match typeAExitSixScopeDichotomy (data := spineData) sixHistory
              (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh]) with
          | .left properHistory =>
              exact ((closeIncompatible properHistory (K .replacementExclusion)
                (K .typeAExitSixProper) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)).elim
          | .right globalHistory =>
              exact ((closeIncompatible globalHistory (K .selection)
                (K .typeAExitSixGlobal) (by simp [K_eq_iff, closureFresh])).elimClosed
                (by infer_instance)).elim
      | .right sixFree =>
          -- `[107]`
          match typeAExitSevenDichotomy (data := spineData) sixFree
              (by simp [K_eq_iff, sevenProducedFresh])
              (by simp [K_eq_iff, sevenFreeFresh]) with
          | .left producedHistory =>
              -- `[108]`: record the produced Type B handoff envelope; `[65]`
              -- proves its admissibility — the next producer.
              let handoff :=
                (typeAExitSevenHandoffRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  producedHistory (by simp [K_eq_iff, sevenHandoffFresh])
              exact selectedTypeADecoratedHandoff handoff (by simp [K_eq_iff, decoratedFresh])
                (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
                (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
                (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
                (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
                (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
          | .right route8History =>
              -- `[109]` → `[110]`: the route-8 residual of Part IX on the silent
              -- lane.
              exact selectedRouteEightResidual route8History
                (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, deficitFailsFresh])
                (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, decoratedBridgeMassFresh])
                (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by
                  simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])

/-- **`[102]` → `[89]`, the retest of the peeled receiver.**  `K
.typeAExitFourReceiverDischarged` records the outcome of the recompute-`L₄`
loop: a witnessed peeling set `P₄(w)` at which the receiver is unsaturated
(`lem:typeA-exit4-peeling-charge`: the remaining receiver charge
`q(w) − ¼ − ¼L₄(w)` is nonnegative).  Its peeled loads and their remaining
negative mass enter node `[123]`'s unified target-defect/route-8 pressure
ledger, where `lem:typeA-pressure-is-exit4-peel` reads the witnesses. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedTypeAExitFourDischargedRetest
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFourReceiverDischarged) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (terminalFresh : K .route8TerminalNoGo ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known) :
    SelectedRouteEightBoundary selected := by
  -- Read the discharged receiver fact from the accumulated ledger.
  let _discharged := history.get (K .typeAExitFourReceiverDischarged)
  -- `[123]`: publish `def:typeA-unified-negative` on this residual.
  let unifiedNegative :=
    (route8UnifiedNegativeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, unifiedNegativeFresh])
  let typeAExcluded :=
    (typeAExclusionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      unifiedNegative (by simp [K_eq_iff, typeAExclusionFresh])
  let typeBReduced :=
    (typeBBridgeReductionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeAExcluded (by simp [K_eq_iff, typeBBridgeReductionFresh])
  let classified :=
    (route8PiecesClassifiedRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      typeBReduced (by simp [K_eq_iff, piecesClassifiedFresh])
  match typeBSublinearDichotomy (data := spineData) classified
      (by simp [K_eq_iff, sublinearLedgerFresh])
      (by simp [K_eq_iff, sublinearResidualFresh]) with
  | .right residualHistory =>
      exact Or.inl (residualHistory.get (K .typeBSublinearResidual)).down
  | .left sublinearHistory =>
      let unifiedDeficit :=
        (route8UnifiedDeficitRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          sublinearHistory (by simp [K_eq_iff, unifiedDeficitFresh])
      match route8QuotientDichotomy (data := spineData) unifiedDeficit
          (by simp [K_eq_iff, quotientFreeFresh])
          (by simp [K_eq_iff, quotientResidualFresh]) with
      | .right residualHistory =>
          exact Or.inr (Or.inl
            (residualHistory.get (K .route8QuotientResidual)).down)
      | .left quotientFreeHistory =>
          let census :=
            (route8UnifiedEntryCensusRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run quotientFreeHistory
                (by simp [K_eq_iff, unifiedCensusFresh])
          let peeled := selectedLargeBudgetPressureCensus census
            (peelingFresh := by simp [K_eq_iff, peelingFresh])
            (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
            (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
            (terminalFresh := by simp [K_eq_iff, terminalFresh])
            (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
            (demandAbsorptionFresh := by
              simp [K_eq_iff, demandAbsorptionFresh])
            (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
            (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
          exact Or.inr (Or.inr
            (peeled.get (K .route8PeeledDemandResidual)).down)

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
-- EG-NODE [101] exit 4? target-defective quotient
-- EG-NODE [102] target-defect peels one load
noncomputable def selectedTypeAExitFourChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
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
    (cubicBaselineFresh : K .cubicBaseline ∉ known)
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
  let cubic :=
    (cubicBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, cubicBaselineFresh])
  -- `lem:typeA-exit4-finite-descent` on the ledger (read again at `[123]`).
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, descentFresh])
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
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
            (by simp [K_eq_iff, trueResidualFresh])
            (by simp [K_eq_iff, cutParityFresh]) (by simp [K_eq_iff, smallFresh])
            (by simp [K_eq_iff, noSmallFresh]) (by simp [K_eq_iff, collapseFresh])
            (by simp [K_eq_iff, deletionWitnessesFresh])
            (by simp [K_eq_iff, privateBudgetFresh])
            (by simp [K_eq_iff, noTwoContradictionFresh])
            (by simp [K_eq_iff, terminalNoGoFresh])
            (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
            (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
            (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
            (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
            (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
            (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
            (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
            (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
            (by simp [K_eq_iff, unifiedNegativeFresh])
            (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
            (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
            (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
            (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
            (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
            (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
            (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
            (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
            (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
            (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
            (peelingFresh := by simp [K_eq_iff, peelingFresh])
            (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
            (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
            (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
            (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
            (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
            (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
            (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
            (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
            (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
            (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right dischargedHistory =>
          -- `[89]` retest of the discharged receiver with its peeled
          -- target-defect loads (Part IX pressure ledger `[123]`) — the next
          -- producer.
          exact selectedTypeAExitFourDischargedRetest dischargedHistory
            (by simp [K_eq_iff, unifiedNegativeFresh])
            (by simp [K_eq_iff, typeAExclusionFresh])
            (by simp [K_eq_iff, typeBBridgeReductionFresh])
            (by simp [K_eq_iff, piecesClassifiedFresh])
            (by simp [K_eq_iff, sublinearLedgerFresh])
            (by simp [K_eq_iff, sublinearResidualFresh])
            (by simp [K_eq_iff, unifiedDeficitFresh])
            (by simp [K_eq_iff, quotientFreeFresh])
            (by simp [K_eq_iff, quotientResidualFresh])
            (by simp [K_eq_iff, unifiedCensusFresh])
            (by simp [K_eq_iff, peelingFresh])
            (by simp [K_eq_iff, unifiedTrueFresh])
            (by simp [K_eq_iff, stageFailedFresh])
            (by simp [K_eq_iff, unifiedTerminalFresh])
            (by simp [K_eq_iff, demandLedgerFresh])
            (by simp [K_eq_iff, demandAbsorptionFresh])
            (by simp [K_eq_iff, windowBlockersFresh])
            (by simp [K_eq_iff, demandResidualFresh])
  | .right freeHistory =>
      exact selectedTypeAExitFiveToSeven freeHistory
        (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
        (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
        (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
        (by simp [K_eq_iff, trueResidualFresh])
        (by simp [K_eq_iff, cutParityFresh]) (by simp [K_eq_iff, smallFresh])
        (by simp [K_eq_iff, noSmallFresh]) (by simp [K_eq_iff, collapseFresh])
        (by simp [K_eq_iff, deletionWitnessesFresh])
        (by simp [K_eq_iff, privateBudgetFresh])
        (by simp [K_eq_iff, noTwoContradictionFresh])
        (by simp [K_eq_iff, terminalNoGoFresh])
        (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
        (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
        (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
        (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
        (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
        (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
        (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
        (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
        (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
        (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
        (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
        (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
        (by simp [K_eq_iff, closureFresh])

/-- The silent-lane copy of `selectedTypeAExitFourChain` (`[94]` → `[101]`--`[109]`
→ Part IX). -/
-- EG-NODE [101] exit 4? target-defective quotient
-- EG-NODE [102] target-defect peels one load
noncomputable def selectedTypeAExitFourChainSilent
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
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
    (cubicBaselineFresh : K .cubicBaseline ∉ known)
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
  let cubic :=
    (cubicBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, cubicBaselineFresh])
  -- `lem:typeA-exit4-finite-descent` on the ledger (read again at `[123]`).
  let descended :=
    (typeAExitFourFiniteDescentRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, descentFresh])
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
            (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh]) (by simp [K_eq_iff, decoratedExcludedFresh]) (by simp [K_eq_iff, decoratedExclusionResidualFresh]) (by simp [K_eq_iff, decoratedExclusionMassFresh]) (by simp [K_eq_iff, decoratedObstructionMassFresh])
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, deficitFailsFresh])
            (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
            (by simp [K_eq_iff, closureFresh])
      | .right dischargedHistory =>
          -- `[89]` retest of the discharged receiver with its peeled
          -- target-defect loads (Part IX pressure ledger `[123]`) — the next
          -- producer.
          exact selectedTypeAExitFourDischargedRetest dischargedHistory
            (by simp [K_eq_iff, unifiedNegativeFresh])
            (by simp [K_eq_iff, typeAExclusionFresh])
            (by simp [K_eq_iff, typeBBridgeReductionFresh])
            (by simp [K_eq_iff, piecesClassifiedFresh])
            (by simp [K_eq_iff, sublinearLedgerFresh])
            (by simp [K_eq_iff, sublinearResidualFresh])
            (by simp [K_eq_iff, unifiedDeficitFresh])
            (by simp [K_eq_iff, quotientFreeFresh])
            (by simp [K_eq_iff, quotientResidualFresh])
            (by simp [K_eq_iff, unifiedCensusFresh])
            (by simp [K_eq_iff, peelingFresh])
            (by simp [K_eq_iff, unifiedTrueFresh])
            (by simp [K_eq_iff, stageFailedFresh])
            (by simp [K_eq_iff, unifiedTerminalFresh])
            (by simp [K_eq_iff, demandLedgerFresh])
            (by simp [K_eq_iff, demandAbsorptionFresh])
            (by simp [K_eq_iff, windowBlockersFresh])
            (by simp [K_eq_iff, demandResidualFresh])
  | .right freeHistory =>
      exact selectedTypeAExitFiveToSevenSilent freeHistory
        (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
        (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
        (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
        (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
        (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
        (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh]) (by simp [K_eq_iff, decoratedExcludedFresh]) (by simp [K_eq_iff, decoratedExclusionResidualFresh]) (by simp [K_eq_iff, decoratedExclusionMassFresh]) (by simp [K_eq_iff, decoratedObstructionMassFresh])
        (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
        (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
        (by simp [K_eq_iff, deficitFailsFresh])
        (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
        (by simp [K_eq_iff, closureFresh])

/-- **Node `[99]` → `[101]`, the visible lane**: the shared saturated exit entry
at the empty peeling set (`lem:typeA-unpeeled-visible-routing`), then the exit
segment `[101]`--`[109]`. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedTypeAVisibleExitFour
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAExitThreeFree) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
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
    (cubicBaselineFresh : K .cubicBaseline ∉ known)
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
  let entered :=
    (typeAVisibleExitEntryRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, entryFresh])
  exact selectedTypeAExitFourChain entered
    (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
    (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
    (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
    (by simp [K_eq_iff, trueResidualFresh]) (by simp [K_eq_iff, cutParityFresh])
    (by simp [K_eq_iff, smallFresh]) (by simp [K_eq_iff, noSmallFresh])
    (by simp [K_eq_iff, collapseFresh]) (by simp [K_eq_iff, deletionWitnessesFresh])
    (by simp [K_eq_iff, privateBudgetFresh])
    (by simp [K_eq_iff, noTwoContradictionFresh])
    (by simp [K_eq_iff, terminalNoGoFresh])
    (by simp [K_eq_iff, descentFresh]) (by simp [K_eq_iff, exitFourFresh])
    (by simp [K_eq_iff, exitFourFreeFresh]) (by simp [K_eq_iff, peeledFresh])
    (by simp [K_eq_iff, dischargedFresh])
    (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
    (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
    (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
    (by simp [K_eq_iff, sevenProducedFresh]) (by simp [K_eq_iff, sevenFreeFresh])
    (by simp [K_eq_iff, sevenHandoffFresh]) (by simp [K_eq_iff, decoratedFresh])
    (by simp [K_eq_iff, cubicBaselineFresh]) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
    (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
    (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
    (by simp [K_eq_iff, unifiedNegativeFresh])
    (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
    (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
    (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
    (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
    (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
    (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
    (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
    (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
    (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
    (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
    (peelingFresh := by simp [K_eq_iff, peelingFresh])
    (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
    (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
    (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
    (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
    (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
    (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
    (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
    (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
    (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
    (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
    (by simp [K_eq_iff, closureFresh])

/-- **Node `[94]` → `[101]`, the silent lane**: the shared saturated exit entry
at the empty peeling set (`lem:typeA-unpeeled-silent-routing`), then the exit
segment `[101]`--`[109]`. -/
-- EG-NODE none (establishes no manuscript DAG node)
noncomputable def selectedTypeASilentExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAVisibleFirstExcess) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
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
    (cubicBaselineFresh : K .cubicBaseline ∉ known)
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
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
    (by simp [K_eq_iff, cubicBaselineFresh]) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh]) (by simp [K_eq_iff, decoratedExcludedFresh]) (by simp [K_eq_iff, decoratedExclusionResidualFresh]) (by simp [K_eq_iff, decoratedExclusionMassFresh]) (by simp [K_eq_iff, decoratedObstructionMassFresh])
    (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
    (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
    (by simp [K_eq_iff, deficitFailsFresh])
    (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
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
-- EG-NODE [95] exit 1? Mersenne return
-- EG-NODE [96] target cycle
-- EG-NODE [97] exit 2? power-of-two theta
-- EG-NODE [98] target cycle
-- EG-NODE [99] exit 3? P13 label collision
-- EG-NODE [100] label/target collision
noncomputable def selectedTypeAVisibleExitChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeAVisibleEntry) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    (profileFresh : K .route8ResidualProfile ∉ known)
    (squeezeFresh : K .route8GlobalSqueeze ∉ known)
    (burdenFresh : K .route8BasinBurden ∉ known)
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known)
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known)
    (coreFresh : K .route8CarrierCore ∉ known)
    (trueResidualFresh : K .route8TrueResidual ∉ known)
    (cutParityFresh : K .route8CarrierCutParity ∉ known)
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known)
    (collapseFresh : K .route8SmallCoreCollapse ∉ known)
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known)
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known)
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known)
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known)
    (returnFresh : K .typeAExitOneReturn ∉ known)
    (oneFreeFresh : K .typeAExitOneFree ∉ known)
    (thetaFresh : K .typeAExitTwoTheta ∉ known)
    (twoFreeFresh : K .typeAExitTwoFree ∉ known)
    (collisionFresh : K .typeAExitThreeCollision ∉ known)
    (threeFreeFresh : K .typeAExitThreeFree ∉ known)
    -- Type A exits `(4)`--`(7)`, `[101]`--`[109]` (`selectedTypeAExitFourChain`).
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
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
    (cubicBaselineFresh : K .cubicBaseline ∉ known)
    (normalFormFresh : K .highCentreNormalForm ∉ known)
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known)
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known)
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known)
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known)
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known)
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known)
    (fanCapFresh : K .fanCertificateCap ∉ known)
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known)
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known)
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known)
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known)
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known)
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known)
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known)
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known)
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known)
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known)
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known)
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known)
    (censusFresh : K .route8Census ∉ known)
    (twoFresh : K .route8TwoCarrierEntry ∉ known)
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known)
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known)
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known)
    (typeAExclusionFresh : K .typeAExclusion ∉ known)
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known)
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known)
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known)
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known)
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known)
    (quotientFreeFresh : K .route8QuotientFree ∉ known)
    (quotientResidualFresh : K .route8QuotientResidual ∉ known)
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known)
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known)
    (decoratedExcludedFresh : K .typeBExcluded ∉ known)
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known)
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known)
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known)
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known) : SelectedRouteEightBoundary selected := by
  -- `[95]`
  match typeAExitOneDichotomy (data := spineData) history returnFresh oneFreeFresh with
  | .left returnHistory =>
      -- `[96]`
      exact ((closeIncompatible returnHistory (K .returnAvoidance) (K .typeAExitOneReturn)
        (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)).elim
  | .right oneFree =>
      -- `[97]`
      match typeAExitTwoDichotomy (data := spineData) oneFree
          (by simp [K_eq_iff, thetaFresh]) (by simp [K_eq_iff, twoFreeFresh]) with
      | .left thetaHistory =>
          -- `[98]`
          exact ((closeIncompatible thetaHistory (K .selection) (K .typeAExitTwoTheta)
            (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)).elim
      | .right twoFree =>
          -- `[99]`
          match typeAExitThreeDichotomy (data := spineData) twoFree
              (by simp [K_eq_iff, collisionFresh]) (by simp [K_eq_iff, threeFreeFresh]) with
          | .left collisionHistory =>
              -- `[100]`
              exact ((closeIncompatible collisionHistory (K .selection)
                (K .typeAExitThreeCollision)
                (by simp [K_eq_iff, closureFresh])).elimClosed (by infer_instance)).elim
          | .right threeFree =>
              -- `[101]`--`[109]`: exit `(4)` and the rest of the exit segment on
              -- the visible lane.
              exact selectedTypeAVisibleExitFour threeFree
                (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh]) (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh]) (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, entryFresh]) (by simp [K_eq_iff, descentFresh])
                (by simp [K_eq_iff, exitFourFresh]) (by simp [K_eq_iff, exitFourFreeFresh])
                (by simp [K_eq_iff, peeledFresh]) (by simp [K_eq_iff, dischargedFresh])
                (by simp [K_eq_iff, fiveFresh]) (by simp [K_eq_iff, fiveFreeFresh])
                (by simp [K_eq_iff, sixFresh]) (by simp [K_eq_iff, sixFreeFresh])
                (by simp [K_eq_iff, sixProperFresh]) (by simp [K_eq_iff, sixGlobalFresh])
                (by simp [K_eq_iff, sevenProducedFresh])
                (by simp [K_eq_iff, sevenFreeFresh]) (by simp [K_eq_iff, sevenHandoffFresh])
                (by simp [K_eq_iff, decoratedFresh])
                (by simp [K_eq_iff, cubicBaselineFresh]) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
                (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
                (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
                (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
                (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
                (by simp [K_eq_iff, closureFresh])

/-- **Nodes `[63]`, `[86]`--`[94]`: the Type A entry**, on the `[62]` Type A
residual of either spine arm (index-polymorphic, as `selectedNetChargeContinuation`).

`[86]` is `def:typeA-support`, namely `def:admissible` with `σ(X) = 0`.
At `[87]`, node `[27]` makes that selected piece `P13`-free; shortest internal
paths give `diam(X) ≤ 11`, and the subcubic breadth-first count gives
`|X| ≤ 6142`.  At `[88]`, the receiver routing `lem:typeA-receiver-loads`
and the threshold algebra
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
-- EG-NODE [88] raw thresholds H_0<=4, H_1<=8, H_2<=12
-- EG-NODE [89] some receiver has L(w)>=4q(w)?
-- EG-NODE [90] no: unsaturated L(w)<=4q(w)-1
-- EG-NODE [91] 3/7/11 charge bound
-- EG-NODE [92] unsaturated Type A charge closes
-- EG-NODE [93] some port has four visible receiver-entry returns?
-- EG-NODE [94] visible-first excess S_sil^exc(X)>=4D_A(X)
-- EG-NODE [86] Type A: sigma(X)=0, hence defp(X) < |X|/4
-- EG-NODE [87] selected Type A support: P13-free, diam(X)<=11, |X|<=6142
noncomputable def selectedTypeALowSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .selection) known]
    (boundedFresh : K .typeABoundedSupport ∉ known := by simp [K_eq_iff])
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (saturatedFresh : K .typeASaturatedReceiver ∉ known := by simp [K_eq_iff])
    (unsaturatedFresh : K .typeAUnsaturatedReceivers ∉ known := by simp [K_eq_iff])
    (dischargeFresh : K .typeAUnsaturatedDischarge ∉ known := by simp [K_eq_iff])
    (portFresh : K .typeAPortReturn ∉ known := by simp [K_eq_iff])
    (powerReturnFresh : K .portPowerReturn ∉ known := by simp [K_eq_iff])
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
    (cubicBaselineFresh : K .cubicBaseline ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known := by simp [K_eq_iff])
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (fanCapFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (decoratedExcludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (profileFresh : K .route8ResidualProfile ∉ known := by simp [K_eq_iff])
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by simp [K_eq_iff])
    (burdenFresh : K .route8BasinBurden ∉ known := by simp [K_eq_iff])
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by simp [K_eq_iff])
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known :=
      by simp [K_eq_iff])
    (coreFresh : K .route8CarrierCore ∉ known := by simp [K_eq_iff])
    (trueResidualFresh : K .route8TrueResidual ∉ known := by simp [K_eq_iff])
    (cutParityFresh : K .route8CarrierCutParity ∉ known := by simp [K_eq_iff])
    (smallFresh : K .route8SmallCoreEntry ∉ known := by simp [K_eq_iff])
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known := by simp [K_eq_iff])
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by simp [K_eq_iff])
    (censusFresh : K .route8Census ∉ known := by simp [K_eq_iff])
    (twoFresh : K .route8TwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known :=
      by simp [K_eq_iff])
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known :=
      by simp [K_eq_iff])
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known :=
      by simp [K_eq_iff])
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by
      simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    [FactKeys.Has (K .negativeSupport) known]
    (closureFresh : closed ∉ known := by simp [K_eq_iff]) :
    SelectedRouteEightBoundary selected := by
  -- `[87]`: the selected incoming Type A piece is P13-free, has diameter at
  -- most 11, and has at most 6142 vertices.
  let bounded :=
    (typeABoundedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, boundedFresh])
  -- `[88]`
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      bounded (by simp [K_eq_iff, routingFresh])
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
      -- `cor:port-power-return`, on the same saturated support and before `[93]`.
      let powerReturns :=
        (portPowerReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          ports (by simp [K_eq_iff, powerReturnFresh])
      -- `[93]`
      match typeAVisibleEntryDichotomy (data := spineData) powerReturns
          (by simp [K_eq_iff, visibleFresh]) (by simp [K_eq_iff, excessFresh]) with
      | .left visibleHistory =>
          -- `[95]`--`[107]`: the saturated exit chain on the visible arm.
          exact selectedTypeAVisibleExitChain visibleHistory
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, deficitFailsFresh]) (by simp [K_eq_iff, coreFresh])
            (by simp [K_eq_iff, trueResidualFresh])
            (by simp [K_eq_iff, cutParityFresh]) (by simp [K_eq_iff, smallFresh])
            (by simp [K_eq_iff, noSmallFresh]) (by simp [K_eq_iff, collapseFresh])
            (by simp [K_eq_iff, deletionWitnessesFresh])
            (by simp [K_eq_iff, privateBudgetFresh])
            (by simp [K_eq_iff, noTwoContradictionFresh])
            (by simp [K_eq_iff, terminalNoGoFresh])
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
            (by simp [K_eq_iff, cubicBaselineFresh]) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh])
            (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
            (by simp [K_eq_iff, noTwoFresh]) (by simp [K_eq_iff, trueEntryFresh])
            (by simp [K_eq_iff, unifiedNegativeFresh])
            (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
            (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
            (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
            (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
            (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
            (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
            (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
            (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
            (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
            (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
            (peelingFresh := by simp [K_eq_iff, peelingFresh])
            (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
            (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
            (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
            (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
            (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
            (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
            (decoratedExcludedFresh := by simp [K_eq_iff, decoratedExcludedFresh])
            (decoratedExclusionResidualFresh := by simp [K_eq_iff, decoratedExclusionResidualFresh])
            (decoratedExclusionMassFresh := by simp [K_eq_iff, decoratedExclusionMassFresh])
            (decoratedObstructionMassFresh := by simp [K_eq_iff, decoratedObstructionMassFresh])
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
            (by simp [K_eq_iff, cubicBaselineFresh]) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh]) (by simp [K_eq_iff, decoratedExcludedFresh]) (by simp [K_eq_iff, decoratedExclusionResidualFresh]) (by simp [K_eq_iff, decoratedExclusionMassFresh]) (by simp [K_eq_iff, decoratedObstructionMassFresh])
            (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
            (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
            (by simp [K_eq_iff, deficitFailsFresh])
            (by simp [K_eq_iff, coreFresh])
            (by simp [K_eq_iff, trueResidualFresh])
            (by simp [K_eq_iff, cutParityFresh])
            (by simp [K_eq_iff, smallFresh])
            (by simp [K_eq_iff, noSmallFresh])
            (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
                (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
                (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
                (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
                (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
                (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
                (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
                (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
                (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
                (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
                (peelingFresh := by simp [K_eq_iff, peelingFresh])
                (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
                (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
                (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
                (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
                (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
                (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
            (by simp [K_eq_iff, closureFresh])

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
-- EG-NODE [65] Type B assigned support: high-degree fan centers
-- EG-NODE [67] high-degree centers independent; fan neighbours cubic
-- EG-NODE [68] some center has d_G(h)>4?
-- EG-NODE [69] degree >4 local dichotomy: fan-compatible open pair or ports
-- EG-NODE [70] fan-safe graph, P13 certificate graph, certificate cap
-- EG-NODE [71] certificate labelling present?
-- EG-NODE [75] bridge fan-mass: fan-certificate centers and B2 failures charged
-- EG-NODE [78] degree-4 branch: d_G(h)=4
-- EG-NODE [79] degree-4 fan profile: center surplus 1, 0<=c<=4, D_B=c-7/4
-- EG-NODE [80] certificate labelling present?
-- EG-NODE [84] fan-mass route: certificate failures and B2 failures charged
noncomputable def selectedTypeBHighSurplusContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBHighSurplus) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .route8Rate) known]
    (routingFresh : K .typeAReceiverRouting ∉ known := by simp [K_eq_iff])
    (cubicFresh : K .cubicBaseline ∉ known := by simp [K_eq_iff])
    (assignedFresh : K .typeBAssignedSupport ∉ known := by simp [K_eq_iff])
    (fanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (heavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (degreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (localFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (compatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (capFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (markedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (residualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    -- `[72]`--`[85]` continue on this same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (triangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (fanClosedFresh : K .fanClosedPort ∉ known := by simp [K_eq_iff])
    (compatibleClosureFresh : K .compatiblePairFanClosure ∉ known := by simp [K_eq_iff])
    (fanClosedRoutingFresh : K .fanClosedPortTypeBRouting ∉ known := by simp [K_eq_iff])
    (compatibleRoutingFresh : K .compatiblePairTypeBRouting ∉ known := by simp [K_eq_iff])
    (shoulderCompletionFresh : K .triangularShoulderCompletion ∉ known := by simp [K_eq_iff])
    (portReturnFresh : K .triangularPortReturn ∉ known := by simp [K_eq_iff])
    (firstLandingFresh : K .triangularFirstLanding ∉ known := by simp [K_eq_iff])
    (crossShoulderFresh : K .triangularCrossShoulder ∉ known := by simp [K_eq_iff])
    (triangularRoutingFresh : K .triangularPortTypeBRouting ∉ known := by simp [K_eq_iff]) :
    SelectedRouteEightBoundary selected := by
  -- The common Part IX census reads the object-wide receiver routing of
  -- `[88]`.  Publish that paper fact on this literal Type B residual before
  -- adding the branch-specific fan support; no handoff carrier is needed.
  let routed :=
    (typeAReceiverRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) spineData).run
      history (by simp [K_eq_iff, routingFresh])
  let cubic :=
    (cubicBaselineRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      routed (by simp [K_eq_iff, cubicFresh])
  -- `[65]`: the ordinary Type B assigned support.
  let assigned :=
    (typeBAssignedSupportRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      cubic (by simp [K_eq_iff, assignedFresh, fanEntryFresh])
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
      -- `[69]`: publish `lem:same-center-open-port-compatibility`, then derive
      -- `cor:heavy-center-local-dichotomy` from that registered fact.
      let compatibleHistory :=
        (sameCenterOpenPortCompatibilityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          heavyHistory (by simp [K_eq_iff, compatibilityFresh])
      let localDichotomy :=
        (typeBFanLocalDichotomyRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          compatibleHistory (by simp [K_eq_iff, localFresh])
      let portRouted := selectedTypeBPortRoutingPrefix localDichotomy
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      -- `[70]`: `lem:fan-certificate`, the certificate-marked degree cap.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, capFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, markedFresh])
        (by simp [K_eq_iff, residualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh])
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])
  | .right degreeFourHistory =>
      -- `[78]`--`[79]`: every assigned fan centre has degree `δ + 1`; the
      -- degree-four fan profile (`cor:degree-four-local-activation`).
      let profile :=
        (typeBFanDegreeFourProfileRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          degreeFourHistory (by simp [K_eq_iff, degreeFourProfileFresh])
      let triangularCore :=
        (triangularFanCoreRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          profile (by simp [K_eq_iff, triangularCoreFresh])
      let completed :=
        (triangularShoulderCompletionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularCore (by simp [K_eq_iff, shoulderCompletionFresh])
      let returned :=
        (triangularPortReturnRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          completed (by simp [K_eq_iff, portReturnFresh])
      let firstLanded :=
        (triangularFirstLandingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          returned (by simp [K_eq_iff, firstLandingFresh])
      let crossShouldered :=
        (triangularCrossShoulderRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          firstLanded (by simp [K_eq_iff, crossShoulderFresh])
      let portRouted := selectedTypeBPortRoutingPrefix crossShouldered
        (by simp [K_eq_iff, fanClosedFresh])
        (by simp [K_eq_iff, compatibleClosureFresh])
        (by simp [K_eq_iff, fanClosedRoutingFresh])
        (by simp [K_eq_iff, compatibleRoutingFresh])
      let triangularRouted :=
        (triangularPortTypeBRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          portRouted (by simp [K_eq_iff, triangularRoutingFresh])
      -- `lem:fan-certificate` (the `[70]` cap, a fact of the object: every
      -- certificate-marked centre is capped by the label packing number), which
      -- `[82]`'s certificate-closed entries and the B1 budget read.
      let capped :=
        (fanCertificateCapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          triangularRouted (by simp [K_eq_iff, capFresh])
      exact selectedTypeBNearCubicCertificateAfterPortRouting capped
        (by simp [K_eq_iff, markedFresh])
        (by simp [K_eq_iff, residualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh])
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, unifiedNegativeFresh])
        (typeAExclusionFresh := by simp [K_eq_iff, typeAExclusionFresh])
        (typeBBridgeReductionFresh := by simp [K_eq_iff, typeBBridgeReductionFresh])
        (piecesClassifiedFresh := by simp [K_eq_iff, piecesClassifiedFresh])
        (sublinearLedgerFresh := by simp [K_eq_iff, sublinearLedgerFresh])
        (sublinearResidualFresh := by simp [K_eq_iff, sublinearResidualFresh])
        (unifiedDeficitFresh := by simp [K_eq_iff, unifiedDeficitFresh])
        (quotientFreeFresh := by simp [K_eq_iff, quotientFreeFresh])
        (quotientResidualFresh := by simp [K_eq_iff, quotientResidualFresh])
        (unifiedCensusFresh := by simp [K_eq_iff, unifiedCensusFresh])
        (unifiedTrueFresh := by simp [K_eq_iff, unifiedTrueFresh])
        (peelingFresh := by simp [K_eq_iff, peelingFresh])
        (stageFailedFresh := by simp [K_eq_iff, stageFailedFresh])
        (demandLedgerFresh := by simp [K_eq_iff, demandLedgerFresh])
        (demandAbsorptionFresh := by simp [K_eq_iff, demandAbsorptionFresh])
        (windowBlockersFresh := by simp [K_eq_iff, windowBlockersFresh])
        (demandResidualFresh := by simp [K_eq_iff, demandResidualFresh])
        (unifiedTerminalFresh := by simp [K_eq_iff, unifiedTerminalFresh])

/-- **Nodes `[170]`--`[172]`, `lem:scale-additivity`.**  On the trivial neutral
germ residual of `[169]` (`K .blockedClassMember`, `def:blocked-class`), decide
whether the conditional savings of the barrier states add at every fixed scale.
Independently of that decision, the yes fact retains two local consequences of
the same incoming blocked-class ledger: imposing the current surviving-state
test can only shrink a graph fibre, and the conditional state fibre has size at
most `F_{a,b} + 1`, where the extra state is exactly the absent-completion
marker.  These strengthen the retained ledger but do not replace the paper's
relative `F_{a,b}/W_{a,b}` test.

*Additive* (`[171]`): `lem:blocked-graphs-compress` encodes every member of
`𝓑(𝒫)` as its outside edges together with all barrier states, paying
`log₂ W_{a,b} − γ_{a,b}` bits per coordinate, so
`card 𝓑(𝒫) · W^N ≤ |𝒢_{n,m}| · F^N`.  `blockedCompressionRow` proves this by
the manuscript's finite prefix exposure directly from `K .blockedClassMember`
and the additive decision arm, then publishes the registered package-bit form
as `K .blockedCompressionBound` and its budget consequence as
`K .blockedCompressionCap`.
The density hypothesis is the
dense-packing residual `[159]` itself: by `def:window-realization-test` the
no-branch of `[158]` is `2^{c₁₃p₁₃log₂n} > |𝒢_{n,m}|`, which
`densePackingOverflowRow` publishes as `K .densePackingOverflow` from the
literal no-arm and `lem:skeleton-dominates`.  On that display
`blockedCompressionCloses` closes the two incompatible ledger facts, giving
`card 𝓑(𝒫) < 1` and contradicting
`G ∈ 𝓑(𝒫)`.  The complementary half of the same reading — the *joint* retained
code (window package with the remainder states and the exact curvature code)
overflowing the budget while the window package alone does not — remains node
`[53]`'s comparison in the hot/cold ledger and is not an arm of `[159]`.

*Not additive* (`[172]`): `lem:barrier-failure-overlap` supplies a minimal
same-scale barrier overlap obstruction with connected overlap support; the
uncrossing of `lem:window-system-realizability` (i)--(v) turns it into a
scale-spanning serial window system, `lem:serial-system-sumset` fills its
spectrum, and `lem:system-increment-arithmetic` closes it.  That uncrossing is
the next producer. -/
-- EG-NODE [170] conditional savings additive at every fixed scale?
-- EG-NODE [171] compression closure: |B(P)| < 1
-- EG-NODE [159] dense-packing residual: no-edge of [158]; 2^(c13 p13 log2 n) > |G_{n,m}|
noncomputable def selectedScaleAdditivityDichotomy
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .blockedClassMember) known]
    (additiveFresh : K .blockedScaleAdditive ∉ known := by simp [K_eq_iff])
    (overlapFresh : K .blockedBarrierOverlap ∉ known := by simp [K_eq_iff]) :
    Decision (K .blockedScaleAdditive) (K .blockedBarrierOverlap) history :=
  scaleAdditivityDichotomy (data := spineData) history additiveFresh overlapFresh

/-- Nodes `[166]` and `[169]`: consume the exact canonical-replacement swap,
publish the forced equality `Q = E`, and enter the blocked-class continuation
on that literal residual. -/
noncomputable def selectedCanonicalReplacementContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .coldCanonicalReplacementSwap) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .densePackingOverflow) known]
    (trivialFresh : K .coldCanonicalReplacementTrivial ∉ known := by
      simp [K_eq_iff])
    (blockedFresh : K .blockedClassMember ∉
        K .coldCanonicalReplacementTrivial :: known := by simp [K_eq_iff])
    (additiveFresh : K .blockedScaleAdditive ∉ known := by simp [K_eq_iff])
    (overlapFresh : K .blockedBarrierOverlap ∉ known := by simp [K_eq_iff])
    (boundFresh : K .blockedCompressionBound ∉ known := by simp [K_eq_iff])
    (capFresh : K .blockedCompressionCap ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff]) :
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedBarrierOverlap
      selected.object := by
  let trivial :=
    (canonicalReplacementTrivialRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, trivialFresh])
  let blocked :=
    (blockedClassRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      trivial (by simp [K_eq_iff, blockedFresh])
  match selectedScaleAdditivityDichotomy blocked
      (additiveFresh := by simp [K_eq_iff, additiveFresh])
      (overlapFresh := by simp [K_eq_iff, overlapFresh]) with
  | .left additiveHistory =>
      exact (blockedCompressionCloses (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        additiveHistory
        (by simp [K_eq_iff, boundFresh])
        (by simp [K_eq_iff, capFresh])
        (by simp [K_eq_iff, closureFresh])).elim
  | .right overlapHistory =>
      exact (overlapHistory.get (K .blockedBarrierOverlap)).down
/-- **Nodes `[174]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ
residual**, index-polymorphic over any residual carrying the hot/cold ledger of
the fixed packing and the actual `[153]` first-failure state and extraction.
Its cold windows' selected branch-excess corridors were charged as the
germ-extraction loss; the charge is restored here at `[175]`: a selected corridor with a
subcubic first-failure support is a genuine (F5) germ, routed exactly as
`[154]`--`[157]` and the `[163]` symmetry split (`[176]`); otherwise every
  selected corridor meets a heavy centre and the half-edges are decorated
  handoff fan data entering Type B at `[65]` (`[177]`).  The function then runs
  the paper's common `[67]`--`[85]` continuation and returns its literal
  ExactLedger boundary.  The genuine-germ arm closes and is eliminated into
  the same result type; no `[64]`-specific quantitative tail is imported.
Entered only from the exact collision failure (`[173]`). -/
-- EG-NODE [153] linear first-failure extraction? N_germ>=9C/D_cold-o(n)
-- EG-NODE [154] bounded germ case?
-- EG-NODE [155] G1: dyadic cycle
-- EG-NODE [156] G2: target defect, exit (4), or handoff
-- EG-NODE [157] G3 or same-interface table: compression
-- EG-NODE [163] neutral equal-length terminal germ: second strand genuine?
-- EG-NODE [165] canonical replacement E!=Q: swap Q->E gives same-size counterexample
-- EG-NODE [166] refined lexicographic minimality: Q=E
-- EG-NODE [167] symmetric strand pair: finite two-strand check on closing lengths
-- EG-NODE [169] trivial neutral germ residual: dense packing, every corridor terminal
-- EG-NODE [175] selected corridor meets a high-degree vertex?
-- EG-NODE [176] genuine (F5) germ closed by [154]-[157], [165]-[168]
-- EG-NODE [177] decorated handoff fan data at the heavy centre z
private noncomputable abbrev AbsorbedPrerequisiteKnown (known : FactKeys EGInput.{u}) :
    FactKeys EGInput.{u} :=
  coldGermCandidatesRow.manifest.Produces ++
    (coldGermExtractionRow.manifest.Produces ++
      (coldFirstFailureRoutingRow.manifest.Produces ++
        (coldHandoffTransferRow.manifest.Produces ++
          (coldFailureHandoffRow.manifest.Produces ++
            (coldFailureCompressionRow.manifest.Produces ++
              (coldFailureDefectRow.manifest.Produces ++
                (coldFailureCycleRow.manifest.Produces ++
                  (coldFirstFailureOccurrenceRow.manifest.Produces ++
                      (denseColdCorridorsTerminalRow.manifest.Produces ++
                        (coldCorridorStateRow.manifest.Produces ++
                          (coldDeclaredHandoffLedgerRow.manifest.Produces ++
                            (coldReturnCorridorRow.manifest.Produces ++
                              (bridgelessRow.manifest.Produces ++ known)))))))))))))

/-- The enclosing node-`[174]` assembly publishes the corridor and extraction
facts which node `[175]` receives.  These are the canonical registered owners
from node `[153]`; `[175]` never reconstructs them and only queries their
ExactLedger entries. -/
noncomputable def selectedAbsorbedGermPrerequisites
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (bridgelessFresh : K .bridgeless ∉ known)
    (returnFresh : K .coldReturnCorridors ∉ known)
    (declaredFresh : K .coldDeclaredHandoffLedger ∉ known)
    (stateFresh : K .coldCorridorState ∉ known)
    (terminalFresh : K .denseColdCorridorsTerminal ∉ known)
    (occurrenceFresh : K .coldFirstFailureOccurrence ∉ known)
    (routingFresh : K .coldFailureRouting ∉ known)
    (failureCycleFresh : K .coldFailureCycle ∉ known)
    (failureDefectFresh : K .coldFailureDefect ∉ known)
    (failureDefectRouteFresh : K .coldFailureDefectRoute ∉ known)
    (failureCompressionFresh : K .coldFailureCompression ∉ known)
    (failureHandoffFresh : K .coldFailureHandoff ∉ known)
    (handoffTransferFresh : K .coldHandoffTransfer ∉ known)
    (exchangeFresh : K .coldExchangeBound ∉ known)
    (extractionFresh : K .coldGermExtraction ∉ known)
    (candidatesFresh : K .coldGermCandidates ∉ known) :
    ExactLedger EGInput.{u} selected (AbsorbedPrerequisiteKnown known) := by
  let bridgeless :=
    (bridgelessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [K_eq_iff, bridgelessFresh])
  let returned :=
    (coldReturnCorridorRow (data := spineData)).run bridgeless
      (by simp [K_eq_iff, returnFresh])
  let declared :=
    (coldDeclaredHandoffLedgerRow (data := spineData)).run returned
      (by simp [K_eq_iff, declaredFresh])
  let state :=
    (coldCorridorStateRow (data := spineData)).run declared
      (by simp [K_eq_iff, stateFresh])
  let terminal :=
    (denseColdCorridorsTerminalRow (data := spineData)).run state
      (by simp [K_eq_iff, terminalFresh])
  let occurrence :=
    (coldFirstFailureOccurrenceRow (data := spineData)).run terminal
      (by simp [K_eq_iff, occurrenceFresh])
  let failureCycle :=
    (coldFailureCycleRow (data := spineData)).run occurrence
      (by simp [K_eq_iff, failureCycleFresh])
  let failureDefect :=
    (coldFailureDefectRow (data := spineData)).run failureCycle
      (by simp [K_eq_iff, failureDefectFresh, failureDefectRouteFresh])
  let failureCompression :=
    (coldFailureCompressionRow (data := spineData)).run failureDefect
      (by simp [K_eq_iff, failureCompressionFresh])
  let failureHandoff :=
    (coldFailureHandoffRow (data := spineData)).run failureCompression
      (by simp [K_eq_iff, failureHandoffFresh])
  let handoffTransfer :=
    (coldHandoffTransferRow (data := spineData)).run failureHandoff
      (by simp [K_eq_iff, handoffTransferFresh])
  let routed :=
    (coldFirstFailureRoutingRow (data := spineData)).run handoffTransfer
      (by simp [K_eq_iff, stateFresh, occurrenceFresh, routingFresh, failureCycleFresh,
        failureDefectFresh, failureDefectRouteFresh, failureCompressionFresh,
        failureHandoffFresh, handoffTransferFresh])
  let extracted :=
    (coldGermExtractionRow (data := spineData)).run routed
      (by simp [K_eq_iff, exchangeFresh, extractionFresh])
  exact (coldGermCandidatesRow (data := spineData)).run extracted
    (by simp [K_eq_iff, candidatesFresh])

abbrev SelectedAbsorbedGermBoundary (selected : EGInput.{u}) :=
  SelectedExtractedTypeBRoute8Boundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldBranchClosed selected.object ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object

noncomputable def selectedAbsorbedGermResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermExtraction) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    (absorbedSplitFresh : K .absorbedGermSplit ∉ known := by simp [K_eq_iff])
    (absorbedPositiveFresh : K .coldPositiveGerm ∉ known := by simp [K_eq_iff])
    (absorbedFamilyPositiveFresh : K .coldGermFamilyPositive ∉ known := by
      simp [K_eq_iff])
    (absorbedFanFresh : K .absorbedGermFanData ∉ known := by simp [K_eq_iff])
    (absorbedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (absorbedNormalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (absorbedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (absorbedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (absorbedCompatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (absorbedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (absorbedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (absorbedTriangularFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (absorbedCapFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (absorbedMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (absorbedResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (absorbedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by
      simp [K_eq_iff])
    (absorbedCycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (absorbedFreeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (absorbedChoiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (absorbedObstructionFresh : K .typeBOverlapObstruction ∉ known := by
      simp [K_eq_iff])
    (absorbedHybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (absorbedLedgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (absorbedExcludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (absorbedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by
      simp [K_eq_iff])
    (absorbedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by
      simp [K_eq_iff])
    (absorbedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by
      simp [K_eq_iff])
    (absorbedRealizedFresh : K .coldGermRealized ∉ known := by simp [K_eq_iff])
    (absorbedDistinguishedFresh : K .coldGermDistinguished ∉ known := by simp [K_eq_iff])
    (absorbedSilentFresh : K .coldGermSilent ∉ known := by simp [K_eq_iff])
    (absorbedRoutedFresh : K .coldGermRouted ∉ known := by simp [K_eq_iff])
    (absorbedTableFresh : K .coldSameInterfaceTable ∉ known := by simp [K_eq_iff])
    (absorbedClosedFresh : K .coldBranchClosed ∉ known := by simp [K_eq_iff])
    (absorbedNeutralFresh : K .coldNeutralEqualLengthTerminal ∉ known := by
      simp [K_eq_iff])
    (absorbedCanonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known := by
      simp [K_eq_iff])
    (absorbedGenuineFresh : K .coldGenuineSecondStrand ∉ known := by
      simp [K_eq_iff])
    (absorbedReplacementSwapFresh : K .coldCanonicalReplacementSwap ∉ known := by
      simp [K_eq_iff])
    (absorbedReplacementTrivialFresh : K .coldCanonicalReplacementTrivial ∉ known := by
      simp [K_eq_iff])
    (absorbedTwoStrandSurvivorFresh : K .coldTwoStrandSurvivor ∉ known := by
      simp [K_eq_iff])
    (absorbedWindowStubFresh : K .coldWindowStubStructure ∉ known := by
      simp [K_eq_iff])
    (absorbedPairExcludedFresh : K .coldSymmetricPairExcluded ∉ known := by
      simp [K_eq_iff])
    (absorbedTerminalFresh : closed ∉ known := by simp [K_eq_iff])
    (absorbedBridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (absorbedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by
      simp [K_eq_iff])
    (absorbedCubicFresh : K .cubicBaseline ∉ known := by simp [K_eq_iff])
    (absorbedExtractedFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff]) :
    SelectedAbsorbedGermBoundary selected := by
  let _absorbed := (history.get (K .absorbedConfigurationResidual)).down
  let _candidates := (history.get (K .coldGermCandidates)).down
  -- `[175]`, `lem:absorbed-germ-fan-data`: the per-half-edge dichotomy — every
  -- selected corridor's first-failure support is subcubic (a charged candidate
  -- germ, `[176]`) or meets a heavy centre whose neighbours sit at the threshold
  -- by node `[10]` (`[177]`).
  let split :=
    (absorbedGermSplitRow (data := spineData)).run history
      (by simp [K_eq_iff, absorbedSplitFresh])
  -- The exhaustive object-level reading of `[175]`: is the subcubic occurrence
  -- class nonempty?  This decision records only that branch predicate.
  match absorbedGermDichotomy (data := spineData) split
      (by simp [K_eq_iff, absorbedPositiveFresh])
      (by simp [K_eq_iff, absorbedFanFresh]) with
  | .left positiveHistory =>
      -- `[176]`: a genuine (F5) germ family; routed exactly as `[154]`--`[157]`,
      -- then the neutral-germ symmetry split of `[163]`.  The candidate family
      -- is obtained by running its registered node-`[153]` owner on this exact
      -- ledger; `[175]` does not reconstruct its count or overlap proof.
      let positiveFamily :=
        (absorbedGermFamilyPositiveRow (data := spineData)).run positiveHistory
          (by simp [K_eq_iff, absorbedFamilyPositiveFresh])
      let neutralConfiguration :=
        (neutralEqualLengthTerminalRow (data := spineData)).run positiveFamily
          (by simp [K_eq_iff, absorbedNeutralFresh])
      let trichotomy :=
        (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
          (by simp [K_eq_iff, absorbedRealizedFresh, absorbedDistinguishedFresh,
            absorbedSilentFresh, absorbedRoutedFresh])
      let table :=
        (coldSameInterfaceTableRow (data := spineData)).run trichotomy
          (by simp [K_eq_iff, absorbedTableFresh])
      let closed :=
        (coldBranchClosedRow (data := spineData)).run table
          (by simp [K_eq_iff, absorbedClosedFresh])
      match neutralGermSymmetryDichotomy (data := spineData) closed
          (by simp [K_eq_iff, absorbedCanonicalFresh])
          (by simp [K_eq_iff, absorbedGenuineFresh]) with
      | .left canonicalHistory =>
          -- `[165]`--`[166]`: the non-realized representative is exchanged in
          -- the retained context, and refined minimality publishes `Q = E`.
          -- This is the local manuscript consumer only; the dense-only
          -- blocked-class continuation `[169]` is not entered here.
          let swapped :=
            (canonicalReplacementSwapRow (data := spineData)).run
              canonicalHistory
              (by simp [K_eq_iff, absorbedReplacementSwapFresh])
          let trivial :=
            (canonicalReplacementTrivialRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              swapped
              (by simp [K_eq_iff, absorbedReplacementTrivialFresh])
          -- `[176]` has now consumed every cited cold/symmetry fact.  Because
          -- `[175]` is per incidence, append `[177]`'s aggregate package and
          -- fan entry on this same ledger so a mixed family retains `Q = E`
          -- together with the Type-B charge of its complement.
          let fanData :=
            (absorbedGermFanDataRow (data := spineData)).run trivial
              (by simp [K_eq_iff, absorbedFanFresh])
          let fanEntry :=
            (absorbedGermFanEnvelopeRow (data := spineData)).run fanData
              (by simp [K_eq_iff, absorbedFanEntryFresh])
          exact Or.inl (selectedAbsorbedFanChargeContinuation fanEntry
            (by simp [K_eq_iff, absorbedNormalFormFresh])
            (by simp [K_eq_iff, absorbedHeavyFresh])
            (by simp [K_eq_iff, absorbedDegreeFourFresh])
            (by simp [K_eq_iff, absorbedCompatibilityFresh])
            (by simp [K_eq_iff, absorbedLocalFresh])
            (by simp [K_eq_iff, absorbedProfileFresh])
            (by simp [K_eq_iff, absorbedTriangularFresh])
            (by simp [K_eq_iff, absorbedCapFresh])
            (by simp [K_eq_iff, absorbedMarkedFresh])
            (by simp [K_eq_iff, absorbedResidualFresh])
            (by simp [K_eq_iff, absorbedCertificateMassFresh])
            (by simp [K_eq_iff, absorbedCycleFresh])
            (by simp [K_eq_iff, absorbedFreeFresh])
            (by simp [K_eq_iff, absorbedChoiceFresh])
            (by simp [K_eq_iff, absorbedObstructionFresh])
            (by simp [K_eq_iff, absorbedHybridFresh])
            (by simp [K_eq_iff, absorbedLedgerFresh])
            (by simp [K_eq_iff, absorbedExcludedFresh])
            (by simp [K_eq_iff, absorbedExclusionResidualFresh])
            (by simp [K_eq_iff, absorbedExclusionMassFresh])
            (by simp [K_eq_iff, absorbedObstructionMassFresh])
            (by simp [K_eq_iff, absorbedBridgeMassFresh])
            (by simp [K_eq_iff, absorbedBridgeSublinearFresh])
            (by simp [K_eq_iff, absorbedCubicFresh])
            (by simp [K_eq_iff, absorbedExtractedFresh]))
      | .right genuineHistory =>
          -- `[167]`--`[168]`: the graph-realized second strand either gives
          -- one of the two prescribed dyadic cycles inside its owner or lands
          -- in the finite survivor list, where the retained interior stub is
          -- incompatible with the two endpoint attachments.
          let survivor :=
            (twoStrandSurvivorRow (data := spineData)).run genuineHistory
              (by simp [K_eq_iff, absorbedTwoStrandSurvivorFresh])
          let stubbed :=
            (coldWindowStubStructureRow (data := spineData)).run survivor
              (by simp [K_eq_iff, absorbedWindowStubFresh])
          let impossible :=
            (symmetricPairEndpointExclusionRow (data := spineData)).runAndCloseIncompatible
              stubbed (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded)
              (by simp [K_eq_iff, absorbedPairExcludedFresh])
              (by simp [K_eq_iff, absorbedTerminalFresh])
          exact (impossible.elimClosed (by infer_instance)).elim
  | .right absorbedHistory =>
      -- `[177]`, `lem:absorbed-germ-fan-data` (ii): at every heavy centre of a
      -- selected corridor, the corridor's two incidences and tails are decorated
      -- handoff fan data (`def:decorated-fan-envelope`,
      -- `lem:typeA-high-degree-handoff`), published on the literal residual.
      let fanEntry :=
        (absorbedGermFanEnvelopeRow (data := spineData)).run absorbedHistory
          (by simp [K_eq_iff, absorbedFanEntryFresh])
      -- This is exactly the drawn `[177] → [65]` edge, followed by the common
      -- registered charge tail.  On this no-candidate arm the complement is
      -- the whole selected family.
      exact Or.inl (selectedAbsorbedFanChargeContinuation fanEntry
        (by simp [K_eq_iff, absorbedNormalFormFresh])
        (by simp [K_eq_iff, absorbedHeavyFresh])
        (by simp [K_eq_iff, absorbedDegreeFourFresh])
        (by simp [K_eq_iff, absorbedCompatibilityFresh])
        (by simp [K_eq_iff, absorbedLocalFresh])
        (by simp [K_eq_iff, absorbedProfileFresh])
        (by simp [K_eq_iff, absorbedTriangularFresh])
        (by simp [K_eq_iff, absorbedCapFresh])
        (by simp [K_eq_iff, absorbedMarkedFresh])
        (by simp [K_eq_iff, absorbedResidualFresh])
        (by simp [K_eq_iff, absorbedCertificateMassFresh])
        (by simp [K_eq_iff, absorbedCycleFresh])
        (by simp [K_eq_iff, absorbedFreeFresh])
        (by simp [K_eq_iff, absorbedChoiceFresh])
        (by simp [K_eq_iff, absorbedObstructionFresh])
        (by simp [K_eq_iff, absorbedHybridFresh])
        (by simp [K_eq_iff, absorbedLedgerFresh])
        (by simp [K_eq_iff, absorbedExcludedFresh])
        (by simp [K_eq_iff, absorbedExclusionResidualFresh])
        (by simp [K_eq_iff, absorbedExclusionMassFresh])
        (by simp [K_eq_iff, absorbedObstructionMassFresh])
        (by simp [K_eq_iff, absorbedBridgeMassFresh])
        (by simp [K_eq_iff, absorbedBridgeSublinearFresh])
        (by simp [K_eq_iff, absorbedCubicFresh])
        (by simp [K_eq_iff, absorbedExtractedFresh]))

/-- The exact complement of the private-carrier rate is retained as its own
residual.  The manuscript does not route this fact to nodes `[174]`--`[177]`;
those nodes are entered only by `K .exactCollisionFails`. -/
noncomputable def selectedRouteEightRateFailure
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8RateFails) known] :
    ExactLedger EGInput.{u} selected known := by
  let _rateFailure := (history.get (K .route8RateFails)).down
  exact history

/-- The only live conclusions of the net-charge continuation are the literal
Route-8 residuals or the literal absorbed-germ residuals published by their
own ledger owners. -/
abbrev SelectedNetChargeBoundary (selected : EGInput.{u}) :=
  SelectedRouteEightBoundary selected ∨ SelectedAbsorbedGermBoundary selected


/-- **Nodes `[57]`--`[64]`: the large-budget net-charge split**, on the `[56]`
residual of either spine arm.  `[57]` enters the asymptotic order regime and
reads the large-budget net cap; `[58]` localizes the charge; `[59]` splits on the
sign; the nonnegative arm is the `[60]` net-cap contradiction (cap gives
`N₀(R) < 0`, the sibling gives `N₀(R) ≥ 0`); the negative arm selects a connected
negative support `[61]` and `[62]` routes it to Type A `[63]` or Type B `[64]`.
The small-order complement `[57]`, and the Type A / Type B continuations, are the
next loud producers.  It is index-polymorphic over the arm's ledger, so both the
density-cap and route-8 arms use the same definition. -/
-- EG-NODE [57] large-budget net cap
-- EG-NODE [58] net charge N_0
-- EG-NODE [59] N_0(R)>=0?
-- EG-NODE [60] net-cap contradiction
-- EG-NODE [61] choose connected N_0(X)<0
-- EG-NODE [62] high-degree surplus?
-- EG-NODE [63] Type A continued in Part VIII
-- EG-NODE [64] Type B continued in Part VI
-- EG-NODE [173] exact collision test holds?
-- EG-NODE [174] absorbed-germ residual: the exact collision fails, corridors charged
-- EG-NODE [86] Type A: sigma(X)=0, hence defp(X) < |X|/4
noncomputable def selectedNetChargeContinuation
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8Rate) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    (capFresh : K .netChargeCap ∉ known := by simp [K_eq_iff])
    -- `[173]`--`[177]`, the exact collision test and the absorbed-germ residual.
    (failsFresh : K .exactCollisionFails ∉ known := by simp [K_eq_iff])
    (absorbedResidualFresh : K .absorbedConfigurationResidual ∉ known := by simp [K_eq_iff])
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (absorbedSplitFresh : K .absorbedGermSplit ∉ known := by simp [K_eq_iff])
    (absorbedBridgelessFresh : K .bridgeless ∉ known := by simp [K_eq_iff])
    (absorbedReturnFresh : K .coldReturnCorridors ∉ known := by simp [K_eq_iff])
    (absorbedDeclaredFresh : K .coldDeclaredHandoffLedger ∉ known := by simp [K_eq_iff])
    (absorbedStateFresh : K .coldCorridorState ∉ known := by simp [K_eq_iff])
    (absorbedTerminalFresh : K .denseColdCorridorsTerminal ∉ known := by
      simp [K_eq_iff])
    (absorbedOccurrenceFresh : K .coldFirstFailureOccurrence ∉ known := by simp [K_eq_iff])
    (absorbedRoutingFresh : K .coldFailureRouting ∉ known := by simp [K_eq_iff])
    (absorbedFailureCycleFresh : K .coldFailureCycle ∉ known := by simp [K_eq_iff])
    (absorbedFailureDefectFresh : K .coldFailureDefect ∉ known := by simp [K_eq_iff])
    (absorbedFailureDefectRouteFresh : K .coldFailureDefectRoute ∉ known := by
      simp [K_eq_iff])
    (absorbedFailureCompressionFresh : K .coldFailureCompression ∉ known := by
      simp [K_eq_iff])
    (absorbedFailureHandoffFresh : K .coldFailureHandoff ∉ known := by simp [K_eq_iff])
    (absorbedHandoffTransferFresh : K .coldHandoffTransfer ∉ known := by
      simp [K_eq_iff])
    (absorbedExchangeFresh : K .coldExchangeBound ∉ known := by simp [K_eq_iff])
    (absorbedExtractionFresh : K .coldGermExtraction ∉ known := by simp [K_eq_iff])
    (absorbedCandidatesFresh : K .coldGermCandidates ∉ known := by simp [K_eq_iff])
    (absorbedPositiveFresh : K .coldPositiveGerm ∉ known := by simp [K_eq_iff])
    (absorbedFamilyPositiveFresh : K .coldGermFamilyPositive ∉ known := by
      simp [K_eq_iff])
    (absorbedFanFresh : K .absorbedGermFanData ∉ known := by simp [K_eq_iff])
    (absorbedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (absorbedRealizedFresh : K .coldGermRealized ∉ known := by simp [K_eq_iff])
    (absorbedDistinguishedFresh : K .coldGermDistinguished ∉ known := by simp [K_eq_iff])
    (absorbedSilentFresh : K .coldGermSilent ∉ known := by simp [K_eq_iff])
    (absorbedRoutedFresh : K .coldGermRouted ∉ known := by simp [K_eq_iff])
    (absorbedTableFresh : K .coldSameInterfaceTable ∉ known := by simp [K_eq_iff])
    (absorbedClosedFresh : K .coldBranchClosed ∉ known := by simp [K_eq_iff])
    (absorbedNeutralFresh : K .coldNeutralEqualLengthTerminal ∉ known := by
      simp [K_eq_iff])
    (absorbedCanonicalFresh : K .coldCanonicalNeutralConfiguration ∉ known := by
      simp [K_eq_iff])
    (absorbedGenuineFresh : K .coldGenuineSecondStrand ∉ known := by
      simp [K_eq_iff])
    (absorbedReplacementSwapFresh : K .coldCanonicalReplacementSwap ∉ known := by
      simp [K_eq_iff])
    (absorbedReplacementTrivialFresh : K .coldCanonicalReplacementTrivial ∉ known := by
      simp [K_eq_iff])
    (absorbedTwoStrandSurvivorFresh : K .coldTwoStrandSurvivor ∉ known := by
      simp [K_eq_iff])
    (absorbedWindowStubFresh : K .coldWindowStubStructure ∉ known := by
      simp [K_eq_iff])
    (absorbedPairExcludedFresh : K .coldSymmetricPairExcluded ∉ known := by
      simp [K_eq_iff])
    (locFresh : K .netChargeLocalization ∉ known := by simp [K_eq_iff])
    (nonNegFresh : K .netChargeNonNegative ∉ known := by simp [K_eq_iff])
    (negFresh : K .netChargeNegative ∉ known := by simp [K_eq_iff])
    (supportFresh : K .negativeSupport ∉ known := by simp [K_eq_iff])
    (typeAFresh : K .typeALowSurplus ∉ known := by simp [K_eq_iff])
    (typeBFresh : K .typeBHighSurplus ∉ known := by simp [K_eq_iff])
    -- Type A `[63]`, `[86]`--`[94]` freshness on the same ledger.
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .remainderRelabelingEntropy) known]
    [FactKeys.Has (K .selection) known]
    (boundedFresh : K .typeABoundedSupport ∉ known := by simp [K_eq_iff])
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
    (typeBFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (normalFormFresh : K .highCentreNormalForm ∉ known := by simp [K_eq_iff])
    (fanHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (fanDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (fanLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (fanCompatibilityFresh : K .sameCenterOpenPortCompatibility ∉ known := by
      simp [K_eq_iff])
    (fanCapFresh : K .fanCertificateCap ∉ known := by simp [K_eq_iff])
    (decoratedMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (decoratedResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    (decoratedCertificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (decoratedCycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (decoratedFreeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (decoratedFanEntryFresh : K .typeBFanEntry ∉ known := by simp [K_eq_iff])
    (decoratedB2ChoiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (decoratedB2ObstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (decoratedHybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (decoratedLedgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (decoratedBridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (decoratedBridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (decoratedExcludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (decoratedExclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (decoratedExclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (decoratedObstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (decoratedClosureFresh : closed ∉ known := by simp [K_eq_iff])
    (fanMarkedFresh : K .fanCertificateMarked ∉ known := by simp [K_eq_iff])
    (fanResidualFresh : K .fanCertificateResidual ∉ known := by simp [K_eq_iff])
    -- Type B `[72]`--`[85]` keys on the same exact ledger.
    [FactKeys.Has (K .uncompressible) known]
    (cycleFresh : K .typeBDirectCycle ∉ known := by simp [K_eq_iff])
    (freeFresh : K .typeBDirectCycleFree ∉ known := by simp [K_eq_iff])
    (choiceFresh : K .typeBB2Choice ∉ known := by simp [K_eq_iff])
    (obstructionFresh : K .typeBOverlapObstruction ∉ known := by simp [K_eq_iff])
    (hybridFresh : K .typeBHybridEntry ∉ known := by simp [K_eq_iff])
    (ledgerFresh : K .typeBDisjointLedger ∉ known := by simp [K_eq_iff])
    (bridgeMassFresh : K .typeBBridgeMass ∉ known := by simp [K_eq_iff])
    (bridgeSublinearFresh : K .typeBBridgeSublinear ∉ known := by simp [K_eq_iff])
    (excludedFresh : K .typeBExcluded ∉ known := by simp [K_eq_iff])
    (exclusionResidualFresh : K .typeBExclusionResidual ∉ known := by simp [K_eq_iff])
    (exclusionMassFresh : K .typeBExclusionResidualMass ∉ known := by simp [K_eq_iff])
    (obstructionMassFresh : K .typeBOverlapObstructionMass ∉ known := by simp [K_eq_iff])
    (certificateMassFresh : K .fanCertificateResidualMass ∉ known := by simp [K_eq_iff])
    (degreeFourProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (triangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    -- `[108]` decorated handoff, `[110]`--`[116]` route 8, `[76]`/`[85]` → `[123]`.
    (decoratedFresh : K .typeBDecoratedAssignedSupport ∉ known := by simp [K_eq_iff])
    (cubicBaselineFresh : K .cubicBaseline ∉ known := by simp [K_eq_iff])
    (decoratedHeavyFresh : K .typeBFanHeavyCentre ∉ known := by simp [K_eq_iff])
    (decoratedDegreeFourFresh : K .typeBFanDegreeFourCentres ∉ known := by simp [K_eq_iff])
    (decoratedLocalFresh : K .typeBFanLocalDichotomy ∉ known := by simp [K_eq_iff])
    (decoratedCompatibilityFresh :
      K .sameCenterOpenPortCompatibility ∉ known := by simp [K_eq_iff])
    (decoratedProfileFresh : K .typeBFanDegreeFourProfile ∉ known := by simp [K_eq_iff])
    (decoratedTriangularCoreFresh : K .triangularFanCore ∉ known := by simp [K_eq_iff])
    (profileFresh : K .route8ResidualProfile ∉ known := by simp [K_eq_iff])
    (squeezeFresh : K .route8GlobalSqueeze ∉ known := by simp [K_eq_iff])
    (burdenFresh : K .route8BasinBurden ∉ known := by simp [K_eq_iff])
    (deficitFresh : K .route8LargeBudgetDeficit ∉ known := by simp [K_eq_iff])
    (deficitFailsFresh : K .route8LargeBudgetDeficitFails ∉ known :=
      by simp [K_eq_iff])
    (coreFresh : K .route8CarrierCore ∉ known := by simp [K_eq_iff])
    (trueResidualFresh : K .route8TrueResidual ∉ known := by simp [K_eq_iff])
    (cutParityFresh : K .route8CarrierCutParity ∉ known := by simp [K_eq_iff])
    (smallFresh : K .route8SmallCoreEntry ∉ known := by simp [K_eq_iff])
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known := by simp [K_eq_iff])
    (collapseFresh : K .route8SmallCoreCollapse ∉ known := by simp [K_eq_iff])
    (censusFresh : K .route8Census ∉ known := by simp [K_eq_iff])
    (twoFresh : K .route8TwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (noTwoFresh : K .route8NoTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (trueEntryFresh : K .route8TrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (deletionWitnessesFresh : K .route8CarrierDeletionWitnesses ∉ known :=
      by simp [K_eq_iff])
    (privateBudgetFresh : K .route8PrivateCarrierBudget ∉ known :=
      by simp [K_eq_iff])
    (noTwoContradictionFresh : K .route8NoTwoCarrierContradiction ∉ known :=
      by simp [K_eq_iff])
    (terminalNoGoFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff])
    (unifiedNegativeFresh : K .route8UnifiedNegative ∉ known := by simp [K_eq_iff])
    (typeAExclusionFresh : K .typeAExclusion ∉ known := by simp [K_eq_iff])
    (typeBBridgeReductionFresh : K .typeBBridgeReduction ∉ known := by
      simp [K_eq_iff])
    (piecesClassifiedFresh : K .route8PiecesClassified ∉ known := by simp [K_eq_iff])
    (sublinearLedgerFresh : K .typeBSublinearLedger ∉ known := by simp [K_eq_iff])
    (sublinearResidualFresh : K .typeBSublinearResidual ∉ known := by simp [K_eq_iff])
    (unifiedDeficitFresh : K .route8UnifiedDeficit ∉ known := by simp [K_eq_iff])
    (quotientFreeFresh : K .route8QuotientFree ∉ known := by simp [K_eq_iff])
    (quotientResidualFresh : K .route8QuotientResidual ∉ known := by simp [K_eq_iff])
    (unifiedCensusFresh : K .route8UnifiedEntryCensus ∉ known := by simp [K_eq_iff])
    (extractedEntryCensusFresh : K .route8ExtractedEntryCensus ∉ known := by
      simp [K_eq_iff])
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by simp [K_eq_iff])
    (peelingFresh : K .route8PeelingDescent ∉ known := by simp [K_eq_iff])
    (stageFailedFresh : K .route8StageRateFailed ∉ known := by simp [K_eq_iff])
    (demandLedgerFresh : K .route8DemandLedger ∉ known := by simp [K_eq_iff])
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known := by simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by simp [K_eq_iff])
    (unifiedTerminalFresh : K .route8TerminalNoGo ∉ known := by simp [K_eq_iff]) :
    SelectedNetChargeBoundary selected := by
  -- `[57]` = `[173]`, `lem:exact-collision-test`: node `[56]`'s collision decided
  -- exactly on the current object (`K .netChargeCap`), with no condition on `n`.
  match exactCollisionDichotomy (data := spineData) history capFresh failsFresh with
  | .right failsHistory =>
      -- `[174]`, `lem:exact-collision-test`: the failed collision rearranges to
      -- the cold-window lower bound `n + s·σ_R ≤ A·(|𝒫_hot| + |𝒫_cold|) + s·σ_W`.
      let absorbed :=
        (absorbedConfigurationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          failsHistory (by simp [K_eq_iff, absorbedResidualFresh])
      let prepared := selectedAbsorbedGermPrerequisites absorbed
        (by simp [K_eq_iff, absorbedBridgelessFresh])
        (by simp [K_eq_iff, absorbedReturnFresh])
        (by simp [K_eq_iff, absorbedDeclaredFresh])
        (by simp [K_eq_iff, absorbedStateFresh])
        (by simp [K_eq_iff, absorbedTerminalFresh])
        (by simp [K_eq_iff, absorbedOccurrenceFresh])
        (by simp [K_eq_iff, absorbedRoutingFresh])
        (by simp [K_eq_iff, absorbedFailureCycleFresh])
        (by simp [K_eq_iff, absorbedFailureDefectFresh])
        (by simp [K_eq_iff, absorbedFailureDefectRouteFresh])
        (by simp [K_eq_iff, absorbedFailureCompressionFresh])
        (by simp [K_eq_iff, absorbedFailureHandoffFresh])
        (by simp [K_eq_iff, absorbedHandoffTransferFresh])
        (by simp [K_eq_iff, absorbedExchangeFresh])
        (by simp [K_eq_iff, absorbedExtractionFresh])
        (by simp [K_eq_iff, absorbedCandidatesFresh])
      -- `[175]`--`[177]`, `lem:absorbed-germ-fan-data`: the absorbed-germ
      -- residual (`selectedAbsorbedGermResidual`).
      exact Or.inr (selectedAbsorbedGermResidual prepared
        (by simp [K_eq_iff, absorbedSplitFresh])
        (absorbedPositiveFresh := by simp [K_eq_iff, absorbedPositiveFresh])
        (absorbedFamilyPositiveFresh := by
          simp [K_eq_iff, absorbedFamilyPositiveFresh])
        (by simp [K_eq_iff, absorbedFanFresh])
        (by simp [K_eq_iff, absorbedFanEntryFresh])
        (by simp [K_eq_iff, normalFormFresh])
        (by simp [K_eq_iff, fanHeavyFresh])
        (by simp [K_eq_iff, fanDegreeFourFresh])
        (by simp [K_eq_iff, fanCompatibilityFresh])
        (by simp [K_eq_iff, fanLocalFresh])
        (by simp [K_eq_iff, degreeFourProfileFresh])
        (by simp [K_eq_iff, triangularCoreFresh])
        (by simp [K_eq_iff, fanCapFresh])
        (by simp [K_eq_iff, fanMarkedFresh])
        (by simp [K_eq_iff, fanResidualFresh])
        (by simp [K_eq_iff, certificateMassFresh])
        (by simp [K_eq_iff, cycleFresh])
        (by simp [K_eq_iff, freeFresh])
        (by simp [K_eq_iff, choiceFresh])
        (by simp [K_eq_iff, obstructionFresh])
        (by simp [K_eq_iff, hybridFresh])
        (by simp [K_eq_iff, ledgerFresh])
        (by simp [K_eq_iff, excludedFresh])
        (by simp [K_eq_iff, exclusionResidualFresh])
        (by simp [K_eq_iff, exclusionMassFresh])
        (by simp [K_eq_iff, obstructionMassFresh])
        (by simp [K_eq_iff, absorbedRealizedFresh]) (by simp [K_eq_iff, absorbedDistinguishedFresh])
        (by simp [K_eq_iff, absorbedSilentFresh]) (by simp [K_eq_iff, absorbedRoutedFresh])
        (by simp [K_eq_iff, absorbedTableFresh]) (by simp [K_eq_iff, absorbedClosedFresh])
        (absorbedNeutralFresh := by simp [K_eq_iff, absorbedNeutralFresh])
        (absorbedCanonicalFresh := by simp [K_eq_iff, absorbedCanonicalFresh])
        (absorbedGenuineFresh := by simp [K_eq_iff, absorbedGenuineFresh])
        (absorbedReplacementSwapFresh := by
          simp [K_eq_iff, absorbedReplacementSwapFresh])
        (absorbedReplacementTrivialFresh := by
          simp [K_eq_iff, absorbedReplacementTrivialFresh])
        (absorbedTwoStrandSurvivorFresh := by
          simp [K_eq_iff, absorbedTwoStrandSurvivorFresh])
        (absorbedWindowStubFresh := by simp [K_eq_iff, absorbedWindowStubFresh])
        (absorbedPairExcludedFresh := by simp [K_eq_iff, absorbedPairExcludedFresh])
        (absorbedTerminalFresh := by simp [K_eq_iff, closureFresh])
        (by simp [K_eq_iff, bridgeMassFresh])
        (by simp [K_eq_iff, bridgeSublinearFresh])
        (by simp [K_eq_iff, cubicBaselineFresh])
        (by simp [K_eq_iff, extractedEntryCensusFresh]))
  | .left capped =>
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
          have impossible : False := by
            obtain ⟨packing, valid, cardinality, _maximal, nonnegative⟩ :=
              (nonNegHistory.get (K .netChargeNonNegative)).down
            have negative :=
              (nonNegHistory.get (K .netChargeCap)).down packing valid cardinality
            exact ((selected.object.not_negativeNetCharge_iff
              (selected.object.remainderSupport packing) spineData.threshold
              spineData.dischargeScale).mpr nonnegative) negative
          exact impossible.elim
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
              exact Or.inl (selectedTypeALowSurplusContinuation typeAHistory
                (by simp [K_eq_iff, boundedFresh])
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
                (by simp [K_eq_iff, cubicBaselineFresh]) (by simp [K_eq_iff, normalFormFresh]) (by simp [K_eq_iff, decoratedHeavyFresh]) (by simp [K_eq_iff, decoratedDegreeFourFresh]) (by simp [K_eq_iff, decoratedLocalFresh]) (by simp [K_eq_iff, decoratedCompatibilityFresh]) (by simp [K_eq_iff, decoratedProfileFresh]) (by simp [K_eq_iff, decoratedTriangularCoreFresh]) (by simp [K_eq_iff, fanCapFresh]) (by simp [K_eq_iff, decoratedMarkedFresh]) (by simp [K_eq_iff, decoratedResidualFresh]) (by simp [K_eq_iff, decoratedCertificateMassFresh]) (by simp [K_eq_iff, decoratedCycleFresh]) (by simp [K_eq_iff, decoratedFreeFresh]) (by simp [K_eq_iff, decoratedFanEntryFresh]) (by simp [K_eq_iff, decoratedB2ChoiceFresh]) (by simp [K_eq_iff, decoratedB2ObstructionFresh]) (by simp [K_eq_iff, decoratedHybridFresh]) (by simp [K_eq_iff, decoratedLedgerFresh]) (by simp [K_eq_iff, decoratedBridgeMassFresh]) (by simp [K_eq_iff, decoratedBridgeSublinearFresh]) (by simp [K_eq_iff, decoratedExcludedFresh]) (by simp [K_eq_iff, decoratedExclusionResidualFresh]) (by simp [K_eq_iff, decoratedExclusionMassFresh]) (by simp [K_eq_iff, decoratedObstructionMassFresh])
                (by simp [K_eq_iff, profileFresh]) (by simp [K_eq_iff, squeezeFresh])
                (by simp [K_eq_iff, burdenFresh]) (by simp [K_eq_iff, deficitFresh])
                (by simp [K_eq_iff, deficitFailsFresh])
                (by simp [K_eq_iff, coreFresh])
                (by simp [K_eq_iff, trueResidualFresh])
                (by simp [K_eq_iff, cutParityFresh])
                (by simp [K_eq_iff, smallFresh])
                (by simp [K_eq_iff, noSmallFresh])
                (by simp [K_eq_iff, collapseFresh])
                (by simp [K_eq_iff, censusFresh]) (by simp [K_eq_iff, twoFresh])
                (by simp [K_eq_iff, noTwoFresh])
                (by simp [K_eq_iff, trueEntryFresh])
                (by simp [K_eq_iff, deletionWitnessesFresh])
                (by simp [K_eq_iff, privateBudgetFresh])
                (by simp [K_eq_iff, noTwoContradictionFresh])
                (by simp [K_eq_iff, terminalNoGoFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (by simp [K_eq_iff, typeAExclusionFresh])
                (by simp [K_eq_iff, typeBBridgeReductionFresh])
                (by simp [K_eq_iff, piecesClassifiedFresh])
                (by simp [K_eq_iff, sublinearLedgerFresh])
                (by simp [K_eq_iff, sublinearResidualFresh])
                (by simp [K_eq_iff, unifiedDeficitFresh])
                (by simp [K_eq_iff, quotientFreeFresh])
                (by simp [K_eq_iff, quotientResidualFresh])
                (by simp [K_eq_iff, unifiedCensusFresh])
                (by simp [K_eq_iff, unifiedTrueFresh])
                (by simp [K_eq_iff, peelingFresh])
                (by simp [K_eq_iff, stageFailedFresh])
                (by simp [K_eq_iff, demandLedgerFresh])
                (by simp [K_eq_iff, demandAbsorptionFresh])
                (by simp [K_eq_iff, windowBlockersFresh])
                (by simp [K_eq_iff, demandResidualFresh])
                (by simp [K_eq_iff, unifiedTerminalFresh])
                (by simp [K_eq_iff, closureFresh]))
          | .right typeBHistory =>
              exact Or.inl (selectedTypeBHighSurplusContinuation typeBHistory
                (by simp [K_eq_iff, routingFresh])
                (by simp [K_eq_iff, cubicBaselineFresh])
                (by simp [K_eq_iff, typeBAssignedFresh]) (by simp [K_eq_iff, typeBFanEntryFresh]) (by simp [K_eq_iff, normalFormFresh])
                (by simp [K_eq_iff, fanHeavyFresh]) (by simp [K_eq_iff, fanDegreeFourFresh])
                (by simp [K_eq_iff, fanLocalFresh])
                (by simp [K_eq_iff, fanCompatibilityFresh])
                (by simp [K_eq_iff, fanCapFresh])
                (by simp [K_eq_iff, fanMarkedFresh]) (by simp [K_eq_iff, fanResidualFresh])
                (by simp [K_eq_iff, cycleFresh]) (by simp [K_eq_iff, freeFresh])
                (by simp [K_eq_iff, choiceFresh]) (by simp [K_eq_iff, obstructionFresh])
                (by simp [K_eq_iff, hybridFresh]) (by simp [K_eq_iff, ledgerFresh])
                (by simp [K_eq_iff, bridgeMassFresh])
                (by simp [K_eq_iff, bridgeSublinearFresh])
                (by simp [K_eq_iff, unifiedNegativeFresh])
                (by simp [K_eq_iff, typeAExclusionFresh])
                (by simp [K_eq_iff, typeBBridgeReductionFresh])
                (by simp [K_eq_iff, piecesClassifiedFresh])
                (by simp [K_eq_iff, sublinearLedgerFresh])
                (by simp [K_eq_iff, sublinearResidualFresh])
                (by simp [K_eq_iff, unifiedDeficitFresh])
                (by simp [K_eq_iff, quotientFreeFresh])
                (by simp [K_eq_iff, quotientResidualFresh])
                (by simp [K_eq_iff, unifiedCensusFresh])
                (by simp [K_eq_iff, unifiedTrueFresh])
                (by simp [K_eq_iff, peelingFresh])
                (by simp [K_eq_iff, stageFailedFresh])
                (by simp [K_eq_iff, demandLedgerFresh])
                (by simp [K_eq_iff, demandAbsorptionFresh])
                (by simp [K_eq_iff, windowBlockersFresh])
                (by simp [K_eq_iff, demandResidualFresh])
                (by simp [K_eq_iff, unifiedTerminalFresh])
                (by simp [K_eq_iff, excludedFresh]) (by simp [K_eq_iff, exclusionResidualFresh])
                (by simp [K_eq_iff, exclusionMassFresh]) (by simp [K_eq_iff, obstructionMassFresh])
                (by simp [K_eq_iff, certificateMassFresh])
                (by simp [K_eq_iff, degreeFourProfileFresh])
                (by simp [K_eq_iff, triangularCoreFresh]))



/-! ## Nodes `[50]`--`[52]` on the literal low-entropy residual -/

/-- Run the manuscript's complete low-entropy refinement without erasing any
fact from the incoming `ExactLedger`: structural repetitiveness, dominant
rooted type, the root-wedge split, and—only on the wedge arm—the independent
translate estimate.  Every surviving arm is then written as Residual C before
the caller's next node is invoked. -/
noncomputable def selectedLowTypeToLargeBudget
    {Result : Sort w} {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    {downstream : FactKey EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .remainderEntropyLow) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has downstream known]
    (continue : ∀ {known' : FactKeys EGInput.{u}},
      ExactLedger EGInput.{u} selected known' →
      [FactKeys.Has (K .largeBudgetResidual) known'] →
      [FactKeys.Has downstream known'] → Result)
    (repetitiveFresh : K .localTypeCoordinateRepetitive ∉ known := by
      simp [K_eq_iff])
    (nonrepetitiveFresh : K .localTypeCoordinateNonrepetitive ∉ known := by
      simp [K_eq_iff])
    (dominantFresh : K .dominantRootedType ∉ known := by simp [K_eq_iff])
    (wedgeFresh : K .dominantRootedWedgeType ∉ known := by simp [K_eq_iff])
    (wedgeFreeFresh : K .dominantRootedTypeWedgeFree ∉ known := by
      simp [K_eq_iff])
    (translateFresh : K .independentObstructionTranslates ∉ known := by
      simp [K_eq_iff])
    (largeFresh : K .largeBudgetResidual ∉ known := by simp [K_eq_iff]) :
    Result := by
  match localTypeCoordinateDichotomy (data := spineData) history
      repetitiveFresh nonrepetitiveFresh with
  | .right nonrepetitiveHistory =>
      let large :=
        (lowEntropyLargeBudgetRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          nonrepetitiveHistory (by simp [K_eq_iff, largeFresh])
      exact continue large
  | .left repetitiveHistory =>
      let dominant :=
        (dominantRootedTypeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          repetitiveHistory (by simp [K_eq_iff, dominantFresh])
      match dominantRootedTypeWedgeDichotomy (data := spineData) dominant
          (by simp [K_eq_iff, wedgeFresh])
          (by simp [K_eq_iff, wedgeFreeFresh]) with
      | .right wedgeFreeHistory =>
          let large :=
            (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              wedgeFreeHistory (by simp [K_eq_iff, largeFresh])
          exact continue large
      | .left wedgeHistory =>
          let translated :=
            (independentObstructionTranslatesRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              wedgeHistory (by simp [K_eq_iff, translateFresh])
          let large :=
            (lowEntropyLargeBudgetRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              translated (by simp [K_eq_iff, largeFresh])
          exact continue large

/-! ## Nodes `[25]`--`[55]` on any near-cubic residual

The remainder normalization, boundary demand, stub supply, wedge lower bound,
curvature target-rank and circuit (`[25]`--`[31]`), the rank split `[32]` with
Branch D closed on its yes arm (`[33]`--`[46]`), `cor:forced-curvature-cost`
`[48]`, the remainder-entropy split `[49]`/`[50]`, the rooted-type refinement
and independent-translate argument `[51]`, the window-plus-remainder accounting
and entropy cap `[52]`/`[53]` with `[54]` closed when the comparison retains a
code, and Residual C `[55]` on every surviving entropy/type arm.  The rows are
the same on every arm of the spine; only node `[56]`'s density input differs.
The caller therefore supplies one tail-polymorphic continuation, which receives
the literal Residual-C ledger from the high-entropy route, the nonrepetitive or
wedge-free low-entropy routes, or the repetitive rooted-wedge translate route. -/
-- EG-NODE [25] Residual A: R=G-union V(P) large and componentwise P13-free
-- EG-NODE [26] Residual A: R large and componentwise P13-free
-- EG-NODE [27] no component of R has an internal 3-core
-- EG-NODE [28] positive deficiency def+(X)=sum_v max(0,3-d_X(v))
-- EG-NODE [29] external-incidence supply def+(R)<=15p13+o(n)
-- EG-NODE [30] wedge lower bound W_2(R)>=omega_win|R|-o(|R|)
-- EG-NODE [31] curvature target-rank r_Omega(R)
-- EG-NODE [32] rank drop? r_Omega(R)<W_2(R)-o(W_2)
-- EG-NODE [33] Branch D: rank-reducing curvature dependence
-- EG-NODE [34] Residual B: no rank drop; full curvature rank
-- EG-NODE [35] Branch D: rank-reducing obstruction dependence
-- EG-NODE [47] Residual B: full curvature rank r_Omega(R)>=W_2(R)-o(W_2)
-- EG-NODE [48] forced curvature cost c_Omega W_2(R)>=K_win|R|-o(|R|)
-- EG-NODE [49] per-vertex remainder entropy eta(R)=log2|G(R)|/|R|
-- EG-NODE [50] eta(R)>=(1/10)log2 n ?
-- EG-NODE [51] repetitive dominant rooted type and independent translates
-- EG-NODE [52] window plus remainder accounting bounds theta
-- EG-NODE [53] remaining non-curvature budget < K|R| ?
-- EG-NODE [54] entropy cap closes
-- EG-NODE [55] Residual C: large-budget branch; theta<=theta_win+o(1)
noncomputable def selectedSpineToLargeBudget
    {Result : Sort w} {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    {downstream : FactKey EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has downstream known]
    (continue : ∀ {known' : FactKeys EGInput.{u}},
      ExactLedger EGInput.{u} selected known' →
      [FactKeys.Has (K .largeBudgetResidual) known'] →
      [FactKeys.Has downstream known'] → Result)
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
    (separatedFresh : K .separatedTesters ∉ known := by simp [K_eq_iff])
    (defectFresh : K .contextDefect ∉ known := by simp [K_eq_iff])
    (universalFresh : K .contextUniversal ∉ known := by simp [K_eq_iff])
    (compressionFresh : K .atomCompression ∉ known := by simp [K_eq_iff])
    (delocalizedFresh : K .delocalizedSupport ∉ known := by simp [K_eq_iff])
    (properFresh : K .properDelocalization ∉ known := by simp [K_eq_iff])
    (globalFresh : K .globalDelocalization ∉ known := by simp [K_eq_iff])
    (repairFresh : K .repairIdentity ∉ known := by simp [K_eq_iff])
    (barrierFresh : K .globalBarrier ∉ known := by simp [K_eq_iff])
    (closureFresh : closed ∉ known := by simp [K_eq_iff])
    (entropyBoundFresh : K .entropyCapBound ∉ known := by simp [K_eq_iff])
    (costFresh : K .forcedCurvatureCost ∉ known := by simp [K_eq_iff])
    (highFresh : K .remainderEntropyHigh ∉ known := by simp [K_eq_iff])
    (lowFresh : K .remainderEntropyLow ∉ known := by simp [K_eq_iff])
    (packageFresh : K .entropyPackageDemand ∉ known := by simp [K_eq_iff])
    (activeFresh : K .entropyCapActive ∉ known := by simp [K_eq_iff])
    (largeFresh : K .largeBudgetResidual ∉ known := by simp [K_eq_iff]) :
    Result := by
  let remainder :=
    (remainderNormalizationRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        history (by simp [K_eq_iff, remainderFresh])
  let relabelingEntropy :=
    (remainderRelabelingEntropyRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        remainder (by simp [K_eq_iff])
  let boundary :=
    (boundaryDemandRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)).run
        relabelingEntropy (by simp [K_eq_iff, boundaryFresh])
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
      -- `[35]`: retain the Branch-D state and append only
      -- `lem:separated-testers` to the same literal ledger.
      let tested :=
        (separatedTestersRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) spineData).run
          dependence (by simp [K_eq_iff, separatedFresh])
      exact (selectedRankDropCloses tested
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
      -- `[52]`/`[53]`: the high arm performs only the manuscript's independent
      -- window/remainder accounting and entropy-cap test.
      let package :=
        (entropyPackageRow (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) spineData).run
        highHistory (by simp [K_eq_iff, packageFresh])
      match entropyCapDichotomy (data := spineData) package
          (by simp [K_eq_iff, activeFresh]) (by simp [K_eq_iff, largeFresh]) with
      | .left activeHistory =>
          -- `[54]`: the sealed row derives the exact opposite budget bound on
          -- both alternatives stored in `K .hotColdPartition`; Core closes the
          -- resulting incompatible facts on this literal active ledger.
          let closedHistory :=
            (entropyCapBoundRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).runAndCloseIncompatible
                activeHistory
                (K .entropyCapActive) (K .entropyCapBound)
                (by simp [K_eq_iff, entropyBoundFresh])
                (by simp [K_eq_iff, closureFresh])
          exact (closedHistory.elimClosed (by infer_instance)).elim
      | .right largeHistory =>
          exact continue largeHistory
  | .right lowHistory =>
      exact selectedLowTypeToLargeBudget lowHistory continue
        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
        (by simp [K_eq_iff, largeFresh])

/-- The near-cubic branch after node `[19]`: node `[21]`, the `[22]` split and
live-hot cap, and — on the cap arm, exactly as `[24]` prescribes — the cold
branch `[145]`--`[157]` on the literal cap residual.  Both spine arms — `[146]`'s
yes arm (`θ < 1/78`, node `[147]`: closed by the spine's route-8 closure with
`K .coldRoute8Below` as its private-carrier inequality) and `[153]`'s bounded
arm (`[24]`'s density cap) — run `[25]`--`[31]` on their literal residuals,
decide `[32]` and enter `[33]` (Branch D) or `[34]` (Residual B); `[35]`--`[46]`
and `[47]` onward fail loudly; the routed cold closure `[157]` fails loudly at
its target-defect/handoff discharge. -/
-- EG-NODE [22] hot/cold split P=P_hot+P_cold: live-hot entropy cap closes?
-- EG-NODE [24] bounded cold-mass return from [153]: theta<=theta_win+o(1)
-- EG-NODE [25] Residual A: R=G-union V(P) large and componentwise P13-free
-- EG-NODE [26] Residual A: R large and componentwise P13-free
-- EG-NODE [27] no component of R has an internal 3-core
-- EG-NODE [28] positive deficiency def+(X)
-- EG-NODE [29] external-incidence supply def+(R)<=15p13+o(n)
-- EG-NODE [30] wedge lower bound W_2(R)>=omega_win|R|-o(|R|)
-- EG-NODE [31] curvature target-rank r_Omega(R)
-- EG-NODE [32] rank drop? r_Omega(R)<W_2(R)-o(W_2)
-- EG-NODE [33] Branch D: rank-reducing curvature dependence
-- EG-NODE [34] Residual B: no rank drop; full curvature rank
-- EG-NODE [35] Branch D: rank-reducing obstruction dependence
-- EG-NODE [47] Residual B: full curvature rank r_Omega(R)>=W_2(R)-o(W_2)
-- EG-NODE [48] forced curvature cost c_Omega W_2(R)>=K_win|R|-o(|R|)
-- EG-NODE [49] per-vertex remainder entropy eta(R)
-- EG-NODE [50] eta(R)>=(1/10)log2 n ?
-- EG-NODE [51] repetitive dominant rooted type and independent translates
-- EG-NODE [52] window plus remainder accounting bounds theta
-- EG-NODE [53] remaining non-curvature budget < K|R| ?
-- EG-NODE [54] entropy cap closes
-- EG-NODE [55] Residual C: large-budget branch; theta<=theta_win+o(1)
-- EG-NODE [56] Delta_net(R)=(def+(R)-sigma_R)/|R| <= tau_win+o(1) < 1/4
-- EG-NODE [145] cold-branch continuation from the no-edge of [22]
-- EG-NODE [146] theta < 1/78 ?
-- EG-NODE [147] route-8 private-carrier collision closes
-- EG-NODE [148] live-hot entropy cap closes?
-- EG-NODE [150] hot failure forces cold mass C>=(theta-theta_win)n-o(n)
-- EG-NODE [151] all but o(n) cold windows ambient-cubic
-- EG-NODE [152] selected interior stub excess b_int(S_cold)>=9C-o(n)
-- EG-NODE [153] linear first-failure extraction? N_germ>=9C/D_cold-o(n)
-- EG-NODE [154] bounded germ case?
-- EG-NODE [155] G1: dyadic cycle
-- EG-NODE [156] G2: target defect, exit (4), or handoff
-- EG-NODE [157] G3 or same-interface table: compression
-- EG-NODE [160] tau(theta) < 1/4 ? (exact [56] comparison)
-- EG-NODE [161] negative-net-charge collision: continue at [25] with deficiency cap
-- EG-NODE [162] dense hot/cold pass: run [22]-[24] and [145]-[157] on dense residual
-- EG-NODE [163] neutral equal-length terminal germ: second strand genuine?
-- EG-NODE [164] all-cold comparison closes: |G(R)|<=|G_{n,m}| by remainder glue
-- EG-NODE [165] canonical replacement E!=Q: same-size counterexample
-- EG-NODE [166] refined lexicographic minimality: Q=E
-- EG-NODE [167] symmetric strand pair: finite two-strand check
-- EG-NODE [168] surviving symmetric pair: endpoint/interior-stub exclusion
-- EG-NODE [169] trivial neutral germ residual: dense packing, all corridors terminal
abbrev SelectedNearCubicSurvivorBoundary (selected : EGInput.{u}) :=
  SelectedNetChargeBoundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .route8RateFails selected.object ∨
      Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData .coldBranchClosed selected.object

set_option maxHeartbeats 4000000 in
noncomputable def selectedNearCubicSurvivorBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicSurvivorBoundary selected := by
  let dominated := selectedNearCubicNode21 history
  match selectedWindowPackageRealizationDichotomy dominated with
  | .right unrealizedHistory =>
      -- The residual on which the manuscript's `[21]` realization sentence
      -- fails (dense packing: `2^{bits·p}` exceeds the skeleton states).  The
      -- manuscript's own nodes are run on it: `[22]`'s partition, then the
      -- `τ(θ) < 1/4` reading of `prop:negative-net-charge` as a decision.
      let denseOverflow :=
        (densePackingOverflowRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          unrealizedHistory (by simp [K_eq_iff])
      let partitioned :=
        (hotColdPartitionRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          denseOverflow (by simp [K_eq_iff])
      -- `[145]` is the direct handoff of `[22]`'s hot/cold fact.  Both
      -- deficiency arms read it from this same literal ExactLedger.
      match Decision.run partitioned (K .denseDeficiencyBelow) (K .denseDeficiencyAtOrAbove)
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
          -- branches, with `[56]` read from the decision.  The route-8 rate
          -- `τ < 3/13` (`[120]`) is not decided by `τ < 1/4`; it is decided here
          -- (`route8RateDichotomy`), and its failure — the manuscript's delicate
          -- density interval `3/13 ≤ τ < 1/4`, row 2 of `tab:cold-branch-ledger`,
          -- which the manuscript sends to the hot/cold pass — is the next producer.
          match route8RateDichotomy (data := spineData) belowHistory
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .right rateFails =>
              -- The exact interval `3/13 ≤ τ < 1/4` does not satisfy the
              -- private-carrier input of `[120]`--`[122]`.  Keep both literal
              -- decision facts and run `[162]` on this residual; in particular,
              -- do not fabricate `K .route8Rate` in order to enter `[161]`.
              match selectedBarrierDichotomy rateFails
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .right overflowHistory =>
                  exact (selectedBarrierOverflowCloses overflowHistory
                    (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim
              | .left capHistory =>
              match coldRoute8Dichotomy (data := spineData) capHistory
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left coldBelowHistory =>
                  let coldBelowHistory :=
                    (route8RateFromColdBelowRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run coldBelowHistory
                      (by simp [K_eq_iff])
                  exact selectedSpineToLargeBudget
                    (downstream := K .coldRoute8Below) coldBelowHistory
                    (fun spineHistory =>
                      let netCap :=
                        (routeEightNetDeficiencyCapRow
                          (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run spineHistory
                          (by simp [K_eq_iff])
                      Or.inl (selectedNetChargeContinuation netCap))
              | .right coldAtOrAboveHistory =>
              match coldHotEntropyDichotomy (data := spineData)
                  coldAtOrAboveHistory (by simp [K_eq_iff])
                  (by simp [K_eq_iff]) with
              | .left overflowHistory =>
                  exact (selectedColdHotEntropyCloses overflowHistory).elim
              | .right hotCapHistory =>
              let mass :=
                (coldMassRow (data := spineData)).run hotCapHistory
                  (by simp [K_eq_iff])
              let cubic :=
                (coldAmbientCubicRow (data := spineData)).run mass
                  (by simp [K_eq_iff])
              let stubs :=
                (coldStubExcessRow (data := spineData)).run cubic
                  (by simp [K_eq_iff])
              match coldMassDichotomy (data := spineData) stubs
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left linearHistory =>
                  let normalized :=
                    (remainderNormalizationRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run linearHistory
                      (by simp [K_eq_iff])
                  let relabelingEntropy :=
                    (remainderRelabelingEntropyRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run normalized (by simp [K_eq_iff])
                  let bridgeless :=
                    (bridgelessRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run relabelingEntropy
                      (by simp [K_eq_iff])
                  let corridors :=
                    (coldReturnCorridorRow (data := spineData)).run bridgeless
                      (by simp [K_eq_iff])
                  let declared :=
                    (coldDeclaredHandoffLedgerRow (data := spineData)).run
                      corridors (by simp [K_eq_iff])
                  let state :=
                    (coldCorridorStateRow (data := spineData)).run declared
                      (by simp [K_eq_iff])
                  let terminal :=
                    (denseColdCorridorsTerminalRow (data := spineData)).run state
                      (by simp [K_eq_iff])
                  let occurrence :=
                    (coldFirstFailureOccurrenceRow (data := spineData)).run
                      terminal (by simp [K_eq_iff])
                  let failureCycle :=
                    (coldFailureCycleRow (data := spineData)).run occurrence
                      (by simp [K_eq_iff])
                  let failureDefect :=
                    (coldFailureDefectRow (data := spineData)).run failureCycle
                      (by simp [K_eq_iff])
                  let failureCompression :=
                    (coldFailureCompressionRow (data := spineData)).run
                      failureDefect (by simp [K_eq_iff])
                  let failureHandoff :=
                    (coldFailureHandoffRow (data := spineData)).run
                      failureCompression (by simp [K_eq_iff])
                  let handoffTransfer :=
                    (coldHandoffTransferRow (data := spineData)).run
                      failureHandoff (by simp [K_eq_iff])
                  let routed :=
                    (coldFirstFailureRoutingRow (data := spineData)).run
                      handoffTransfer
                      (by simp [K_eq_iff])
                  let extracted :=
                    (coldGermExtractionRow (data := spineData)).run routed
                      (by simp [K_eq_iff])
                  let candidates :=
                    (coldGermCandidatesRow (data := spineData)).run extracted
                      (by simp [K_eq_iff])
                  let positive :=
                    (coldGermFamilyPositiveRow (data := spineData)).run candidates
                      (by simp [K_eq_iff])
                  let neutralConfiguration :=
                    (neutralEqualLengthTerminalRow (data := spineData)).run positive
                      (by simp [K_eq_iff])
                  let trichotomy :=
                    (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
                      (by simp [K_eq_iff])
                  let table :=
                    (coldSameInterfaceTableRow (data := spineData)).run trichotomy
                      (by simp [K_eq_iff])
                  let closed :=
                    (coldBranchClosedRow (data := spineData)).run table
                      (by simp [K_eq_iff])
                  match neutralGermSymmetryDichotomy (data := spineData)
                      closed (by simp [K_eq_iff])
                      (by simp [K_eq_iff]) with
                  | .left canonicalHistory =>
                      let swapped :=
                        (canonicalReplacementSwapRow (data := spineData)).run
                          canonicalHistory (by simp [K_eq_iff])
                      exact Or.inr (Or.inr (Or.inl
                        (selectedCanonicalReplacementContinuation swapped)))
                  | .right genuineHistory =>
                      let survivor :=
                        (twoStrandSurvivorRow (data := spineData)).run
                          genuineHistory (by simp [K_eq_iff])
                      let stubbed :=
                        (coldWindowStubStructureRow (data := spineData)).run
                          survivor (by simp [K_eq_iff])
                      let closedHistory :=
                        (symmetricPairEndpointExclusionRow
                          (data := spineData)).runAndCloseIncompatible
                          stubbed (K .coldTwoStrandSurvivor)
                            (K .coldSymmetricPairExcluded)
                          (by simp [K_eq_iff]) (by simp [K_eq_iff])
                      exact (closedHistory.elimClosed (by infer_instance)).elim
              | .right boundedHistory =>
                  -- `[162]` has now been reached correctly.  Its bounded
                  -- `[153]` arm returns through `[24]`; the existing exact
                  -- finite route-rate decision remains the first downstream
                  -- obligation if that stronger rate still fails.
                  let density :=
                    (densityBudgetRow (data := spineData)).run boundedHistory
                      (by simp [K_eq_iff])
                  exact Or.inr (Or.inl
                    (density.get (K .route8RateFails)).down)
          | .left belowHistory =>
          exact selectedSpineToLargeBudget
            (downstream := K .denseDeficiencyBelow) belowHistory
            (fun spineHistory =>
              let netCap :=
                (denseNetDeficiencyCapRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  spineHistory (by simp [K_eq_iff])
              Or.inl (selectedNetChargeContinuation netCap))
      | .right denseHistory =>
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
              let belowHistory :=
                (route8RateFromColdBelowRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  belowHistory (by simp [K_eq_iff])
              -- `[147]`: `τ(θ) < 3/13`, the spine's route-8 closure with that
              -- inequality as `[56]`'s input.
              exact selectedSpineToLargeBudget
                (downstream := K .coldRoute8Below) belowHistory
                (fun spineHistory =>
                  let netCap :=
                    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      spineHistory (by simp [K_eq_iff])
                  Or.inl (selectedNetChargeContinuation netCap))
          | .right atOrAboveHistory =>
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
              -- `[153]`--`[157]` on the dense linear residual: `lem:bridgeless`,
              -- return corridors, first-failure routing, exchange bound and
              -- extraction, the (F5) candidate family, the germ trichotomy and
              -- the same-interface table.  (F1)/G1 close by `K .selection`,
              -- (F2)/G2 by `lem:context-universality`, (F3)/G3 by
              -- `K .replacementExclusion`; the residual after them is the
              -- neutral equal-length terminal germ `[163]`, a symmetry
              -- (`lem:neutral-germ-symmetry`): canonical-replacement swap
              -- (`[165]`--`[166]`, refined minimality: needs the (F5) exchange
              -- representative `E` built as a piece and the selection order
              -- refined by the canonical atom multiset) or a genuine symmetric
              -- strand pair (`[167]`, `Graph/TwoStrandEnumeration.lean`: closed
              -- by a dyadic cycle iff `2ℓ ∈ Pow ∨ ℓ + d ∈ Pow`; the surviving
              -- pairs `ℓ ∉ Pow ∧ ℓ + d ∉ Pow` are `[168]`).
              let normalized :=
                (remainderNormalizationRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  linearHistory (by simp [K_eq_iff])
              let relabelingEntropy :=
                (remainderRelabelingEntropyRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run normalized (by simp [K_eq_iff])
              let bridgeless :=
                (bridgelessRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                  relabelingEntropy (by simp [K_eq_iff])
              let corridors :=
                (coldReturnCorridorRow (data := spineData)).run bridgeless (by simp [K_eq_iff])
              let declared :=
                (coldDeclaredHandoffLedgerRow (data := spineData)).run corridors
                  (by simp [K_eq_iff])
              let state :=
                (coldCorridorStateRow (data := spineData)).run declared
                  (by simp [K_eq_iff])
              let terminal :=
                (denseColdCorridorsTerminalRow (data := spineData)).run state
                  (by simp [K_eq_iff])
              let occurrence :=
                (coldFirstFailureOccurrenceRow (data := spineData)).run terminal
                  (by simp [K_eq_iff])
              let failureCycle :=
                (coldFailureCycleRow (data := spineData)).run occurrence
                  (by simp [K_eq_iff])
              let failureDefect :=
                (coldFailureDefectRow (data := spineData)).run failureCycle
                  (by simp [K_eq_iff])
              let failureCompression :=
                (coldFailureCompressionRow (data := spineData)).run failureDefect
                  (by simp [K_eq_iff])
              let failureHandoff :=
                (coldFailureHandoffRow (data := spineData)).run failureCompression
                  (by simp [K_eq_iff])
              let handoffTransfer :=
                (coldHandoffTransferRow (data := spineData)).run failureHandoff
                  (by simp [K_eq_iff])
              let routed :=
                (coldFirstFailureRoutingRow (data := spineData)).run handoffTransfer
                  (by simp [K_eq_iff])
              let extracted :=
                (coldGermExtractionRow (data := spineData)).run routed
                  (by simp [K_eq_iff])
              let candidates :=
                (coldGermCandidatesRow (data := spineData)).run extracted (by simp [K_eq_iff])
              let positive :=
                (coldGermFamilyPositiveRow (data := spineData)).run candidates
                  (by simp [K_eq_iff])
              let neutralConfiguration :=
                (neutralEqualLengthTerminalRow (data := spineData)).run positive
                  (by simp [K_eq_iff])
              let trichotomy :=
                (coldGermTrichotomyRow (data := spineData)).run neutralConfiguration
                  (by simp [K_eq_iff])
              let table :=
                (coldSameInterfaceTableRow (data := spineData)).run trichotomy
                  (by simp [K_eq_iff])
              let closed :=
                (coldBranchClosedRow (data := spineData)).run table (by simp [K_eq_iff])
              -- `[163]`, `lem:neutral-germ-symmetry`: decide the manuscript's
              -- literal question — whether the neutral equal-length terminal
              -- configuration has a graph-realized second representative.
              match neutralGermSymmetryDichotomy (data := spineData)
                  closed
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left canonicalHistory =>
                  -- `[165]`: the marked `E ≠ Q` exchange preserves the baseline,
                  -- target avoidance, and both graph counts, while replacing the
                  -- marked canonical-decomposition piece by a strict predecessor.
                  -- `[166]` consumes this literal ledger fact with node `[4]`'s
                  -- refined minimality and retains only `Q = E`.
                  let swapped :=
                    (canonicalReplacementSwapRow (data := spineData)).run
                      canonicalHistory (by simp [K_eq_iff])
                  exact Or.inr (Or.inr (Or.inl
                    (selectedCanonicalReplacementContinuation swapped)))
              | .right genuineHistory =>
                  -- `[167]` retains the finite-check survivor; `[168]` proves
                  -- its exclusion from the selected interior occurrence and
                  -- closes the two exact facts through Core.
                  let survivor :=
                    (twoStrandSurvivorRow (data := spineData)).run genuineHistory
                      (by simp [K_eq_iff])
                  let stubbed :=
                    (coldWindowStubStructureRow (data := spineData)).run survivor
                      (by simp [K_eq_iff])
                  let closedHistory :=
                    (symmetricPairEndpointExclusionRow
                      (data := spineData)).runAndCloseIncompatible
                      stubbed (K .coldTwoStrandSurvivor)
                        (K .coldSymmetricPairExcluded)
                      (by simp [K_eq_iff]) (by simp [K_eq_iff])
                  exact (closedHistory.elimClosed (by infer_instance)).elim
          | .right boundedHistory =>
              -- `[24]`: the density cap on the bounded arm, then the spine.  The
              -- route-8 rate `τ < 3/13` (`[120]`) follows from the density cap
              -- only for sufficiently large `n`; it is decided here, and its
              -- failure (`densityCap` with `3/13 ≤ τ`, a finite-order corner
              -- like `[57]`'s) is the next producer.
              let density :=
                (densityBudgetRow (data := spineData)).run boundedHistory (by simp [K_eq_iff])
              match route8RateDichotomy (data := spineData) density
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .right rateFails =>
                  exact Or.inr (Or.inl
                    (rateFails.get (K .route8RateFails)).down)
              | .left density =>
              exact selectedSpineToLargeBudget
                (downstream := K .densityCap) density
                (fun spineHistory =>
                  let netCap :=
                    (netDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      spineHistory (by simp [K_eq_iff])
                  Or.inl (selectedNetChargeContinuation netCap))
  | .left enumerated =>
  let partitioned :=
    (hotColdPartitionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      enumerated (by simp [K_eq_iff])
  match selectedBarrierDichotomy partitioned
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left capHistory =>
      -- `[145]` carries no mathematical assertion of its own: pass the
      -- literal `[22]` ledger directly to `[146]`.
      match coldRoute8Dichotomy (data := spineData) capHistory
          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
      | .left belowHistory =>
          -- The route-8 rate `K .route8Rate` (`[120]`, `τ < 3/13` with the exact
          -- allowances) is `K .coldRoute8Below` read through `|∂R| ≤ 15p + σ_W`.
          let belowHistory :=
            (route8RateFromColdBelowRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              belowHistory (by simp [K_eq_iff])
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
          let relabelingEntropy :=
            (remainderRelabelingEntropyRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run remainder (by simp [K_eq_iff])
          let boundary :=
            (boundaryDemandRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              relabelingEntropy (by simp [K_eq_iff])
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
              -- inclusion-minimal connected support.
              let dependence :=
                (branchDependenceRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  dropHistory (by simp [K_eq_iff])
              -- `[35]`: the repeated Branch-D state plus the exact
              -- `lem:separated-testers` fact on this literal ancestry.
              let tested :=
                (separatedTestersRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  dependence (by simp [K_eq_iff])
              exact (selectedRankDropCloses tested
                (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim
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
              -- `[52]`: join the high-entropy remainder and window accounts;
              -- `[53]`: test the resulting entropy cap.
              let package :=
                (entropyPackageRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile) spineData).run
                  highHistory (by simp [K_eq_iff])
              match entropyCapDichotomy (data := spineData) package
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left activeHistory =>
                  -- `[54]`: the sealed row handles both alternatives already
                  -- stored in `K .hotColdPartition` and publishes only the exact
                  -- opposite budget bound.  Core closes the two registered facts.
                  let closedHistory :=
                    (entropyCapBoundRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).runAndCloseIncompatible activeHistory
                        (K .entropyCapActive) (K .entropyCapBound)
                        (by simp [K_eq_iff]) (by simp [K_eq_iff])
                  exact (closedHistory.elimClosed (by infer_instance)).elim
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
                  exact Or.inl (selectedNetChargeContinuation netCap)
          | .right lowHistory =>
              -- `[50]`--`[52]`: perform the manuscript's repetitive/nonrepetitive
              -- and root-wedge splits before writing Residual C.
              exact selectedLowTypeToLargeBudget
                (downstream := K .coldRoute8Below) lowHistory
                (fun largeHistory =>
                  let netCap :=
                    (routeEightNetDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run largeHistory (by simp [K_eq_iff])
                  Or.inl (selectedNetChargeContinuation netCap))
      | .right atOrAboveHistory =>
          match coldHotEntropyDichotomy (data := spineData) atOrAboveHistory
              (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
          | .left overflowHistory =>
              exact (selectedColdHotEntropyCloses overflowHistory).elim
          | .right hotCapHistory =>
              let mass :=
                (coldMassRow (data := spineData)).run hotCapHistory
                  (by simp [K_eq_iff])
              let cubic :=
                (coldAmbientCubicRow (data := spineData)).run mass
                  (by simp [K_eq_iff])
              let stubs :=
                (coldStubExcessRow (data := spineData)).run cubic
                  (by simp [K_eq_iff])
              match coldMassDichotomy (data := spineData) stubs
                  (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
              | .left linearHistory =>
                  -- `[153]`: `lem:bridgeless`, the return corridors, first-failure
                  -- routing, the exchange bound and extraction, and the (F5)
                  -- candidate germ family on the linear residual; then `[154]`.
                  let bridgeless :=
                    (bridgelessRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run linearHistory
                      (by simp [K_eq_iff])
                  let corridors :=
                    (coldReturnCorridorRow (data := spineData)).run bridgeless
                      (by simp [K_eq_iff])
                  let declared :=
                    (coldDeclaredHandoffLedgerRow (data := spineData)).run
                      corridors (by simp [K_eq_iff])
                  let state :=
                    (coldCorridorStateRow (data := spineData)).run declared
                      (by simp [K_eq_iff])
                  let occurrence :=
                    (coldFirstFailureOccurrenceRow (data := spineData)).run
                      state (by simp [K_eq_iff])
                  let failureCycle :=
                    (coldFailureCycleRow (data := spineData)).run occurrence
                      (by simp [K_eq_iff])
                  let failureDefect :=
                    (coldFailureDefectRow (data := spineData)).run failureCycle
                      (by simp [K_eq_iff])
                  let failureCompression :=
                    (coldFailureCompressionRow (data := spineData)).run
                      failureDefect (by simp [K_eq_iff])
                  let failureHandoff :=
                    (coldFailureHandoffRow (data := spineData)).run
                      failureCompression (by simp [K_eq_iff])
                  let handoffTransfer :=
                    (coldHandoffTransferRow (data := spineData)).run
                      failureHandoff (by simp [K_eq_iff])
                  let routed :=
                    (coldFirstFailureRoutingRow (data := spineData)).run
                      handoffTransfer (by simp [K_eq_iff])
                  let extracted :=
                    (coldGermExtractionRow (data := spineData)).run routed
                      (by simp [K_eq_iff])
                  let candidates :=
                    (coldGermCandidatesRow (data := spineData)).run extracted
                      (by simp [K_eq_iff])
                  let positive :=
                    (coldGermFamilyPositiveRow (data := spineData)).run candidates
                      (by simp [K_eq_iff])
                  let trichotomy :=
                    (coldGermTrichotomyRow (data := spineData)).run positive
                      (by simp [K_eq_iff])
                  let table :=
                    (coldSameInterfaceTableRow (data := spineData)).run trichotomy
                      (by simp [K_eq_iff])
                  let closed :=
                    (coldBranchClosedRow (data := spineData)).run table
                      (by simp [K_eq_iff])
                  -- The realized-package arm is the ordinary Part-XI oval.
                  -- Its paper edge ends at `[157]`; only `[159]`'s dense
                  -- residual continues to the neutral split `[163]`.
                  exact Or.inr (Or.inr (Or.inr
                    (closed.get (K .coldBranchClosed)).down))
              | .right boundedHistory =>
                  -- `[24]` → `[25]`--`[30]` on the literal bounded residual; the
                  -- route-8 rate `τ < 3/13` (`[120]`) is decided on the density
                  -- cap (it follows only for sufficiently large `n`).
                  let density :=
                    (densityBudgetRow (data := spineData)).run boundedHistory
                      (by simp [K_eq_iff])
                  match route8RateDichotomy (data := spineData) density
                      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                  | .right rateFails =>
                      exact Or.inr (Or.inl
                        (rateFails.get (K .route8RateFails)).down)
                  | .left density =>
                  let remainder :=
                    (remainderNormalizationRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      density (by simp [K_eq_iff])
                  let relabelingEntropy :=
                    (remainderRelabelingEntropyRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run remainder (by simp [K_eq_iff])
                  let boundary :=
                    (boundaryDemandRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                      relabelingEntropy (by simp [K_eq_iff])
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
                      -- inclusion-minimal connected support.
                      let dependence :=
                        (branchDependenceRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) spineData).run
                          dropHistory (by simp [K_eq_iff])
                      -- `[35]`: the repeated Branch-D state plus the exact
                      -- `lem:separated-testers` fact on this literal ancestry.
                      let tested :=
                        (separatedTestersRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) spineData).run
                          dependence (by simp [K_eq_iff])
                      exact (selectedRankDropCloses tested
                        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
                        (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim
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
                      -- `[52]`: join the high-entropy remainder and window accounts;
                      -- `[53]`: test the resulting entropy cap.
                      let package :=
                        (entropyPackageRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile) spineData).run
                          highHistory (by simp [K_eq_iff])
                      match entropyCapDichotomy (data := spineData) package
                          (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
                      | .left activeHistory =>
                          -- `[54]`: the same sealed bound row runs on this literal
                          -- active ledger, and Core owns the terminal closure.
                          let closedHistory :=
                            (entropyCapBoundRow (BranchState := BranchState)
                              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).runAndCloseIncompatible
                                activeHistory (K .entropyCapActive)
                                (K .entropyCapBound)
                                (by simp [K_eq_iff]) (by simp [K_eq_iff])
                          exact (closedHistory.elimClosed (by infer_instance)).elim
                      | .right largeHistory =>
                          -- `[55]`: Residual C on the high-entropy arm.
                          -- `[56]`: `Δ_net(R) ≤ τ_win + o(1) < 1/4` from `[24]`'s density cap.
                          let netCap :=
                            (netDeficiencyCapRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
                              largeHistory (by simp [K_eq_iff])
                          -- `[57]` onward on this residual is the next producer.
                          exact Or.inl (selectedNetChargeContinuation netCap)
                  | .right lowHistory =>
                      -- `[50]`--`[52]`: retain the exact low-arm refinement and
                      -- invoke the translate row only on the root-wedge arm.
                      exact selectedLowTypeToLargeBudget
                        (downstream := K .densityCap) lowHistory
                        (fun largeHistory =>
                          let netCap :=
                            (netDeficiencyCapRow (BranchState := BranchState)
                              (Presentation :=
                                Graph.ReceiverLoad.LoadCapacityProfile)
                              (presentation := erdosReceiverLoadProfile)
                              (data := spineData)).run largeHistory
                              (by simp [K_eq_iff])
                          Or.inl (selectedNetChargeContinuation netCap))
  | .right overflowHistory =>
      exact (selectedBarrierOverflowCloses overflowHistory
        (by simp [K_eq_iff]) (by simp [K_eq_iff])).elim

/-- The literal target-defect exit left by the enclosing `[20]` sparse-exit
classification.  It is an outgoing residual, not a contradiction, not a
survivor fact, and not an output of routing-only node `[125]`. -/
abbrev SelectedSparseTargetDefectBoundary (selected : EGInput.{u}) :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
    erdosReceiverLoadProfile spineData .sparseTargetDefectResidual
      selected.object

/-- The near-cubic branch either leaves through the paper's named
target-defect exit or, after all sparse exits have been excluded, follows the
surviving-cold/net-charge continuation. -/
abbrev SelectedNearCubicBoundary (selected : EGInput.{u}) :=
  SelectedSparseTargetDefectBoundary selected ∨
    SelectedNearCubicSurvivorBoundary selected

/-- Establish `def:surviving-cold-branch` before entering any hot/cold or
net-charge descendant.  The exhaustive sparse-exit split belongs to the
enclosing routing; its survivor ledger crosses `[125]` unchanged and is then
retained monotonically by every later ExactLedger. -/
noncomputable def selectedNearCubicBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres,
        K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicBoundary selected := by
  match sparseSurplusSurvivorDichotomy
      (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData) history
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) with
  | .left exitHistory =>
      let targetDefect :=
        (sparseSurplusExitRoutingRow
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run exitHistory
          (by simp [K_eq_iff])
      exact Or.inl (targetDefect.get (K .sparseTargetDefectResidual)).down
  | .right survivorHistory =>
      let node125 := selectedSparseSurplusSurvivorNode125 survivorHistory
      exact Or.inr (selectedNearCubicSurvivorBranch node125)

/-- Selected-root boundary, assembled directly from the exact-ledger rows.
The raw Type B entry alternative is retained only for the earlier
`[178]`/`[180]` routes; `[144]` now exposes the concrete result of the common
`[65]`--`[85]` accounting continuation.  The final alternative is the open
node-`[182]` fact produced by the repaired `[178]`--`[180]` chain. -/
-- EG-NODE none (establishes no manuscript DAG node)
abbrev SelectedLedgerBoundaryResult (selected : EGInput.{u}) :=
  SelectedSparseTargetDefectBoundary selected ∨
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
        erdosReceiverLoadProfile spineData .typeBFanEntry selected.object ∨
      SelectedTypeBChargeBoundary selected ∨
        Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
          erdosReceiverLoadProfile spineData
              .pairConditionalFactorizationResidual selected.object ∨
          SelectedNearCubicSurvivorBoundary selected

noncomputable def selectedLedgerBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected := by
  match selectedSurplusDichotomy history with
  | .left strictHistory =>
      match selectedSparseSurplusDichotomy strictHistory with
      | .left exitHistory =>
          -- The enclosing `[20]` classification routes the literal exit forms
          -- and retains only the exact attempted-quotient target-defect
          -- payload for its later peeling handoff.  It never enters `[125]`.
          let targetDefectHistory :=
            selectedSparseSurplusExitContinuation exitHistory
          exact Or.inl
            (targetDefectHistory.get (K .sparseTargetDefectResidual)).down
      | .right survivorHistory =>
          match selectedStrictSurplusBranch survivorHistory with
          | .inl (.inl fan) => exact Or.inr (Or.inl fan.down)
          | .inl (.inr charged) => exact Or.inr (Or.inr (Or.inl
              (selectedTypeBChargeOutcomeDown charged)))
          | .inr pair => exact Or.inr (Or.inr (Or.inr (Or.inl pair.down)))
  | .right nearCubicHistory =>
      match selectedNearCubicBranch nearCubicHistory with
      | .inl targetDefect => exact Or.inl targetDefect
      | .inr boundary => exact Or.inr (Or.inr (Or.inr (Or.inr boundary)))

end HypostructureErdos64EG
