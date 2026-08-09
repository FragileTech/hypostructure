import HypostructureErdos64EG.Problem
import Hypostructure.Graph.Strategy.SpineContinuationRun

/-!
# Final Erdős assembly boundary

This file connects the public `Core.Target` registered in `Problem.lean` to the
canonical exact-ledger residual used by the spine.  It does not define rows,
carriers, routers, or side payloads: the only proof input it accepts is the
ledger theorem that the selected residual whose ledger starts with
`K .selection` closes.
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
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection] := by
  let h1 :=
    (returnAvoidance (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by
        simp [returnAvoidance, EGSelectionKey, K_eq_iff])
  let h2 :=
    (noProperBaseline (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by
        simp [noProperBaseline, returnAvoidance, EGSelectionKey, K_eq_iff])
  let h3 :=
    (deletionCriticality (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [deletionCriticality, noProperBaseline, returnAvoidance,
          EGSelectionKey, K_eq_iff])
  let h4 :=
    (interfaceReplacement (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      EGTarget rfl).run h3 (by
        simp [interfaceReplacement, deletionCriticality, noProperBaseline,
          returnAvoidance, EGTarget, EGSelectionKey, K_eq_iff])
  let h5 :=
    (obstructionPacking (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h4 (by
        simp [obstructionPacking, interfaceReplacement, deletionCriticality,
          noProperBaseline, returnAvoidance, EGTarget, EGSelectionKey,
          K_eq_iff])
  exact
    (localAlgebra (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h5 (by
        simp [localAlgebra, obstructionPacking, interfaceReplacement,
          deletionCriticality, noProperBaseline, returnAvoidance, EGTarget,
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
  surplusDichotomy (data := spineData) (selectedEntryPrefix history)
    (K .surplusAbove) (K .surplusAtOrBelow)
    (fun _above => ⟨_above⟩)
    (fun _below => ⟨_below⟩)
    (by simp [selectedEntryPrefix, EGSelectionKey, K_eq_iff])
    (by simp [selectedEntryPrefix, EGSelectionKey, K_eq_iff])

/-- Nodes `[125]`--`[128]`, sparse-surplus activation on node `[19]`'s strict arm. -/
noncomputable def selectedSparseSurplusActivation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let h1 :=
    (sparseSurplusSurvivorRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .uncompressible) (K .sparseSurplusSurvivor)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.2)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact.1, fact.2⟩)).run
      history (by simp [sparseSurplusSurvivorRow, K_eq_iff])
  let h2 :=
    (sparseSlackSurplusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .sparseSlackSurplus) (fun _input fact => ⟨fact⟩)).run
      h1 (by simp [sparseSlackSurplusRow, K_eq_iff])
  let h3 :=
    (activeSurplusFamilyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .slackIndependent) (K .activeSurplusFamily)
      (by simp [K_eq_iff]) (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run h2 (by
        simp [activeSurplusFamilyRow, sparseSlackSurplusRow,
          sparseSurplusSurvivorRow, K_eq_iff])
  let h4 :=
    (sparsePortActivationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .sparsePortActivation) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.2)
      (fun _input fact => ⟨fact⟩)).run h3 (by
        simp [sparsePortActivationRow, activeSurplusFamilyRow,
          sparseSlackSurplusRow, sparseSurplusSurvivorRow, K_eq_iff])
  exact
    (activeSurplusDemandsRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .sparseSurplusSurvivor) (K .activeSurplusFamily)
      (K .sparsePortActivation) (K .activeSurplusDemands)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run h4 (by
        simp [activeSurplusDemandsRow, sparsePortActivationRow,
          activeSurplusFamilyRow, sparseSlackSurplusRow,
          sparseSurplusSurvivorRow, K_eq_iff])

/-- Node `[21]`, window-package split on node `[19]`'s strict arm. -/
noncomputable def selectedSurplusAboveWindowPackageDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .windowPackageSeparated)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .windowPackageCollided)
      history :=
  windowPackageDichotomy (data := spineData) history
    (K .windowPackageSeparated) (K .windowPackageCollided)
    (fun package => ⟨package⟩)
    (fun collided => ⟨collided⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[125]`--`[128]`, on the strict arm after node `[21]`'s separated package. -/
noncomputable def selectedSeparatedSparseSurplusActivation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let h1 :=
    (sparseSurplusSurvivorRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .uncompressible) (K .sparseSurplusSurvivor)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.2)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact.1, fact.2⟩)).run
      history (by simp [sparseSurplusSurvivorRow, K_eq_iff])
  let h2 :=
    (sparseSlackSurplusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .sparseSlackSurplus) (fun _input fact => ⟨fact⟩)).run
      h1 (by simp [sparseSlackSurplusRow, K_eq_iff])
  let h3 :=
    (activeSurplusFamilyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .slackIndependent) (K .activeSurplusFamily)
      (by simp [K_eq_iff]) (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run h2 (by
        simp [activeSurplusFamilyRow, sparseSlackSurplusRow,
          sparseSurplusSurvivorRow, K_eq_iff])
  let h4 :=
    (sparsePortActivationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .sparsePortActivation) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.2)
      (fun _input fact => ⟨fact⟩)).run h3 (by
        simp [sparsePortActivationRow, activeSurplusFamilyRow,
          sparseSlackSurplusRow, sparseSurplusSurvivorRow, K_eq_iff])
  exact
    (activeSurplusDemandsRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .sparseSurplusSurvivor) (K .activeSurplusFamily)
      (K .sparsePortActivation) (K .activeSurplusDemands)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run h4 (by
        simp [activeSurplusDemandsRow, sparsePortActivationRow,
          activeSurplusFamilyRow, sparseSlackSurplusRow,
          sparseSurplusSurvivorRow, K_eq_iff])

/-- Node `[129]`, baseline spine demand on the strict separated surplus arm. -/
noncomputable def selectedBaselineSpineDemand
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterActivation := selectedSeparatedSparseSurplusActivation history
  exact
    (baselineSpineDemandRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .windowPackageSeparated) (K .baselineSpineDemand)
      (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run afterActivation (by
        simp [baselineSpineDemandRow, selectedSeparatedSparseSurplusActivation,
          K_eq_iff])

/-- Node `[132]`, the sparse-pair routing split after baseline demand. -/
noncomputable def selectedBlockedPairRoutingDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
    (K .sparsePairExit) (K .canonicalBlockerRoute)
    (fun exit => ⟨exit⟩)
    (fun blocker => ⟨blocker⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[125]`--`[132]`, strict separated surplus through the sparse-pair split. -/
noncomputable def selectedStrictSeparatedPairDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      (selectedBaselineSpineDemand history) :=
  selectedBlockedPairRoutingDichotomy (selectedBaselineSpineDemand history)

/-- Node `[133]`, sparse-pair exit closes against the survivor fact. -/
noncomputable def selectedSparsePairExitCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePairExit, K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .sparseSurplusSurvivor) (K .sparsePairExit)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[130]` and `[134]`, canonical pair ledger on the blocker arm. -/
noncomputable def selectedCanonicalPairFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  exact
    (canonicalPairLedgerRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .activeSurplusFamily) (K .sparseSlackSurplus)
      (K .surplusAbove) (K .baselineSpineDemand)
      (K .canonicalBlockerRoute) (K .canonicalPairLedger)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact Coordinate family coordinateSupport =>
        (fact.down Coordinate family coordinateSupport).2)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [canonicalPairLedgerRow, K_eq_iff])

/-- Nodes `[135]` and `[136]`, sparse envelope and capacity-token ledger. -/
noncomputable def selectedCapacityTokenFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterPairs := selectedCanonicalPairFacts history
  exact
    (capacityTokenLedgerRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .canonicalPairLedger) (K .baselineSpineDemand)
      (K .noProperBaseline) (K .tightEndpoint) (K .surplusAbove)
      (K .sparseUpperEnvelope) (K .capacityTokenLedger)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.2.2)
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)
      (fun _input fact => ⟨fact⟩)).run afterPairs (by
        simp [capacityTokenLedgerRow, selectedCanonicalPairFacts, K_eq_iff])

/-- Node `[137]`, coupled role-fibre partition and pressure facts. -/
noncomputable def selectedCoupledFibrePressure
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .roleFibrePartition, K .fibrePressure,
        K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterTokens := selectedCapacityTokenFacts history
  exact
    (coupledFibrePressureRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .canonicalPairLedger) (K .capacityTokenLedger)
      (K .roleFibrePartition) (K .fibrePressure)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down.1)
      (fun _input fact declared =>
        ⟨((fact.down.2.1 declared).some).ledger⟩)
      (fun _input fact => ⟨fact⟩)
      (fun _input fact => ⟨fact⟩)).run afterTokens (by
        simp [coupledFibrePressureRow, selectedCapacityTokenFacts, K_eq_iff])

/-- Node `[137]`, sparse-pressure routing after the coupled pressure row. -/
noncomputable def selectedSparsePressureDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .roleFibrePartition, K .fibrePressure,
        K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .sparsePressureNearCubic)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .sparsePressureOverload)
      history :=
  sparsePressureDichotomy (data := spineData) history
    (K .sparsePressureNearCubic) (K .sparsePressureOverload)
    (fun nearCubic => ⟨nearCubic⟩)
    (fun overload => ⟨overload⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Nodes `[130]`--`[137]`, strict blocker arm through the sparse-pressure split. -/
noncomputable def selectedCanonicalBlockerPressureDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .sparsePressureNearCubic)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .sparsePressureOverload)
      (selectedCoupledFibrePressure history) :=
  selectedSparsePressureDichotomy (selectedCoupledFibrePressure history)

/-- Node `[138]`, near-cubic pressure gives the spine surplus estimate. -/
noncomputable def selectedPressureSpineSurplusEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePressureNearCubic, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .spineSurplusEstimate, K .sparsePressureNearCubic,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  exact
    (spineSurplusEstimateRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .sparsePressureNearCubic) (K .capacityTokenLedger)
      (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.2.2)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [spineSurplusEstimateRow, K_eq_iff])

/-- Node `[138]`, the near-cubic arm closes against strict surplus. -/
noncomputable def selectedPressureNearCubicCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePressureNearCubic, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let afterEstimate := selectedPressureSpineSurplusEstimate history
  let closedHistory :=
    closeIncompatible afterEstimate (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[125]`--`[138]`, strict separated surplus reduced to the overload survivor. -/
noncomputable def selectedStrictSeparatedOverload
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedStrictSeparatedPairDichotomy history with
  | .left exitHistory =>
      exact False.elim (selectedSparsePairExitCloses exitHistory)
  | .right blockerHistory =>
      match selectedCanonicalBlockerPressureDichotomy blockerHistory with
      | .left nearCubicHistory =>
          exact False.elim (selectedPressureNearCubicCloses nearCubicHistory)
      | .right overloadHistory =>
          exact overloadHistory

/-- Node `[139]`, window-token class split on the overload arm. -/
noncomputable def selectedWindowClassDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .windowClassOverload)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .windowClassAbsent)
      history :=
  windowClassDichotomy (data := spineData) history
    (K .windowClassOverload) (K .windowClassAbsent)
    (fun overload => ⟨overload⟩)
    (fun absent => ⟨absent⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[140]`, window-incidence homogeneous class audit. -/
noncomputable def selectedWindowIncidenceAudit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .windowIncidenceAudit, K .quantitativeOverload,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  exact
    (classAuditRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      .windowIncidence (K .windowIncidenceAudit) (K .quantitativeOverload)
      (by simp [K_eq_iff])
      (fun _input fact => ⟨fact⟩)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [classAuditRow, K_eq_iff])

/-- Node `[141]`, remainder-token class split after the window-negative arm. -/
noncomputable def selectedRemainderClassDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderClassOverload)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .remainderClassAbsent)
      history :=
  remainderClassDichotomy (data := spineData) history
    (K .remainderClassOverload) (K .remainderClassAbsent)
    (fun overload => ⟨overload⟩)
    (fun absent => ⟨absent⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[142]`, remainder-surplus homogeneous class audit. -/
noncomputable def selectedRemainderSurplusAudit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .remainderSurplusAudit, K .quantitativeOverload,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  exact
    (classAuditRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      .remainderSurplus (K .remainderSurplusAudit) (K .quantitativeOverload)
      (by simp [K_eq_iff])
      (fun _input fact => ⟨fact⟩)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [classAuditRow, K_eq_iff])

/-- Node `[143]`, primitive-carrier fall-through audit. -/
noncomputable def selectedPrimitiveCarrierAudit
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .primitiveClassOverload, K .primitiveCarrierAudit,
        K .quantitativeOverload, K .remainderClassAbsent,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  exact
    (primitiveCarrierAuditRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .sparsePressureOverload) (K .windowClassAbsent)
      (K .remainderClassAbsent) (K .primitiveClassOverload)
      (K .primitiveCarrierAudit) (K .quantitativeOverload)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)
      (fun _input fact => ⟨fact⟩)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [primitiveCarrierAuditRow, K_eq_iff])

/-- Node `[144]`, homogeneous caps split after the window class audit. -/
noncomputable def selectedWindowHomogeneousCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowIncidenceAudit, K .quantitativeOverload,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
      history :=
  homogeneousCapsDichotomy (data := spineData) history
    (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
    (fun caps => ⟨caps⟩)
    (fun pattern => ⟨pattern⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[144]`, cap-close pressure on the window audit caps arm. -/
noncomputable def selectedWindowHomogeneousCapsEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .windowIncidenceAudit,
        K .quantitativeOverload, K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .spineSurplusEstimate, K .homogeneousBottleneck,
        K .homogeneousCapsHold, K .windowIncidenceAudit,
        K .quantitativeOverload, K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterClose :=
    (homogeneousBottleneckRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .homogeneousCapsHold) (K .sparseSlackSurplus)
      (K .homogeneousBottleneck)
      (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [homogeneousBottleneckRow, K_eq_iff])
  exact
    (homogeneousSpineSurplusEstimateRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .homogeneousBottleneck) (K .capacityTokenLedger)
      (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.2.2)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run afterClose (by
        simp [homogeneousSpineSurplusEstimateRow, homogeneousBottleneckRow,
          K_eq_iff])

/-- Node `[144]`, the window audit caps arm closes against strict surplus. -/
noncomputable def selectedWindowHomogeneousCapsCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .windowIncidenceAudit,
        K .quantitativeOverload, K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let afterEstimate := selectedWindowHomogeneousCapsEstimate history
  let closedHistory :=
    closeIncompatible afterEstimate (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[144]`, bottleneck routing fact on the window audit pattern arm. -/
noncomputable def selectedWindowBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .windowIncidenceAudit,
        K .quantitativeOverload, K .windowClassOverload,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bottleneckRouting, K .homogeneousBottleneckPattern,
        K .windowIncidenceAudit, K .quantitativeOverload,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  exact
    (bottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .uncompressible) (K .sparseSurplusSurvivor)
      (K .homogeneousBottleneckPattern) (K .bottleneckRouting)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [bottleneckRoutingRow, K_eq_iff])

/-- Node `[144]`, homogeneous caps split after the remainder class audit. -/
noncomputable def selectedRemainderHomogeneousCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderSurplusAudit, K .quantitativeOverload,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      history :=
  homogeneousCapsDichotomy (data := spineData) history
    (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
    (fun caps => ⟨caps⟩)
    (fun pattern => ⟨pattern⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[144]`, cap-close pressure on the remainder audit caps arm. -/
noncomputable def selectedRemainderHomogeneousCapsEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .remainderSurplusAudit,
        K .quantitativeOverload, K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .spineSurplusEstimate, K .homogeneousBottleneck,
        K .homogeneousCapsHold, K .remainderSurplusAudit,
        K .quantitativeOverload, K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let afterClose :=
    (homogeneousBottleneckRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .homogeneousCapsHold) (K .sparseSlackSurplus)
      (K .homogeneousBottleneck)
      (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [homogeneousBottleneckRow, K_eq_iff])
  exact
    (homogeneousSpineSurplusEstimateRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .homogeneousBottleneck) (K .capacityTokenLedger)
      (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.2.2)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run afterClose (by
        simp [homogeneousSpineSurplusEstimateRow, homogeneousBottleneckRow,
          K_eq_iff])

/-- Node `[144]`, the remainder audit caps arm closes against strict surplus. -/
noncomputable def selectedRemainderHomogeneousCapsCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .remainderSurplusAudit,
        K .quantitativeOverload, K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let afterEstimate := selectedRemainderHomogeneousCapsEstimate history
  let closedHistory :=
    closeIncompatible afterEstimate (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[144]`, bottleneck routing fact on the remainder audit pattern arm. -/
noncomputable def selectedRemainderBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .remainderSurplusAudit,
        K .quantitativeOverload, K .remainderClassOverload,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bottleneckRouting, K .homogeneousBottleneckPattern,
        K .remainderSurplusAudit, K .quantitativeOverload,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  exact
    (bottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .uncompressible) (K .sparseSurplusSurvivor)
      (K .homogeneousBottleneckPattern) (K .bottleneckRouting)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [bottleneckRoutingRow, K_eq_iff])

/-- Node `[144]`, homogeneous caps split after the primitive class audit. -/
noncomputable def selectedPrimitiveHomogeneousCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .primitiveClassOverload, K .primitiveCarrierAudit,
        K .quantitativeOverload, K .remainderClassAbsent,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
      history :=
  homogeneousCapsDichotomy (data := spineData) history
    (K .homogeneousCapsHold) (K .homogeneousBottleneckPattern)
    (fun caps => ⟨caps⟩)
    (fun pattern => ⟨pattern⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[144]`, cap-close pressure on the primitive audit caps arm. -/
noncomputable def selectedPrimitiveHomogeneousCapsEstimate
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .primitiveClassOverload,
        K .primitiveCarrierAudit, K .quantitativeOverload,
        K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .spineSurplusEstimate, K .homogeneousBottleneck,
        K .homogeneousCapsHold, K .primitiveClassOverload,
        K .primitiveCarrierAudit, K .quantitativeOverload,
        K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  let afterClose :=
    (homogeneousBottleneckRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .homogeneousCapsHold) (K .sparseSlackSurplus)
      (K .homogeneousBottleneck)
      (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [homogeneousBottleneckRow, K_eq_iff])
  exact
    (homogeneousSpineSurplusEstimateRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .homogeneousBottleneck) (K .capacityTokenLedger)
      (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff]) (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.2.2)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run afterClose (by
        simp [homogeneousSpineSurplusEstimateRow, homogeneousBottleneckRow,
          K_eq_iff])

/-- Node `[144]`, the primitive audit caps arm closes against strict surplus. -/
noncomputable def selectedPrimitiveHomogeneousCapsCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousCapsHold, K .primitiveClassOverload,
        K .primitiveCarrierAudit, K .quantitativeOverload,
        K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let afterEstimate := selectedPrimitiveHomogeneousCapsEstimate history
  let closedHistory :=
    closeIncompatible afterEstimate (K .surplusAbove) (K .spineSurplusEstimate)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[144]`, bottleneck routing fact on the primitive audit pattern arm. -/
noncomputable def selectedPrimitiveBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .homogeneousBottleneckPattern, K .primitiveClassOverload,
        K .primitiveCarrierAudit, K .quantitativeOverload,
        K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bottleneckRouting, K .homogeneousBottleneckPattern,
        K .primitiveClassOverload, K .primitiveCarrierAudit,
        K .quantitativeOverload, K .remainderClassAbsent,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  exact
    (bottleneckRoutingRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)
      (K .selection) (K .uncompressible) (K .sparseSurplusSurvivor)
      (K .homogeneousBottleneckPattern) (K .bottleneckRouting)
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (fun _input fact => fact.down)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down.1)
      (fun _input fact => fact.down)
      (fun _input fact => ⟨fact⟩)).run history (by
        simp [bottleneckRoutingRow, K_eq_iff])

/-- Nodes `[140]` and `[144]`, window-overload audit through homogeneous caps. -/
noncomputable def selectedWindowOverloadCapsDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      [K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bottleneckRouting, K .homogeneousBottleneckPattern,
        K .windowIncidenceAudit, K .quantitativeOverload,
        K .windowClassOverload, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedWindowOverloadCapsDichotomy history with
  | .left capsHistory =>
      exact False.elim (selectedWindowHomogeneousCapsCloses capsHistory)
  | .right patternHistory =>
      exact selectedWindowBottleneckRouting patternHistory

/-- Nodes `[142]`--`[144]`, remainder-overload arm reduced to bottleneck routing. -/
noncomputable def selectedRemainderOverloadBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bottleneckRouting, K .homogeneousBottleneckPattern,
        K .remainderSurplusAudit, K .quantitativeOverload,
        K .remainderClassOverload, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] := by
  match selectedRemainderOverloadCapsDichotomy history with
  | .left capsHistory =>
      exact False.elim (selectedRemainderHomogeneousCapsCloses capsHistory)
  | .right patternHistory =>
      exact selectedRemainderBottleneckRouting patternHistory

/-- Nodes `[143]`--`[144]`, primitive-overload arm reduced to bottleneck routing. -/
noncomputable def selectedPrimitiveOverloadBottleneckRouting
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderClassAbsent, K .windowClassAbsent,
        K .sparsePressureOverload, K .roleFibrePartition,
        K .fibrePressure, K .sparseUpperEnvelope, K .capacityTokenLedger,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .sparseSurplusSurvivor,
        K .windowPackageSeparated, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .bottleneckRouting, K .homogeneousBottleneckPattern,
        K .primitiveClassOverload, K .primitiveCarrierAudit,
        K .quantitativeOverload, K .remainderClassAbsent,
        K .windowClassAbsent, K .sparsePressureOverload,
        K .roleFibrePartition, K .fibrePressure, K .sparseUpperEnvelope,
        K .capacityTokenLedger, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .sparseSurplusSurvivor, K .windowPackageSeparated,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  match selectedPrimitiveOverloadCapsDichotomy history with
  | .left capsHistory =>
      exact False.elim (selectedPrimitiveHomogeneousCapsCloses capsHistory)
  | .right patternHistory =>
      exact selectedPrimitiveBottleneckRouting patternHistory

/-- Node `[21]`, on the near-cubic arm of node `[19]`. -/
noncomputable def selectedWindowPackageDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .windowPackageSeparated)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .windowPackageCollided)
      history :=
  windowPackageDichotomy (data := spineData) history
    (K .windowPackageSeparated) (K .windowPackageCollided)
    (fun package => ⟨package⟩)
    (fun collided => ⟨collided⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[21]`'s finite barrier split, on the separated arm. -/
noncomputable def selectedBarrierDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .barrierCap)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .barrierOverflow)
      history :=
  barrierEnumerationDichotomy (data := spineData) history
    (K .barrierCap) (K .barrierOverflow)
    (fun cap => ⟨cap⟩)
    (fun overflow => ⟨overflow⟩)
    (by simp [K_eq_iff])
    (by simp [K_eq_iff])

/-- Node `[23]`, closing the barrier-overflow arm of the separated package. -/
noncomputable def selectedBarrierOverflowCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierOverflow, K .windowPackageSeparated, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .windowPackageSeparated) (K .barrierOverflow)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[22]`--`[24]`, after the barrier cap arm. -/
noncomputable def selectedDensityBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .windowPackageSeparated, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (densityBudget (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [densityBudget, K_eq_iff])

/-- Nodes `[25]`--`[31]`, after the density cap path. -/
noncomputable def selectedCompletedSpinePrefix
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .windowPackageSeparated, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] := by
  let h1 := selectedDensityBudget history
  let h2 :=
    (remainderNormalization (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h1 (by simp [remainderNormalization, selectedDensityBudget, K_eq_iff])
  let h3 :=
    (boundaryDemand (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h2 (by
        simp [boundaryDemand, remainderNormalization, selectedDensityBudget,
          K_eq_iff])
  let h4 :=
    (wedgeSupply (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h3 (by
        simp [wedgeSupply, boundaryDemand, remainderNormalization,
          selectedDensityBudget, K_eq_iff])
  exact
    (curvatureTargetRank (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      h4 (by
        simp [curvatureTargetRank, wedgeSupply, boundaryDemand,
          remainderNormalization, selectedDensityBudget, K_eq_iff])

/-- Node `[32]`, run on the completed near-cubic prefix. -/
noncomputable def selectedCurvatureRankDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .windowPackageSeparated, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
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
    (K .curvatureTargetRank) (K .curvatureRankDrop) (K .curvatureFullRank)
    (fun fact => fact.down)
    (fun drop => ⟨drop⟩)
    (fun full => ⟨full⟩)
    (by simp [selectedCompletedSpinePrefix, K_eq_iff])
    (by simp [selectedCompletedSpinePrefix, K_eq_iff])

/-- Nodes `[22]`--`[32]`, barrier-cap arm through the curvature-rank split. -/
noncomputable def selectedBarrierCapCurvatureRankDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .barrierCap, K .windowPackageSeparated, K .surplusAtOrBelow,
        K .localAlgebra, K .maximalPacking, K .uncompressible,
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
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let afterDependence :=
    (branchDependence (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [branchDependence, K_eq_iff])
  let contextDecision :=
    contextValidityDichotomy (data := spineData) afterDependence
      (K .contextDefect) (K .contextUniversal)
      (fun defect => ⟨defect⟩)
      (fun universal => ⟨universal⟩)
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
          (K .branchDependence) (K .contextUniversal)
          (K .atomCompression) (K .delocalizedSupport)
          (fun fact => fact.down)
          (fun fact => fact.down)
          (fun compression => ⟨compression⟩)
          (fun delocalized => ⟨delocalized⟩)
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
              (K .delocalizedSupport) (K .properDelocalization)
              (K .globalDelocalization)
              (fun fact => fact.down)
              (fun proper => ⟨proper⟩)
              (fun global => ⟨global⟩)
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
              let afterBarrier :=
                (globalBarrier (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run globalHistory (by
                    simp [globalBarrier, branchDependence, K_eq_iff])
              let closedHistory :=
                closeIncompatible afterBarrier (K .selection)
                (K .globalBarrier) (by
                    simp [globalBarrier, branchDependence, K_eq_iff])
              exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[21]`--`[46]`, separated near-cubic arm reduced to full rank. -/
noncomputable def selectedSeparatedFullRank
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (forcedCurvatureCost (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [forcedCurvatureCost, K_eq_iff])

/-- Node `[50]`, the entropy split after forced curvature cost. -/
noncomputable def selectedRemainderEntropyDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      [K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
    (K .entropyCapActive) (K .largeBudgetResidual)
    (fun active => ⟨active⟩)
    (fun large => ⟨Or.inl large⟩)
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
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[54]`, closing the active entropy-cap arm. -/
noncomputable def selectedEntropyCapActiveCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .entropyCapActive, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .windowPackageSeparated)
      (K .entropyCapActive) (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[55]`, on the low-entropy arm. -/
noncomputable def selectedLowEntropyLargeBudget
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (lowEntropyLargeBudget (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [lowEntropyLargeBudget, K_eq_iff])

/-- Node `[60]`, the order-regime split on the low-entropy Residual C arm. -/
noncomputable def selectedLowEntropyNetChargeOrderDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      (selectedLowEntropyLargeBudget history) :=
  netChargeOrderDichotomy (data := spineData)
    (selectedLowEntropyLargeBudget history)
    (K .netChargeLarge) (K .netChargeSmall)
    (fun large => ⟨large⟩)
    (fun small => ⟨small⟩)
    (by simp [selectedLowEntropyLargeBudget, K_eq_iff])
    (by simp [selectedLowEntropyLargeBudget, K_eq_iff])

/-- Node `[60]`, the net-charge cap on the large low-entropy arm. -/
noncomputable def selectedLowEntropyNetChargeCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      [K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
      [K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
    (K .netChargeNonNegative) (K .netChargeNegative)
    (fun nonNegative => ⟨nonNegative⟩)
    (fun negative => ⟨negative⟩)
    (by simp [selectedLowEntropyNetChargeLocalization,
      selectedLowEntropyNetChargeCap, K_eq_iff])
    (by simp [selectedLowEntropyNetChargeLocalization,
      selectedLowEntropyNetChargeCap, K_eq_iff])

/-- Node `[60]`, closing the nonnegative low-entropy arm after recording window pressure. -/
noncomputable def selectedLowEntropyNetChargeNonNegativeCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNonNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let pressure :=
    (windowJoinPressure (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [windowJoinPressure, K_eq_iff])
  let closedHistory :=
    closeIncompatible pressure (K .netChargeCap) (K .netChargeNonNegative)
      (by simp [windowJoinPressure, K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[61]`, selecting the negative support on the low-entropy arm. -/
noncomputable def selectedLowEntropyNegativeSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[60]`, the order-regime split on the high-entropy Residual C arm. -/
noncomputable def selectedHighEntropyNetChargeOrderDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[60]`, the net-charge cap on the large high-entropy arm. -/
noncomputable def selectedHighEntropyNetChargeCap
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (netChargeCap (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [netChargeCap, K_eq_iff])

/-- Nodes `[57]`--`[58]`, net-charge localization on the high-entropy arm. -/
noncomputable def selectedHighEntropyNetChargeLocalization
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
      [K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
    (K .netChargeNonNegative) (K .netChargeNegative)
    (fun nonNegative => ⟨nonNegative⟩)
    (fun negative => ⟨negative⟩)
    (by simp [selectedHighEntropyNetChargeLocalization,
      selectedHighEntropyNetChargeCap, K_eq_iff])
    (by simp [selectedHighEntropyNetChargeLocalization,
      selectedHighEntropyNetChargeCap, K_eq_iff])

/-- Node `[60]`, closing the nonnegative high-entropy arm after recording window pressure. -/
noncomputable def selectedHighEntropyNetChargeNonNegativeCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNonNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let pressure :=
    (windowJoinPressure (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [windowJoinPressure, K_eq_iff])
  let closedHistory :=
    closeIncompatible pressure (K .netChargeCap) (K .netChargeNonNegative)
      (by simp [windowJoinPressure, K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[61]`, selecting the negative support on the high-entropy arm. -/
noncomputable def selectedHighEntropyNegativeSupport
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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

/-- Node `[68]`, normal form on the low-entropy Type B arm. -/
noncomputable def selectedLowEntropyTypeBNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection] :=
  (highCentreNormalForm (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [highCentreNormalForm, K_eq_iff])

/-- Node `[68]`, heavy-centre split on the low-entropy Type B arm. -/
noncomputable def selectedLowEntropyTypeBDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBHeavyCentre)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDegreeFourCentres)
      (selectedLowEntropyTypeBNormalForm history) :=
  heavyCentreDichotomy (data := spineData)
    (selectedLowEntropyTypeBNormalForm history)
    (K .typeBHighSurplus) (K .typeBHeavyCentre)
    (K .typeBDegreeFourCentres)
    (fun fact => fact.down)
    (fun heavy => ⟨heavy⟩)
    (fun degreeFour => ⟨degreeFour⟩)
    (by simp [selectedLowEntropyTypeBNormalForm, K_eq_iff])
    (by simp [selectedLowEntropyTypeBNormalForm, K_eq_iff])

/-- Node `[68]`, normal form on the high-entropy Type B arm. -/
noncomputable def selectedHighEntropyTypeBNormalForm
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection] :=
  (highCentreNormalForm (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [highCentreNormalForm, K_eq_iff])

/-- Node `[68]`, heavy-centre split on the high-entropy Type B arm. -/
noncomputable def selectedHighEntropyTypeBDegreeDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBHeavyCentre)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBDegreeFourCentres)
      (selectedHighEntropyTypeBNormalForm history) :=
  heavyCentreDichotomy (data := spineData)
    (selectedHighEntropyTypeBNormalForm history)
    (K .typeBHighSurplus) (K .typeBHeavyCentre)
    (K .typeBDegreeFourCentres)
    (fun fact => fact.down)
    (fun heavy => ⟨heavy⟩)
    (fun degreeFour => ⟨degreeFour⟩)
    (by simp [selectedHighEntropyTypeBNormalForm, K_eq_iff])
    (by simp [selectedHighEntropyTypeBNormalForm, K_eq_iff])

/-- Node `[69]`, local heavy-centre dichotomy on the low-entropy Type B heavy arm. -/
noncomputable def selectedLowEntropyTypeBLocalDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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

/-- Node `[75]`, bridge mass on the low-entropy fan-certificate residual arm. -/
noncomputable def selectedLowEntropyTypeBCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .selection) (K .typeBDirectCycle)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[72]`, B2 assignment split on the low-entropy Type B heavy path. -/
noncomputable def selectedLowEntropyTypeBB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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

/-- Node `[73]`, bridge mass on the low-entropy Type B heavy overlap-obstruction arm. -/
noncomputable def selectedLowEntropyTypeBOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[75]`, bridge mass on the high-entropy fan-certificate residual arm. -/
noncomputable def selectedHighEntropyTypeBCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .selection) (K .typeBDirectCycle)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[72]`, B2 assignment split on the high-entropy Type B heavy path. -/
noncomputable def selectedHighEntropyTypeBB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[73]`, bridge mass on the high-entropy Type B heavy overlap-obstruction arm. -/
noncomputable def selectedHighEntropyTypeBOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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

/-- Node `[84]`, bridge mass on the low-entropy degree-four certificate-residual arm. -/
noncomputable def selectedLowEntropyDegreeFourCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .selection) (K .typeBDirectCycle)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[81]`, B2 assignment split on the low-entropy degree-four path. -/
noncomputable def selectedLowEntropyDegreeFourB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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

/-- Node `[83]`, bridge mass on the low-entropy degree-four overlap-obstruction arm. -/
noncomputable def selectedLowEntropyDegreeFourOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[84]`, bridge mass on the high-entropy degree-four certificate-residual arm. -/
noncomputable def selectedHighEntropyDegreeFourCertificateResidualMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .fanCertificateResidual, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .fanCertificateResidual,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let closedHistory :=
    closeIncompatible history (K .selection) (K .typeBDirectCycle)
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Node `[81]`, B2 assignment split on the high-entropy degree-four path. -/
noncomputable def selectedHighEntropyDegreeFourB2AssignmentDichotomy
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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

/-- Node `[83]`, bridge mass on the high-entropy degree-four overlap-obstruction arm. -/
noncomputable def selectedHighEntropyDegreeFourOverlapObstructionMass
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBOverlapObstruction, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBBridgeMass, K .typeBOverlapObstruction,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBRemainingCoreNonnegative)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedLowEntropyTypeBB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedLowEntropyTypeBB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBRemainingCoreNonnegative)
    (K .typeBExclusionResidual)
    (fun core => ⟨core⟩)
    (fun residual => ⟨residual⟩)
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
      [K .typeBRemainingCoreNonnegative, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let excluded :=
    (typeBExcluded (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [typeBExcluded, K_eq_iff])
  let closedHistory :=
    closeIncompatible excluded (K .typeBDisjointLedger) (K .typeBExcluded)
      (by simp [typeBExcluded, K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[74]`--`[76]`, B2-success charge ledger on the high-entropy heavy path. -/
noncomputable def selectedHighEntropyTypeBB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .fanCertificateCap,
        K .typeBLocalDichotomy, K .typeBHeavyCentre,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBRemainingCoreNonnegative)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedHighEntropyTypeBB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedHighEntropyTypeBB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBRemainingCoreNonnegative)
    (K .typeBExclusionResidual)
    (fun core => ⟨core⟩)
    (fun residual => ⟨residual⟩)
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
      [K .typeBRemainingCoreNonnegative, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .fanCertificateCap, K .typeBLocalDichotomy,
        K .typeBHeavyCentre, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let excluded :=
    (typeBExcluded (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [typeBExcluded, K_eq_iff])
  let closedHistory :=
    closeIncompatible excluded (K .typeBDisjointLedger) (K .typeBExcluded)
      (by simp [typeBExcluded, K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[82]`--`[85]`, B2-success charge ledger on the low-entropy degree-four path. -/
noncomputable def selectedLowEntropyDegreeFourB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .remainderEntropyLow, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBRemainingCoreNonnegative)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedLowEntropyDegreeFourB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedLowEntropyDegreeFourB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBRemainingCoreNonnegative)
    (K .typeBExclusionResidual)
    (fun core => ⟨core⟩)
    (fun residual => ⟨residual⟩)
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
      [K .typeBRemainingCoreNonnegative, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .remainderEntropyLow,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) : False := by
  let excluded :=
    (typeBExcluded (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [typeBExcluded, K_eq_iff])
  let closedHistory :=
    closeIncompatible excluded (K .typeBDisjointLedger) (K .typeBExcluded)
      (by simp [typeBExcluded, K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Nodes `[82]`--`[85]`, B2-success charge ledger on the high-entropy degree-four path. -/
noncomputable def selectedHighEntropyDegreeFourB2ExclusionCharge
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .typeBExclusionCharge, K .typeBSelectedFanCharge,
        K .typeBDisjointLedger, K .typeBHybridEntry,
        K .typeBB2Choice, K .typeBDirectCycleFree,
        K .fanCertificateMarked, K .typeBDegreeFourProfile,
        K .fanCertificateCap, K .typeBDegreeFourCentres,
        K .highCentreNormalForm, K .typeBHighSurplus,
        K .negativeSupport, K .netChargeNegative, K .netChargeLocalization,
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
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
        K .netChargeCap, K .netChargeLarge, K .largeBudgetResidual,
        K .entropyPackageDemand, K .remainderEntropyHigh,
        K .forcedCurvatureCost, K .curvatureFullRank,
        K .curvatureTargetRank, K .wedgeSupply, K .curvatureDemandFloor,
        K .boundaryDemand, K .stubSupply, K .remainderNormalized,
        K .densityCap, K .barrierCap, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .selection]) :
    Decision
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBRemainingCoreNonnegative)
      (K (BranchState := BranchState)
        (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
        (presentation := erdosReceiverLoadProfile) (data := spineData)
        .typeBExclusionResidual)
      (selectedHighEntropyDegreeFourB2ExclusionCharge history) :=
  typeBExclusionDichotomy (data := spineData)
    (selectedHighEntropyDegreeFourB2ExclusionCharge history)
    (K .typeBDisjointLedger) (K .typeBRemainingCoreNonnegative)
    (K .typeBExclusionResidual)
    (fun core => ⟨core⟩)
    (fun residual => ⟨residual⟩)
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
      [K .typeBRemainingCoreNonnegative, K .typeBExclusionCharge,
        K .typeBSelectedFanCharge, K .typeBDisjointLedger,
        K .typeBHybridEntry, K .typeBB2Choice,
        K .typeBDirectCycleFree, K .fanCertificateMarked,
        K .typeBDegreeFourProfile, K .fanCertificateCap,
        K .typeBDegreeFourCentres, K .highCentreNormalForm,
        K .typeBHighSurplus, K .negativeSupport, K .netChargeNegative,
        K .netChargeLocalization, K .netChargeCap, K .netChargeLarge,
        K .largeBudgetResidual, K .entropyPackageDemand,
        K .remainderEntropyHigh, K .forcedCurvatureCost,
        K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
        K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
        K .remainderNormalized, K .densityCap, K .barrierCap,
        K .windowPackageSeparated, K .surplusAtOrBelow, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
        K .selection]) : False := by
  let excluded :=
    (typeBExcluded (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by simp [typeBExcluded, K_eq_iff])
  let closedHistory :=
    closeIncompatible excluded (K .typeBDisjointLedger) (K .typeBExcluded)
      (by simp [typeBExcluded, K_eq_iff])
  exact closedHistory.elimClosed (by infer_instance)

/-- Cold corridor closure, once the selected ledger carries the cold terminal residual. -/
noncomputable def selectedColdCorridorCloses
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldTerminalResidual, K .route8TerminalNoGo, K .typeBExcluded,
        K .sparsePressureNearCubic, K .spineSurplusEstimate,
        K .sparseSurplusSurvivor, K .negativeSupport, K .largeBudgetResidual,
        K .densityCap, K .windowPackageCollided, K .uncompressible,
        K .selection]) : False := by
  let closedHistory :=
    runCold (data := spineData) history
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by
    dsimp [coldKeys]
    infer_instance)

/-- Node `[125]`, appended on the cold corridor prefix before the cold oval. -/
noncomputable def selectedColdSparseSurplusSurvivor
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldTerminalResidual, K .route8TerminalNoGo, K .typeBExcluded,
        K .sparsePressureNearCubic, K .spineSurplusEstimate,
        K .negativeSupport, K .largeBudgetResidual, K .densityCap,
        K .windowPackageCollided, K .uncompressible, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .coldTerminalResidual,
        K .route8TerminalNoGo, K .typeBExcluded, K .sparsePressureNearCubic,
        K .spineSurplusEstimate, K .negativeSupport, K .largeBudgetResidual,
        K .densityCap, K .windowPackageCollided, K .uncompressible,
        K .selection] :=
  (sparseSurplusSurvivorRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)
    (K .selection) (K .uncompressible) (K .sparseSurplusSurvivor)
    (by simp [K_eq_iff]) (by simp [K_eq_iff])
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.2)
    (fun _input fact => fact.down)
    (fun _input fact => ⟨fact.1, fact.2⟩)).run
    history (by simp [sparseSurplusSurvivorRow, K_eq_iff])

/-- Cold corridor closure after appending node `[125]` on the same ledger. -/
noncomputable def selectedColdCorridorClosesFromTerminal
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .coldTerminalResidual, K .route8TerminalNoGo, K .typeBExcluded,
        K .sparsePressureNearCubic, K .spineSurplusEstimate,
        K .negativeSupport, K .largeBudgetResidual, K .densityCap,
        K .windowPackageCollided, K .uncompressible, K .selection]) : False := by
  let withSurvivor := selectedColdSparseSurplusSurvivor history
  let closedHistory :=
    runCold (data := spineData) withSurvivor
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff]) (by simp [K_eq_iff])
      (by simp [K_eq_iff])
  exact closedHistory.elimClosed (by
    dsimp [coldKeys]
    infer_instance)

/-- The exact selected-residual closure contract consumed by final assembly. -/
noncomputable abbrev SelectedResidualCloses : Prop :=
  ∀ {selected : EGInput.{u}},
    ExactLedger EGInput.{u} selected [EGSelectionKey] → False

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
theorem target_closure_of_selectedResidualCloses
    (selectedResidualCloses : SelectedResidualCloses.{u}) :
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
    exact (selectedResidualCloses (selected := selected) history).elim

/-- Final public theorem, once the exact-ledger selected residual closure has
been assembled from the rows. -/
theorem erdos_64_of_selectedResidualCloses
    (selectedResidualCloses : SelectedResidualCloses.{u}) :
    OfficialStatement.{u} :=
  EGTarget.target_to_statement
    (target_closure_of_selectedResidualCloses selectedResidualCloses)

end HypostructureErdos64EG
