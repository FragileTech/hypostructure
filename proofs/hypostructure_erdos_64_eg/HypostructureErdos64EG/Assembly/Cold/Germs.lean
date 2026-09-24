import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.ColdCorridorRows
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Cold / Germs

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Node `[150]`: append the cold-mass inequality to `[148]`'s literal
no-residual. -/
-- EG-NODE [150] hot failure forces cold mass: \(C\ge(\theta-\theta_{\rm win})n-o(n)\)
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
-- EG-NODE [151] all but \(o(n)\) cold windows ambient-cubic
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
-- EG-NODE [152] selected interior-stub excess: \(b_{\rm int}(\mathfrak S_{\rm cold})\ge9C-o(n)\)
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
-- EG-NODE [153] linear first-failure extraction? \(N_{\rm conf}\ge9C/D_{\rm cold}-o(n)\)
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
-- EG-NODE [154] bounded configuration case?
-- EG-NODE [155] G1: power-of-two cycle
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

end HypostructureErdos64EG
