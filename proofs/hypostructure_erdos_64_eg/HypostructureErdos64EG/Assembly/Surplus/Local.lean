import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppression
import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppressionSafe
import Hypostructure.Graph.Strategy.SpineRows.SingleOpenPortSuppressionWitness
import Hypostructure.Graph.Strategy.SpineRows.SuppressedFamilyCriticalCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows
import Hypostructure.Graph.Strategy.SurplusRows
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Surplus / Local

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Nodes `[126]`--`[128]`, sparse-surplus activation on node `[125]`'s
unchanged literal survivor residual. -/
-- EG-NODE [126] sparse envelope: \(m\le2n-2\), \(\sigma=n-6-2\lambda\)
-- EG-NODE [127] excess-port extraction: \(\mathcal A=\mathcal P_{\rm exc}\), \(|\mathcal A|=\sigma(G)\)
-- EG-NODE [128] canonical activation: returns \(R_p\); open \(Q_p\); triangular response
noncomputable def selectedSparseSurplusActivation
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
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
-- EG-NODE [129] full active family and baseline: \(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)
noncomputable def selectedBaselineSpineDemand
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
        K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
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
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
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
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
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
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
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
-- EG-NODE [134] canonical blocker ledger: each blocked pair gets one \(B_\pi\) and one capacity token
noncomputable def selectedCanonicalPairFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
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
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
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
-- EG-NODE [135] exact window-join load: \(e(R,W)+2e_\times(W)=15p_{13}+\sigma_W\)
noncomputable def selectedExactWindowJoinPressure
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection] :=
  (exactWindowJoinPressureRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run history (by
      simp [exactWindowJoinPressureRow, K_eq_iff])

/-- Node `[136]`, capacity tokens on the literal `[135]` residual. -/
-- EG-NODE [136] tokenized blocked-pair ledger: \(|\Pi_{\rm blk}|=\sum_{C,t,r}\ell(t,r)\), supplies \(15p_{13}+\sigma_W,\sigma_R,4n+2\sigma\)
noncomputable def selectedCapacityTokenFacts
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .sparseUpperEnvelope, K .canonicalPairLedger,
        K .canonicalBlockerRoute, K .dependentPairFamily,
        K .baselineSpineDemand, K .activeSurplusDemands,
        K .sparsePortActivation, K .activeSurplusFamily,
        K .sparseSlackSurplus, K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression, K .sparseSurplusSurvivor,
        K .surplusAbove, K .localAlgebra, K .maximalPacking,
        K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .capacityTokenLedger, K .sparseUpperEnvelope,
        K .canonicalPairLedger, K .canonicalBlockerRoute,
        K .dependentPairFamily, K .baselineSpineDemand,
        K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
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
-- EG-NODE [138] no coupled overload: explicit quadratic bound on \(\sigma\); near-cubic spine
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
    [FactKeys.Has (K .bridgeless) known]
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
    [FactKeys.Has (K .highCentreNormalForm) known]
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

end HypostructureErdos64EG
