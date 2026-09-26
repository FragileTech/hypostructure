import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppression
import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppressionSafe
import Hypostructure.Graph.Strategy.SpineRows.SingleOpenPortSuppressionWitness
import Hypostructure.Graph.Strategy.SpineRows.SuppressedFamilyCriticalCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SameTokenBottleneckRouting
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SameTokenTypeBFanEntry
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.HomogeneousBottleneckAudit
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.HomogeneousCapsClose
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.FibrePressure
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairFailureOverlap
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairOverlapSystem
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairPowerOfTwoCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.PairSystemOutcome
import Hypostructure.Graph.Strategy.SurplusRows
import HypostructureErdos64EG.Assembly.Surplus.Boundary

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
        K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection]) :
    ExactLedger EGInput.{u} selected
      [K .activeSurplusDemands, K .sparsePortActivation,
        K .activeSurplusFamily, K .sparseSlackSurplus,
        K .suppressedFamilyCriticalCycle,
        K .singleOpenPortSuppressionWitness, K .openPortSuppressionSafe,
        K .openPortSuppression,
        K .sparseSurplusSurvivor, K .surplusAbove, K .localAlgebra,
        K .maximalPacking, K .windowPresent, K .uncompressible, K .replacementExclusion, K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint, K .tightEndpoint,
        K .slackIndependent, K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline,
        K .selection] := by
  let suppressionDefined :=
    (openPortSuppressionRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  let suppressionSafe :=
    (openPortSuppressionSafeRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      suppressionDefined (by
        key_fresh)
  let singleSuppressionWitnessed :=
    (singleOpenPortSuppressionWitnessRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      suppressionSafe (by
        key_fresh)
  let familyCritical :=
    (suppressedFamilyCriticalCycleRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      singleSuppressionWitnessed (by
        key_fresh)
  let h2 :=
    (sparseSlackSurplusRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      familyCritical (by
        key_fresh)
  let h3 :=
    (activeSurplusFamilyRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h2 (by
        key_fresh)
  let h4 :=
    (sparsePortActivationRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h3 (by
        key_fresh)
  exact
    (activeSurplusDemandsRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run h4 (by
        key_fresh)

/-- Nodes `[178]`--`[180]`, the pair-code chain on any ledger that already
carries the node-`[178]` first failure `K .pairOverlapFirstFailure` (from the
free side of `[131]` or of `[137]`).  Each paper test is a `Decision`; each
uncovered implication is retained at the open node `[182]`, each covered Type B
alternative returns with its own `[179]`/`[180]` source key, and the
full-modulus arithmetic arm closes against node `[1]` through the framework. -/
-- EG-NODE [178] pair-code unrealized residual: conditional factorization gives a minimal connected pair overlap obstruction
-- EG-NODE [179] covered uncrossing: target/sparse-exit/Type B, or a graph-realized serial demand system
-- EG-NODE [180] covered increment split: periodic sparse-exit/Type B, or full-modulus arithmetic gives an actual power-of-two cycle
-- EG-NODE [182] OPEN: the exact [178], [179], or [180] implication not supplied by the manuscript
noncomputable def selectedPairCodeChain
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .pairOverlapFirstFailure) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .surplusAbove) known]
    (systemFresh : K .pairOverlapSystem ∉ known)
    (factorizationFresh : K .pairConditionalFactorization ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known)
    (overlapFresh : K .pairFailureOverlap ∉ known)
    (returnsFresh : K .pairDemandReturns ∉ known)
    (realizabilityFresh : K .pairSystemRealizability ∉ known)
    (systemEarlyFresh : K .pairSystemEarlyOutcome ∉ known)
    (serialFresh : K .pairSerialDemandSystem ∉ known)
    (fanEntryFresh : K .typeBFanEntry ∉ known)
    (incrementFresh : K .pairIncrementCovered ∉ known)
    (incrementEarlyFresh : K .pairIncrementEarlyOutcome ∉ known)
    (arithmeticFresh : K .pairSerialArithmetic ∉ known)
    (cycleFresh : K .pairPowerOfTwoCycle ∉ known)
    (closedFresh : closed ∉ known) :
    StrictSurplusBoundaryResult selected := by
  let overlapSystem :=
    (pairOverlapSystemRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match pairConditionalFactorizationDichotomy (data := spineData)
      overlapSystem (by key_fresh) (by key_fresh) with
  | .right residualHistory =>
      exact Or.inr (Or.inr
        (residualHistory.get (K .pairConditionalFactorizationResidual)).down)
  | .left factorizationHistory =>
      let overlapFailure :=
        (pairFailureOverlapRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run factorizationHistory (by key_fresh)
      let demandReturns :=
        (pairDemandReturnsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run overlapFailure (by key_fresh)
      match pairSystemRealizabilityDichotomy (data := spineData)
          demandReturns (by key_fresh) (by key_fresh) with
      | .right residualHistory =>
          exact Or.inr (Or.inr
            (residualHistory.get (K .pairConditionalFactorizationResidual)).down)
      | .left coveredHistory =>
          match pairSystemOutcomeDichotomy (data := spineData)
              coveredHistory (by key_fresh) (by key_fresh) with
          | .left earlyHistory =>
              let typeBHistory :=
                (pairSystemEarlyTypeBEntryRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run earlyHistory (by key_fresh)
              exact Or.inr (Or.inl ⟨
                Or.inl (typeBHistory.get (K .pairSystemEarlyOutcome)).down,
                (typeBHistory.get (K .typeBFanEntry)).down,
                (typeBHistory.get (K .surplusAbove)).down,
                (typeBHistory.get (K .sparseSurplusSurvivor)).down⟩)
          | .right serialHistory =>
              match pairIncrementCoveredDichotomy (data := spineData)
                  serialHistory (by key_fresh) (by key_fresh) with
              | .right residualHistory =>
                  exact Or.inr (Or.inr
                    (residualHistory.get
                      (K .pairConditionalFactorizationResidual)).down)
              | .left incrementHistory =>
                  match pairIncrementOutcomeDichotomy (data := spineData)
                      incrementHistory (by key_fresh) (by key_fresh) with
                  | .left earlyHistory =>
                      let typeBHistory :=
                        (pairIncrementEarlyTypeBEntryRow
                          (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run earlyHistory (by key_fresh)
                      exact Or.inr (Or.inl ⟨
                        Or.inr (typeBHistory.get
                          (K .pairIncrementEarlyOutcome)).down,
                        (typeBHistory.get (K .typeBFanEntry)).down,
                        (typeBHistory.get (K .surplusAbove)).down,
                        (typeBHistory.get (K .sparseSurplusSurvivor)).down⟩)
                  | .right arithmeticHistory =>
                      let closedHistory :=
                        (pairPowerOfTwoCycleRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).runAndCloseIncompatible
                            arithmeticHistory (K .selection)
                            (K .pairPowerOfTwoCycle) (by key_fresh)
                            (by key_fresh)
                      exact (closedHistory.elimClosed (by infer_instance)).elim

/-- Nodes `[140]`, `[142]`, `[143]` and `[144]`, on any overload ledger whose
token class has just been decided at `[139]`/`[141]`: the geometric audit of
the selected overload publishes the homogeneous bottleneck pattern, and `[144]`
decides the fixed caps.  On the failing arm `lem:same-token-bottleneck-routing`
routes the pattern to the decorated same-token Type B handoff and node `[65]`
appends the common Type B entry, reaching `[144a]`; the caps arm gives node
`[138]`'s `σ(G) ≤ C_sp ⌈√n⌉`, which closes against node `[19]`. -/
-- EG-NODE [140] window-incidence geometric audit: homogeneous matching/star
-- EG-NODE [142] remainder-surplus geometric audit: homogeneous matching/star
-- EG-NODE [143] primitive blocker-support geometric audit: homogeneous matching/star
-- EG-NODE [144] same-token bottleneck: Type B handoff or capped route?
-- EG-NODE [138] no coupled overload: explicit quadratic bound on \(\sigma\); near-cubic spine
noncomputable def selectedBottleneckAudit
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .sparsePressureOverload) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    (patternFresh : K .homogeneousBottleneckPattern ∉ known)
    (failFresh : K .homogeneousCapsFail ∉ known)
    (capsFresh : K .homogeneousCapsHold ∉ known)
    (routingFresh : K .bottleneckRouting ∉ known)
    (handoffFresh : K .typeBHandoff ∉ known)
    (fanEntryFresh : K .typeBFanEntry ∉ known)
    (capsCloseFresh : K .homogeneousBottleneck ∉ known)
    (estimateFresh : K .spineSurplusEstimate ∉ known)
    (closedFresh : closed ∉ known) :
    StrictSurplusBoundaryResult selected := by
  let audited :=
    (homogeneousBottleneckAuditRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData)).run history (by key_fresh)
  match homogeneousBottleneckDichotomy (data := spineData) audited
      (by key_fresh) (by key_fresh) with
  | .left patternHistory =>
      let routed :=
        (sameTokenBottleneckRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run patternHistory (by key_fresh)
      let entered :=
        (sameTokenTypeBFanEntryRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run routed (by key_fresh)
      exact Or.inl ⟨
        (entered.get (K .typeBHandoff)).down,
        (entered.get (K .typeBFanEntry)).down,
        (entered.get (K .bottleneckRouting)).down,
        (entered.get (K .homogeneousBottleneckPattern)).down,
        (entered.get (K .sparsePressureOverload)).down,
        (entered.get (K .capacityTokenLedger)).down,
        (entered.get (K .surplusAbove)).down,
        (entered.get (K .sparseSurplusSurvivor)).down⟩
  | .right capsHistory =>
      let closedHistory :=
        (homogeneousCapsCloseRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).runAndCloseIncompatible capsHistory
            (K .surplusAbove) (K .spineSurplusEstimate) (by key_fresh)
            (by key_fresh)
      exact (closedHistory.elimClosed (by infer_instance)).elim

end HypostructureErdos64EG
