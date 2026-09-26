import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppression
import Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppressionSafe
import Hypostructure.Graph.Strategy.SpineRows.SingleOpenPortSuppressionWitness
import Hypostructure.Graph.Strategy.SpineRows.SuppressedFamilyCriticalCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SameTokenBottleneckRouting
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.SameTokenTypeBFanEntry
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
    (systemFresh : K .pairOverlapSystem ∉ known := by key_fresh)
    (factorizationFresh : K .pairConditionalFactorization ∉ known := by key_fresh)
    (factorizationFailsFresh : K .pairFactorizationFails ∉ known := by key_fresh)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known := by key_fresh)
    (overlapFresh : K .pairFailureOverlap ∉ known := by key_fresh)
    (returnsFresh : K .pairDemandReturns ∉ known := by key_fresh)
    (realizabilityFresh : K .pairSystemRealizability ∉ known := by key_fresh)
    (realizabilityFailsFresh : K .pairRealizabilityFails ∉ known := by key_fresh)
    (systemEarlyFresh : K .pairSystemEarlyOutcome ∉ known := by key_fresh)
    (systemNoEarlyFresh : K .pairSystemNoEarlyOutcome ∉ known := by key_fresh)
    (serialFresh : K .pairSerialDemandSystem ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (incrementFresh : K .pairIncrementCovered ∉ known := by key_fresh)
    (incrementFailsFresh : K .pairIncrementFails ∉ known := by key_fresh)
    (incrementEarlyFresh : K .pairIncrementEarlyOutcome ∉ known := by key_fresh)
    (incrementNoEarlyFresh : K .pairIncrementNoEarlyOutcome ∉ known := by key_fresh)
    (arithmeticFresh : K .pairSerialArithmetic ∉ known := by key_fresh)
    (cycleFresh : K .pairPowerOfTwoCycle ∉ known := by key_fresh)
    (closedFresh : closed ∉ known := by key_fresh) :
    StrictSurplusBoundaryResult selected := by
  let overlapSystem :=
    (pairOverlapSystemRow (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile) (data := spineData)).run
      history (by key_fresh)
  match pairConditionalFactorizationDichotomy (data := spineData)
      overlapSystem (by key_fresh) (by key_fresh) with
  | .right failsHistory =>
      let residualHistory :=
        (pairFactorizationResidualRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run failsHistory (by key_fresh)
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
      | .right failsHistory =>
          let residualHistory :=
            (pairRealizabilityResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run failsHistory (by key_fresh)
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
          | .right noEarlyHistory =>
              let serialHistory :=
                (pairSerialDemandSystemRow (BranchState := BranchState)
                  (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                  (presentation := erdosReceiverLoadProfile)
                  (data := spineData)).run noEarlyHistory (by key_fresh)
              match pairIncrementCoveredDichotomy (data := spineData)
                  serialHistory (by key_fresh) (by key_fresh) with
              | .right failsHistory =>
                  let residualHistory :=
                    (pairIncrementResidualRow (BranchState := BranchState)
                      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                      (presentation := erdosReceiverLoadProfile)
                      (data := spineData)).run failsHistory (by key_fresh)
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
                  | .right noEarlyHistory =>
                      let arithmeticHistory :=
                        (pairSerialArithmeticRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).run noEarlyHistory (by key_fresh)
                      let closedHistory :=
                        (pairPowerOfTwoCycleRow (BranchState := BranchState)
                          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
                          (presentation := erdosReceiverLoadProfile)
                          (data := spineData)).runAndCloseIncompatible
                            arithmeticHistory (K .selection)
                            (K .pairPowerOfTwoCycle) (by key_fresh)
                            (by key_fresh)
                      exact (closedHistory.elimClosed (by infer_instance)).elim

/-- Node `[144]` on any ledger carrying the homogeneous bottleneck pattern
published by the geometric audit `[140]`/`[142]`/`[143]`: decide the fixed caps.
On the failing arm `lem:same-token-bottleneck-routing` routes the pattern to the
decorated same-token Type B handoff and node `[65]` appends the common Type B
entry, reaching `[144a]`; the caps arm gives node `[138]`'s
`σ(G) ≤ C_sp ⌈√n⌉`, which closes against node `[19]`. -/
-- EG-NODE [144] same-token bottleneck: Type B handoff or capped route?
-- EG-NODE [138] no coupled overload: explicit quadratic bound on \(\sigma\); near-cubic spine
noncomputable def selectedBottleneckDischarge
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .homogeneousBottleneckPattern) known]
    [FactKeys.Has (K .sparsePressureOverload) known]
    [FactKeys.Has (K .capacityTokenLedger) known]
    [FactKeys.Has (K .activeSurplusDemands) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .highCentreNormalForm) known]
    [FactKeys.Has (K .sparseSlackSurplus) known]
    [FactKeys.Has (K .fibrePressure) known]
    [FactKeys.Has (K .surplusAbove) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .selection) known]
    (failFresh : K .homogeneousCapsFail ∉ known := by key_fresh)
    (capsFresh : K .homogeneousCapsHold ∉ known := by key_fresh)
    (routingFresh : K .bottleneckRouting ∉ known := by key_fresh)
    (handoffFresh : K .typeBHandoff ∉ known := by key_fresh)
    (handoffFailsFresh : K .typeBHandoffFails ∉ known := by key_fresh)
    (unresolvedFresh : K .sameTokenPatternUnresolved ∉ known := by key_fresh)
    (fanEntryFresh : K .typeBFanEntry ∉ known := by key_fresh)
    (capsCloseFresh : K .homogeneousBottleneck ∉ known := by key_fresh)
    (estimateFresh : K .spineSurplusEstimate ∉ known := by key_fresh)
    (closedFresh : closed ∉ known := by key_fresh) :
    StrictSurplusBoundaryResult selected := by
  match homogeneousBottleneckDichotomy (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left patternHistory =>
      let routed :=
        (sameTokenBottleneckRoutingRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run patternHistory (by key_fresh)
      match sameTokenHandoffDichotomy (data := spineData) routed
          (by key_fresh) (by key_fresh) with
      | .left handoffHistory =>
          let entered :=
            (sameTokenTypeBFanEntryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run handoffHistory (by key_fresh)
          exact Or.inl ⟨
            Or.inl ⟨(entered.get (K .typeBHandoff)).down,
              (entered.get (K .typeBFanEntry)).down⟩,
            (entered.get (K .bottleneckRouting)).down,
            (entered.get (K .homogeneousBottleneckPattern)).down,
            (entered.get (K .sparsePressureOverload)).down,
            (entered.get (K .capacityTokenLedger)).down,
            (entered.get (K .surplusAbove)).down,
            (entered.get (K .sparseSurplusSurvivor)).down⟩
      | .right failsHistory =>
          let unresolved :=
            (sameTokenPatternUnresolvedRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run failsHistory (by key_fresh)
          exact Or.inl ⟨
            Or.inr ⟨(unresolved.get (K .typeBHandoffFails)).down,
              (unresolved.get (K .sameTokenPatternUnresolved)).down⟩,
            (unresolved.get (K .bottleneckRouting)).down,
            (unresolved.get (K .homogeneousBottleneckPattern)).down,
            (unresolved.get (K .sparsePressureOverload)).down,
            (unresolved.get (K .capacityTokenLedger)).down,
            (unresolved.get (K .surplusAbove)).down,
            (unresolved.get (K .sparseSurplusSurvivor)).down⟩
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
