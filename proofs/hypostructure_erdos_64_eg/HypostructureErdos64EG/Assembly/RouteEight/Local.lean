import Hypostructure.Graph.Strategy.SpineRows.Route8OpenBoundarySaturated
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowSignature
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowSingletonTail
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitCycle
import Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitExcluded
import Hypostructure.Graph.Strategy.SpineRows.Route8DemandAbsorption
import Hypostructure.Graph.Strategy.SpineRows.Route8DemandLedgerDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8JointBalance
import Hypostructure.Graph.Strategy.SpineRows.Route8PeeledDemandResidual
import Hypostructure.Graph.Strategy.SpineRows.Route8PeelingDescent
import Hypostructure.Graph.Strategy.SpineRows.Route8StageOutcomeDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedTerminalNoGo
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleOverload
import Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleResidual
import Hypostructure.Graph.Strategy.SpineRows.Route8UnpaidExitFourDichotomy
import Hypostructure.Graph.Strategy.SpineRows.Route8WindowBlockers
import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: RouteEight / Local

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

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
    [FactKeys.Has (K .route8UnifiedNegative) known]
    [FactKeys.Has (K .typeAExclusion) known]
    [FactKeys.Has (K .typeBBridgeReduction) known]
    [FactKeys.Has (K .route8PiecesClassified) known]
    [FactKeys.Has (K .typeBBridgeSublinear) known]
    [FactKeys.Has (K .route8ExtractedEntryCensus) known]
    [FactKeys.Has (K .typeBSublinearLedger) known]
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8QuotientFree) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .selection) known]
    (peelingFresh : K .route8PeelingDescent ∉ known)
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known)
    (stageFailedFresh : K .route8StageRateFailed ∉ known)
    (terminalFresh : K .route8TerminalNoGo ∉ known)
    (demandLedgerFresh : K .route8DemandLedger ∉ known)
    (demandAbsorptionFresh : K .route8DemandAbsorption ∉ known)
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known)
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known)
    (windowBlockersFresh : K .route8WindowBlockers ∉ known)
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known)
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known)
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known)
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known)
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known) :
    ExactLedger EGInput.{u} selected
      ([K .route8PeeledDemandResidual, K .windowShadowHitExcluded,
        K .windowShadowHitCycle, K .windowShadowSingletonTail, K .windowShadowSignature,
        K .route8WindowBlockers,
        K .route8OpenBoundarySaturated, K .route8DemandUnitCount,
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
          let saturated :=
            (route8OpenBoundarySaturatedRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              absorbed (by simp [K_eq_iff, openBoundarySaturatedFresh, demandUnitCountFresh])
          let blocked :=
            (route8WindowBlockersRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              saturated (by simp [K_eq_iff, windowBlockersFresh])
          let shadowSignature :=
            (windowShadowSignatureRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              blocked (by simp [K_eq_iff, windowShadowSignatureFresh])
          let shadowTail :=
            (windowShadowSingletonTailRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              shadowSignature (by simp [K_eq_iff, windowShadowTailFresh])
          let shadowCycle :=
            (windowShadowHitCycleRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              shadowTail (by simp [K_eq_iff, windowShadowCycleFresh])
          let shadowExcluded :=
            (windowShadowHitExcludedRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              shadowCycle (by simp [K_eq_iff, windowShadowExcludedFresh])
          exact
            (route8PeeledDemandResidualRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile) (data := spineData)).run
              shadowExcluded (by simp [K_eq_iff, demandResidualFresh])

/-- **Node `[123]`: exact large-budget descent.**

The complete unified prefix is a literal prerequisite of this node: the
negative collection, Type A exclusion, Type B reduction and sublinear ledger,
both entry censuses, unified deficit, quotient-free arm, receiver routing, and
selection fact must all occur in `known`.  The node performs only the finite
exit-`(4)` descent prescribed by
`thm:large-budget-route8-only`: true route-8 entries close at `[124]`, while a
failed reduced-rate stage is returned as the exact peeled-demand ledger at
`[181]`.  Its result prepends the twelve newly established keys to the unchanged
`known` list, so no inherited fact is projected or reconstructed.  In
particular this wrapper does not claim `False` from `[181]`, does not absorb
the earlier quotient or Type B residual decisions into node `[123]`, and does
not perform mathematics belonging to the eventual `[181]` continuation. -/
-- EG-NODE [123] finite exact descent terminates in true route 8?
noncomputable def selectedLargeBudgetPressureCensus
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedNegative) known]
    [FactKeys.Has (K .typeAExclusion) known]
    [FactKeys.Has (K .typeBBridgeReduction) known]
    [FactKeys.Has (K .route8PiecesClassified) known]
    [FactKeys.Has (K .typeBBridgeSublinear) known]
    [FactKeys.Has (K .route8ExtractedEntryCensus) known]
    [FactKeys.Has (K .typeBSublinearLedger) known]
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8QuotientFree) known]
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
    (openBoundarySaturatedFresh : K .route8OpenBoundarySaturated ∉ known := by
      simp [K_eq_iff])
    (demandUnitCountFresh : K .route8DemandUnitCount ∉ known := by
      simp [K_eq_iff])
    (windowBlockersFresh : K .route8WindowBlockers ∉ known := by
      simp [K_eq_iff])
    (windowShadowSignatureFresh : K .windowShadowSignature ∉ known := by
      simp [K_eq_iff])
    (windowShadowTailFresh : K .windowShadowSingletonTail ∉ known := by
      simp [K_eq_iff])
    (windowShadowCycleFresh : K .windowShadowHitCycle ∉ known := by
      simp [K_eq_iff])
    (windowShadowExcludedFresh : K .windowShadowHitExcluded ∉ known := by
      simp [K_eq_iff])
    (demandResidualFresh : K .route8PeeledDemandResidual ∉ known := by
      simp [K_eq_iff]) :
    ExactLedger EGInput.{u} selected
      ([K .route8PeeledDemandResidual, K .windowShadowHitExcluded,
        K .windowShadowHitCycle, K .windowShadowSingletonTail, K .windowShadowSignature,
        K .route8WindowBlockers,
        K .route8OpenBoundarySaturated, K .route8DemandUnitCount,
        K .route8DemandAbsorption, K .route8DemandLedger,
        K .route8StageRateFailed, K .route8PeelingDescent] ++ known) :=
  selectedRouteEightCensus history
    (by simp [K_eq_iff, peelingFresh])
    (by simp [K_eq_iff, unifiedTrueFresh])
    (by simp [K_eq_iff, stageFailedFresh])
    (by simp [K_eq_iff, terminalFresh])
    (by simp [K_eq_iff, demandLedgerFresh])
    (by simp [K_eq_iff, demandAbsorptionFresh])
    (by simp [K_eq_iff, openBoundarySaturatedFresh])
    (by simp [K_eq_iff, demandUnitCountFresh])
    (by simp [K_eq_iff, windowBlockersFresh])
    (by simp [K_eq_iff, windowShadowSignatureFresh])
    (by simp [K_eq_iff, windowShadowTailFresh])
    (by simp [K_eq_iff, windowShadowCycleFresh])
    (by simp [K_eq_iff, windowShadowExcludedFresh])
    (by simp [K_eq_iff, demandResidualFresh])

/-- **Nodes `[181]`--`[183]`: maximal-ledger exit-`(4)` reduction.**

The incoming ledger is retained verbatim.  Maximality of its demand partition
rules out an unpaid entry with three private carriers by a one-entry
augmentation.  If an unpaid two-carrier entry has no exit-`(4)` witness, the
unified census identifies the already closed `[124]` input.  On the other arm,
every unpaid two-carrier entry retains its canonical exit-`(4)` witness. -/
-- EG-NODE [181] maximal-ledger augmentation: some unpaid entry lacks an exit-\textup{(4)} witness?
-- EG-NODE [183] shortest-trace boundary-support test on the retained unified entries
noncomputable def selectedRouteEightUnpaidExitFourReduction
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8PeeledDemandResidual) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    [FactKeys.Has (K .route8ExtractedEntryCensus) known]
    [FactKeys.Has (K .selection) known]
    (unifiedTrueFresh : K .route8UnifiedTrueTwoCarrierEntry ∉ known := by
      simp [K_eq_iff])
    (residualFresh : K .route8UnpaidExitFourResidual ∉ known := by
      simp [K_eq_iff])
    (terminalFresh : K .route8TerminalNoGo ∉
        (K .route8UnifiedTrueTwoCarrierEntry :: known) := by
      simp [K_eq_iff]) :
    ExactLedger EGInput.{u} selected
      (K .route8UnpaidExitFourResidual :: known) := by
  match route8UnpaidExitFourDichotomy (data := spineData) history
      (by simp [K_eq_iff, unifiedTrueFresh])
      (by simp [K_eq_iff, residualFresh]) with
  | .left trueEntry =>
      -- This is literally the node `[124]` proposition, so its existing local
      -- deletion contradiction closes the arm without weakening the ledger.
      let closed :=
        (route8UnifiedTerminalNoGoRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile) (data := spineData)).run
          trueEntry (by simp [K_eq_iff, terminalFresh])
      exact (closed.get (K .route8TerminalNoGo)).down.elim
  | .right residualHistory =>
      exact residualHistory

/-- **Node `[184]`: shortest-trace boundary-support exhaustion.**

The exact entry family and every inherited ledger key are retained.  On the
literal `[183]` survivor, a silent entry would have a chordless shortest trace
whose vertices all lie on the boundary of its own support.  The retained basin
state would then be independent of its coordinate set, so the empty essential
core would be admissible, contradicting the incoming census bound `alpha ≥ 2`.
Thus the explicit silent-entry residual has cardinality zero. -/
-- EG-NODE [184] visible-first prefix test on the unchanged all-visible entries
noncomputable def selectedRouteEightVisibleResidual
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnpaidExitFourResidual) known]
    [FactKeys.Has (K .route8UnifiedEntryCensus) known]
    (visibleFresh : K .route8UnifiedVisibleResidual ∉ known := by
      simp [K_eq_iff]) :
    ExactLedger EGInput.{u} selected
      (K .route8UnifiedVisibleResidual :: known) :=
  (route8UnifiedVisibleResidualRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [K_eq_iff, visibleFresh])

/-- **Node `[185]`: visible-first prefix exhaustion.**

The literal unified entry family is retained.  Since `[184]` makes each of
its excess loads visible, a receiver with no overloaded completion port would
put that load back in the visible-first payable prefix.  This contradicts the
entry's inherited excess-basin membership.  Thus every retained entry owns
the canonical actual visible-four package and the non-overloaded subfamily has
cardinality zero. -/
-- EG-NODE [185] canonical actual visible-four packages; non-overloaded count zero
noncomputable def selectedRouteEightVisibleOverload
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedVisibleResidual) known]
    [FactKeys.Has (K .route8PeeledDemandResidual) known]
    (overloadFresh : K .route8UnifiedVisibleOverload ∉ known := by
      simp [K_eq_iff]) :
    ExactLedger EGInput.{u} selected
      ([K .route8UnifiedVisibleOverload] ++ known) :=
  (route8UnifiedVisibleOverloadRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simp [K_eq_iff, overloadFresh])

/-- **Node `[186]`: simultaneous balance of the literal `[185]` residual.**

This executes `route8JointBalanceRow` at the fresh canonical key, so the new
fact is appended to the same `ExactLedger`; no bare proposition or detached
reconstruction is returned. -/
-- EG-NODE [186] OPEN: joint balance and silent-terminal exclusion; visible-entry history retained
noncomputable def selectedRouteEightJointBalance
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8UnifiedVisibleOverload) known]
    [FactKeys.Has (K .route8UnifiedVisibleResidual) known]
    [FactKeys.Has (K .route8PeeledDemandResidual) known]
    [FactKeys.Has (K .route8UnifiedDeficit) known]
    [FactKeys.Has (K .route8DemandUnitCount) known]
    (jointFresh : K .route8JointBalance ∉ known) :
    ExactLedger EGInput.{u} selected (K .route8JointBalance :: known) :=
  (route8JointBalanceRow (BranchState := BranchState)
    (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
    (presentation := erdosReceiverLoadProfile) (data := spineData)).run
    history (by simpa [K_eq_iff] using jointFresh)

end HypostructureErdos64EG
