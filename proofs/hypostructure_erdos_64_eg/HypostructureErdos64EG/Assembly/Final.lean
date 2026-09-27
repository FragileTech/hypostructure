import HypostructureErdos64EG.Assembly.NearCubic.Survivor
import HypostructureErdos64EG.Assembly.Surplus.Strict

/-!
# Assembly: Final

Part of the dependency-separated Erdős–Gyárfás assembly.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u w

/-- Establish `def:surviving-cold-branch` before entering any hot/cold or
net-charge descendant.  The exhaustive sparse-exit split belongs to the
enclosing routing; its survivor ledger enters `[21]` directly and is then
retained monotonically by every later ExactLedger. -/
noncomputable def selectedNearCubicBranch
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking,
        K .windowPresent, K .uncompressible, K .replacementExclusion,
        K .cycleRankConstraint, K .tightEndpoint, K .slackIndependent,
        K .noProperBaseline, K .returnAvoidance, K .contractionCritical, K .gadgetClosure, K .relabelingDensityCap, K .cubicBaseline, K .selection]) :
    SelectedNearCubicBoundary selected := by
  match sparseSurplusSurvivorDichotomy
      (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left exitHistory =>
      let structured := selectedSparseTargetDefectExit exitHistory
      exact Or.inl ⟨
        (structured.get (K .sparseTargetDefectResidual)).down,
        (structured.get (K .sparseTargetDefectStructure)).down⟩
  | .right survivorHistory =>
      -- The at-or-below survivor goes to `[21]`; `[125]` is entered only
      -- from the strict arm `[20]`.
      exact Or.inr (selectedNearCubicSurvivorBranch survivorHistory)

/-- Node `[20a]`: the exact strict-surplus named-exit survivor, including
the source decision and the structured target-defect witness. -/
abbrev Node20aOutcome (selected : EGInput.{u}) :=
  SelectedSparseTargetDefectBoundary selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparsePairExit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAbove selected.object

/-- The same target-defect fact from the distinct at-or-below-surplus arm. -/
abbrev NearCubicTargetDefectOutcome (selected : EGInput.{u}) :=
  SelectedSparseTargetDefectBoundary selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .sparseTargetDefectStructure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object

/-- Node `[187]` collects only the other literal selected-root outcomes.
The pair-system entry retains its own source key and is not `[144a]`. -/
abbrev OtherReturnedOutcome (selected : EGInput.{u}) :=
  NearCubicTargetDefectOutcome selected ∨
  PairTypeBOutcome selected ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBSublinearResidual selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object) ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8QuotientResidual selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object) ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object) ∨
  (Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldBranchClosed selected.object ∧
    Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .surplusAtOrBelow selected.object)

/-- Exact selected-root reduction: five individually identified residuals
and the explicit remaining disjunction at `[187]`. -/
abbrev SelectedLedgerBoundaryResult (selected : EGInput.{u}) :=
  Node20aOutcome selected ∨
  Node144aOutcome selected ∨
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .blockedBarrierOverlap selected.object ∨
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData
        .pairConditionalFactorizationResidual selected.object ∨
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8JointBalance selected.object ∨
  OtherReturnedOutcome selected

noncomputable def selectedLedgerBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected := by
  match selectedSurplusDichotomy history with
  | .left strictHistory =>
      -- EG-NODE [20] surplus-pair accounting branch
      -- The enclosing `[20]` routing tests `def:named-surplus-exits` before
      -- node `[125]`: the exit arm retains only the attempted-quotient target
      -- defect and its structure at `[20a]`; the survivor arm is `[125]`.
      match sparseSurplusSurvivorDichotomy
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData) strictHistory
          (by key_fresh) (by key_fresh) with
      | .left exitHistory =>
          let targetDefectHistory :=
            (sparseSurplusExitRoutingRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run exitHistory (by key_fresh)
          let structuredHistory :=
            (sparseTargetDefectStructureRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run targetDefectHistory (by key_fresh)
          exact Or.inl ⟨
            (structuredHistory.get (K .sparseTargetDefectResidual)).down,
            (structuredHistory.get (K .sparseTargetDefectStructure)).down,
            (structuredHistory.get (K .sparsePairExit)).down,
            (structuredHistory.get (K .surplusAbove)).down⟩
      | .right survivorHistory =>
          match selectedStrictSurplusBranch survivorHistory with
          | .inl handoff => exact Or.inr (Or.inl handoff)
          | .inr (.inl pairEntry) =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl pairEntry))))))
          | .inr (.inr pair) =>
              exact Or.inr (Or.inr (Or.inr (Or.inl pair)))
  | .right nearCubicHistory =>
      match selectedNearCubicBranch nearCubicHistory with
      | .inl targetDefect =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨targetDefect.1, targetDefect.2,
              (nearCubicHistory.get (K .surplusAtOrBelow)).down⟩)))))
      | .inr survivor =>
          have liftRoute : SelectedRouteEightBoundary selected →
              SelectedLedgerBoundaryResult selected := by
            intro route
            match route with
            | .inl sublinear =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl ⟨sublinear, (nearCubicHistory.get (K .surplusAtOrBelow)).down⟩)))))))
            | .inr joint =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl joint))))
          match survivor with
          | .inl (.inl route) => exact liftRoute route
          | .inl (.inr absorbed) => exact liftRoute absorbed
          | .inr (.inl rate) =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rate, (nearCubicHistory.get (K .surplusAtOrBelow)).down⟩)))))))))
          | .inr (.inr (.inl blocked)) =>
              exact Or.inr (Or.inr (Or.inl blocked))
          | .inr (.inr (.inr cold)) =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨cold, (nearCubicHistory.get (K .surplusAtOrBelow)).down⟩)))))))))

/-- The selected minimal counterexample has one of the six exact boundary
outcomes, with each source fact read from its producer's retained ledger. -/
theorem selectedCounterexample_reaches_exactBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected :=
  selectedLedgerBoundary history

/-- Every counterexample to the public finite-graph statement reaches one of
the six displayed boundary alternatives through the selected ledger. -/
theorem officialCounterexample_reaches_selectedLedgerBoundary
    (counterexample : ¬ OfficialStatement.{u}) :
    ∃ selected : EGInput.{u}, SelectedLedgerBoundaryResult selected := by
  classical
  have existsBad : ∃ object : Graph.FiniteObject.{u},
      Baseline object ∧ ¬ Target object := by
    by_contra noBad
    have closure : ∀ object : Graph.FiniteObject.{u},
        Baseline object → Target object := by
      intro object baseline
      by_contra avoids
      exact noBad ⟨object, baseline, avoids⟩
    apply counterexample
    exact target.target_to_statement closure
  obtain ⟨object, baseline, avoids⟩ := existsBad
  let input : EGInput.{u} := ⟨object, baseline, ()⟩
  let opened := openSelectedCounterexample input avoids
  exact ⟨opened.selected, selectedCounterexample_reaches_exactBoundary opened.history⟩

end HypostructureErdos64EG
