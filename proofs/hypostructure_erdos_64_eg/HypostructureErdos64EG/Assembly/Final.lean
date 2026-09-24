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
      let structured :=
        (sparseTargetDefectStructureRow
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run targetDefect (by simp [K_eq_iff])
      exact Or.inl ⟨
        (structured.get (K .sparseTargetDefectResidual)).down,
        (structured.get (K .sparseTargetDefectStructure)).down⟩
  | .right survivorHistory =>
      let node125 := selectedSparseSurplusSurvivorNode125 survivorHistory
      exact Or.inr (selectedNearCubicSurvivorBranch node125)

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

/-- The two sparse target-defect exits have incompatible surplus ancestry. -/
theorem node20a_nearCubicTargetDefect_disjoint
    {selected : EGInput.{u}}
    (strict : Node20aOutcome selected)
    (near : NearCubicTargetDefectOutcome selected) : False := by
  have above :
      spineData.surplusThreshold selected.object.vertexCount <
        selected.object.degreeSurplus spineData.threshold :=
    strict.2.2.2
  have atOrBelow :
      selected.object.degreeSurplus spineData.threshold ≤
        spineData.surplusThreshold selected.object.vertexCount :=
    near.2.2
  exact Nat.not_lt_of_ge atOrBelow above

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
      match selectedSparseSurplusDichotomy strictHistory with
      | .left exitHistory =>
          -- The enclosing `[20]` classification routes the literal exit forms
          -- and retains only the exact attempted-quotient target-defect
          -- payload for its later peeling handoff.  It never enters `[125]`.
          let targetDefectHistory :=
            selectedSparseSurplusExitContinuation exitHistory
          let structuredHistory :=
            selectedSparseTargetDefectStructureContinuation targetDefectHistory
          exact Or.inl ⟨
            (structuredHistory.get (K .sparseTargetDefectResidual)).down,
            (structuredHistory.get (K .sparseTargetDefectStructure)).down,
            (structuredHistory.get (K .sparsePairExit)).down,
            (structuredHistory.get (K .surplusAbove)).down⟩
      | .right survivorHistory =>
          match selectedStrictSurplusBranch survivorHistory with
          | .inl handoff => exact Or.inr (Or.inl handoff.down)
          | .inr (.inl pairEntry) =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl pairEntry.down))))))
          | .inr (.inr pair) =>
              exact Or.inr (Or.inr (Or.inr (Or.inl pair.down)))
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
            | .inr (.inl quotient) =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inl ⟨quotient, (nearCubicHistory.get (K .surplusAtOrBelow)).down⟩))))))))
            | .inr (.inr joint) =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl joint))))
          have liftAbsorbed : SelectedAbsorbedGermBoundary selected →
              SelectedLedgerBoundaryResult selected := by
            intro absorbed
            match absorbed with
            | .inl route => exact liftRoute route
            | .inr (.inl cold) =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨cold, (nearCubicHistory.get (K .surplusAtOrBelow)).down⟩)))))))))
            | .inr (.inr blocked) =>
                exact Or.inr (Or.inr (Or.inl blocked))
          match survivor with
          | .inl (.inl route) => exact liftRoute route
          | .inl (.inr absorbed) => exact liftAbsorbed absorbed
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
