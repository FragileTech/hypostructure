import HypostructureErdos64EG.Assembly.NearCubic.Survivor
import HypostructureErdos64EG.Assembly.Surplus.Strict
import Hypostructure.Graph.Strategy.SpineRows.SparseExitResidual
import Hypostructure.Graph.Strategy.SpineRows.Bridgeless
import Hypostructure.Graph.Strategy.SurplusRows
import HypostructureErdos64EG.Assembly.Surplus.RegisteredConstants

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
      [K .surplusAtOrBelow, K .localAlgebra, K .maximalPacking, K .windowPresent, K .uncompressible,
        K .admissibleQuotientsLabelInjective, K .replacementExclusion,
        K .targetCompleteContextUniversality, K .degreeProfileFibres, K .cycleRankConstraint,
        K .surplusDartIdentity, K .highDegreeCountBound, K .tightEndpoint, K .slackIndependent,
        K .singleBoundaryShape, K .noProperBaseline, K .returnAvoidance,
        K .primitiveCarrierCount, K .remainderDeficiencyBelowCut, K .windowCutCapacity,
        K .minDegreeBaseline, K .bridgeless, K .cubicBaseline, K .packingOrderBound,
        K .noSuppressionChordViolation, K .specWitnessStructure, K .selection]) :
    SelectedNearCubicBoundary selected := by
  match sparseSurplusSurvivorDichotomy
      (BranchState := BranchState)
      (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
      (presentation := erdosReceiverLoadProfile)
      (data := spineData) history
      (by key_fresh) (by key_fresh) with
  | .left exitHistory =>
      exact Or.inl
        (nearCubicTargetDefectReturn (selectedSparseTargetDefectExit exitHistory))
  | .right survivorHistory =>
      -- The at-or-below survivor goes to `[21]`; `[125]` is entered only
      -- from the strict arm `[20]`.
      exact Or.inr (selectedNearCubicSurvivorBranch survivorHistory)

/-- Node `[187]` collects only the other literal selected-root outcomes, each
with every fact of its ledger at its return (`Assembly/Residuals/`): the
near-cubic target defect, the four pair Type B subtypes, the Type B sublinear
failure and the route-`8` quotient failure `[348]` as products of their arm
blocks, the eleven private-carrier rate failure subtypes, and the local
cold-terminal exclusion as its four linear-arm singletons (its absorbed-germ
product is not entered: `[173]`'s no-arm is closed against `K .route8Rate`).  The pair-system entry retains its own source key and is not
`[144a]`. -/
abbrev OtherReturnedOutcome (selected : EGInput.{u}) :=
  NearCubicTargetDefectOutcome selected ∨
  (PairTypeBOutcome_independentSystem selected ∨
    PairTypeBOutcome_independentIncrement selected ∨
    PairTypeBOutcome_dependentSystem selected ∨
    PairTypeBOutcome_dependentIncrement selected) ∨
  TypeBSublinearOutcome_product selected ∨
  Route8QuotientOutcome_product selected ∨
  (Route8RateFailsOutcome_realized_highEntropy selected ∨
    Route8RateFailsOutcome_realized_lowNonrepetitive selected ∨
    Route8RateFailsOutcome_realized_lowWedgeFree selected ∨
    Route8RateFailsOutcome_realized_lowWedge selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_highEntropy selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_lowNonrepetitive selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_lowWedgeFree selected ∨
    Route8RateFailsOutcome_denseAtOrAbove_lowWedge selected ∨
    Route8RateFailsOutcome_denseBelow_lowNonrepetitive selected ∨
    Route8RateFailsOutcome_denseBelow_lowWedgeFree selected ∨
    Route8RateFailsOutcome_denseBelow_lowWedge selected) ∨
  (ColdBranchClosedOutcome_linearDenseAtOrAbove selected ∨
    ColdBranchClosedOutcome_linearDenseRateFailed selected ∨
    ColdBranchClosedOutcome_linearRealizedDistinguished selected ∨
    ColdBranchClosedOutcome_linearRealizedSilent selected)

/-- Exact selected-root reduction.  Every returned residual carries every fact
of the single ledger at its return, one `get` per fact; paths with different
fact sets are different residuals, stated as subtypes of the generic residual
or, where the paths form a full product, as the product of their arm blocks:
`[20a]`; the six `[144a]` subtypes; the two `[172a]` subtypes; the six `[182]`
subtypes; the `[186]` joint balance product; the remaining `[187]` outcomes;
and the structural exhaustion residuals `[153]` (3 subtypes), `[162]`
(2 subtypes) and `[54]` (5 subtypes).

Bounded-size residuals: on `[146]` no, the density order (`[158]`'s realized
package, or `[24]` on the bounded arm of `[153]`, against `θ ≥ 1/78`) is
decided exactly on G's order (`realizedOrderDichotomy`,
`boundedOrderDichotomy`); the arm `N₀ ≤ n` is closed and every residual below
the other arm carries the combined bound and `n < N₀` (`K .realizedOrderSmall`
or `K .boundedOrderSmall`): all eleven private-carrier rate failure subtypes,
the three bounded `[54]` subtypes, the `[153]` subtype `realized_linear`, the
two realized cold-terminal singletons, and the product paths through the prefix
blocks `Route8LanePrefixBlock_realizedColdAtOrAbove` /
`Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove`. -/
abbrev SelectedLedgerBoundaryResult (selected : EGInput.{u}) :=
  Node20aOutcome selected ∨
  (Node144aOutcome_windowHandoff selected ∨ Node144aOutcome_windowFails selected ∨
    Node144aOutcome_remainderHandoff selected ∨
    Node144aOutcome_remainderFails selected ∨
    Node144aOutcome_primitiveHandoff selected ∨
    Node144aOutcome_primitiveFails selected) ∨
  (BlockedBarrierOverlapOutcome_DeficiencyAtOrAbove selected ∨
    BlockedBarrierOverlapOutcome_DeficiencyBelowRateFails selected) ∨
  (PairConditionalFactorizationOutcome_freeFactorizationFails selected ∨
    PairConditionalFactorizationOutcome_freeRealizabilityFails selected ∨
    PairConditionalFactorizationOutcome_freeIncrementFails selected ∨
    PairConditionalFactorizationOutcome_blockedFactorizationFails selected ∨
    PairConditionalFactorizationOutcome_blockedRealizabilityFails selected ∨
    PairConditionalFactorizationOutcome_blockedIncrementFails selected) ∨
  Route8JointBalanceOutcome_product selected ∨
  OtherReturnedOutcome selected ∨
  (Node153ResidualOutcome_denseAtOrAbove_linear selected ∨
    Node153ResidualOutcome_denseRateFails_linear selected ∨
    Node153ResidualOutcome_realized_linear selected) ∨
  (Node162ResidualOutcome_tauAtOrAbove selected ∨
    Node162ResidualOutcome_tauBelowRateFails selected) ∨
  (Node54ResidualOutcome_realizedColdBelow selected ∨
    Node54ResidualOutcome_realizedBounded selected ∨
    Node54ResidualOutcome_unrealizedTauHighBounded selected ∨
    Node54ResidualOutcome_unrealizedRateFailsBounded selected ∨
    Node54ResidualOutcome_unrealizedBothRates selected)

-- The `[20a]` enrichment rows make `FactKeys.Available` search deeper than the
-- default instance budget along the one `[20a]` ledger; the facts hoisted to
-- the entry prefix and to the top of the strict arm of `[19]` lengthen every
-- ledger here, so the `[20a]` return also needs more than the default
-- elaboration budget.
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
noncomputable def selectedLedgerBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected := by
  have other : OtherReturnedOutcome selected → SelectedLedgerBoundaryResult selected :=
    fun outcome => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl outcome)))))
  match selectedSurplusDichotomy history with
  | .left strictHistory =>
      -- Top of the strict arm of `[19]`: every fact that reads only entry facts
      -- and `K .surplusAbove` is published here, once, so both `[20]` arms
      -- (`[20a]` and `[125]`) carry it.  No decision.
      -- `[135]`'s exact window-join load, hoisted to the top of the strict arm; no decision.
      let windowJoinHistory :=
        (exactWindowJoinPressureRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run strictHistory (by key_fresh)
      -- `[129]`'s baseline spine demand, hoisted to the top of the strict arm; no decision.
      let baselineDemandHistory :=
        (sparseExitBaselineSpineDemandRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run windowJoinHistory (by key_fresh)
      -- hoisted from `[20a]`: the budget identities; no decision.
      let budgetHistory :=
        (sparseExitBudgetRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run baselineDemandHistory (by key_fresh)
      -- hoisted from `[20a]`: the sharpened envelope; no decision.
      let envelopeHistory :=
        (sparseExitEnvelopeRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run budgetHistory (by key_fresh)
      -- hoisted from `[20a]`: the high-degree range; no decision.
      let highDegreeHistory :=
        (highDegreeSurplusRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run envelopeHistory (by key_fresh)
      -- hoisted from `[20a]`: G's canonical capacity presentation; no decision.
      let canonicalCapacityHistory :=
        (sparseExitCanonicalCapacityRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run highDegreeHistory (by key_fresh)
      -- hoisted from `[20a]`: the canonical capacity counts; no decision.
      let canonicalCountsHistory :=
        (sparseExitCanonicalCapacityCountsRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run canonicalCapacityHistory (by key_fresh)
      -- hoisted from `[20a]`: the paper budget and the pair-code chain; no decision.
      let pairChainHistory :=
        (sparseExitPairChainRow (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData)).run canonicalCountsHistory (by key_fresh)
      -- EG-NODE [20] surplus-pair accounting branch
      -- The enclosing `[20]` routing tests `def:named-surplus-exits` before
      -- node `[125]`: the exit arm retains only the attempted-quotient target
      -- defect and its structure at `[20a]`; the survivor arm is `[125]`.
      match sparseSurplusSurvivorDichotomy
          (BranchState := BranchState)
          (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
          (presentation := erdosReceiverLoadProfile)
          (data := spineData) pairChainHistory
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
          -- `[131]`'s full-schedule count fails at G (unconditionally).  Kept on the
          -- `[20a]` arm: on `[125]`'s independent arm `K .freePairCountFails` is the
          -- no-arm key of the paper's `[131]` decision, so it cannot be published
          -- above `[20]` without removing that decision.  No decision here.
          let freePairCountHistory :=
            (sparseExitFreePairCountRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run structuredHistory (by key_fresh)
          -- [20a] enrichment: facts at G that read `K .sparseTargetDefectResidual`; no decision.
          let witnessFactsHistory :=
            (sparseExitWitnessFactsRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run freePairCountHistory (by key_fresh)
          -- [20a] enrichment: facts at G that read `K .sparseTargetDefectResidual`; no decision.
          let realizedContextsHistory :=
            (sparseExitRealizedContextsRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run witnessFactsHistory (by key_fresh)
          -- [20a] enrichment: facts at G that read `K .sparseTargetDefectResidual`; no decision.
          let boundaryHistory :=
            (sparseExitBoundaryRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run realizedContextsHistory (by key_fresh)
          -- [20a] enrichment: facts at G that read `K .sparseTargetDefectResidual`; no decision.
          let compressionHistory :=
            (sparseExitCompressionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run boundaryHistory (by key_fresh)
          -- [20a] enrichment: facts at G that read `K .sparseTargetDefectResidual`; no decision.
          let deletionHistory :=
            (sparseExitDeletionRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run compressionHistory (by key_fresh)
          -- [20a] enrichment: facts at G that read `K .sparseTargetDefectResidual`; no decision.
          let combinationHistory :=
            (sparseExitCombinationRow (BranchState := BranchState)
              (Presentation := Graph.ReceiverLoad.LoadCapacityProfile)
              (presentation := erdosReceiverLoadProfile)
              (data := spineData)).run deletionHistory (by key_fresh)
          exact Or.inl (node20aReturn combinationHistory)
      | .right survivorHistory =>
          match selectedStrictSurplusBranch survivorHistory with
          | .inl handoff => exact Or.inr (Or.inl handoff)
          | .inr (.inl pairEntry) =>
              exact other (Or.inr (Or.inl pairEntry))
          | .inr (.inr pair) =>
              exact Or.inr (Or.inr (Or.inr (Or.inl pair)))
  | .right nearCubicHistory =>
      match selectedNearCubicBranch nearCubicHistory with
      | .inl targetDefect =>
          exact other (Or.inl targetDefect)
      | .inr survivor =>
          have liftRoute : SelectedRouteEightBoundary selected →
              SelectedLedgerBoundaryResult selected := by
            intro route
            match route with
            | .inl sublinear =>
                exact other (Or.inr (Or.inr (Or.inl sublinear)))
            | .inr (.inl quotient) =>
                exact other (Or.inr (Or.inr (Or.inr (Or.inl quotient))))
            | .inr (.inr joint) =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl joint))))
          have repeatedOut : Node153ResidualSubtypes selected →
              SelectedLedgerBoundaryResult selected :=
            fun repeated => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl repeated))))))
          match survivor with
          | .inl route => exact liftRoute route
          | .inr (.inl rate) =>
              exact other (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rate)))))
          | .inr (.inr (.inl blocked)) =>
              exact Or.inr (Or.inr (Or.inl blocked))
          | .inr (.inr (.inr (.inl cold))) =>
              exact other (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr cold)))))
          | .inr (.inr (.inr (.inr (.inl repeated)))) => exact repeatedOut repeated
          | .inr (.inr (.inr (.inr (.inr (.inl heavy))))) =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl heavy)))))))
          | .inr (.inr (.inr (.inr (.inr (.inr entropy))))) =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr entropy)))))))

/-- The selected minimal counterexample has one of the exact boundary
outcomes, each with every fact of the single ledger at its return. -/
theorem selectedCounterexample_reaches_exactBoundary
    {selected : EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected [EGSelectionKey]) :
    SelectedLedgerBoundaryResult selected :=
  selectedLedgerBoundary history

/-- Every counterexample to the public finite-graph statement reaches one of
the displayed boundary alternatives through the selected ledger. -/
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
